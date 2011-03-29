(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


open Why
open Format

type prover_data =
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }

type proof_attempt_status =
  | Undone
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)


module type OBSERVER = sig
  type key
  val create: ?parent:key -> unit -> key
  val remove: key -> unit

  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit
end

module Make(O : OBSERVER) = struct

type proof_attempt =
    { prover : prover_data;
      proof_goal : goal;
      proof_key : O.key;
      mutable proof_state : proof_attempt_status;
      mutable proof_obsolete : bool;
      mutable edited_as : string;
    }

and goal_parent =
  | Parent_theory of theory
  | Parent_transf of transf

and goal =
    { goal_name : string;
      goal_expl : string option;
      parent : goal_parent;
      task: Task.task;
      goal_key : O.key;
      mutable proved : bool;
      external_proofs: (string, proof_attempt) Hashtbl.t;
      transformations : (string, transf) Hashtbl.t;
    }

and transf =
    { parent_goal : goal;
      mutable transf_proved : bool;
      transf_key : O.key;
      mutable subgoals : goal list;
    }

and theory =
    { theory : Theory.theory;
      theory_key : O.key;
      theory_parent : file;
      mutable goals : goal list;
      mutable verified : bool;
    }

and file =
    { file_name : string;
      file_key : O.key;
      mutable theories: theory list;
      mutable file_verified : bool;
    }

type any =
  | File of file
  | Theory of theory
  | Goal of goal
  | Proof_attempt of proof_attempt
  | Transformation of transf

let all_files : file list ref = ref []

let notify_fun = ref (fun (_:any) -> ())
  
let open_session ~notify _ = 
  notify_fun := notify

let check_file_verified f =
  let b = List.for_all (fun t -> t.verified) f.theories in
  if f.file_verified <> b then
    begin
      f.file_verified <- b;
      !notify_fun (File f)
    end

let check_theory_proved t =
  let b = List.for_all (fun g -> g.proved) t.goals in
  if t.verified <> b then
    begin
      t.verified <- b;
      !notify_fun (Theory t);
      check_file_verified t.theory_parent
    end

let rec check_goal_proved g =
  let b1 = Hashtbl.fold
    (fun _ a acc -> acc ||
       match a.proof_state with
	 | Done { Call_provers.pr_answer = Call_provers.Valid} -> true
	 | _ -> false) g.external_proofs false
  in
  let b = Hashtbl.fold
    (fun _ t acc -> acc || t.transf_proved) g.transformations b1
  in
  if g.proved <> b then
    begin
      g.proved <- b;
      !notify_fun (Goal g);
      match g.parent with
        | Parent_theory t -> check_theory_proved t
        | Parent_transf t -> check_transf_proved t
    end

and check_transf_proved t =
  let b = List.for_all (fun g -> g.proved) t.subgoals in
  if t.transf_proved <> b then
    begin
      t.transf_proved <- b;
      !notify_fun (Transformation t);
      check_goal_proved t.parent_goal
    end


let set_file_verified f =
  f.file_verified <- true;
  !notify_fun (File f)

let set_theory_proved ~propagate t =
  t.verified <- true;
  !notify_fun (Theory t);
  let f = t.theory_parent in
  if propagate then
    if List.for_all (fun t ->
                       t.verified) f.theories 
    then set_file_verified f

let rec set_proved ~propagate g =
  g.proved <- true;
  !notify_fun (Goal g);
  if propagate then
    match g.parent with
      | Parent_theory t ->
          if List.for_all (fun g -> g.proved) t.goals then
            set_theory_proved ~propagate t
      | Parent_transf t ->
          if List.for_all (fun g -> g.proved) t.subgoals then
            begin
              set_proved ~propagate t.parent_goal;
            end

let set_proof_state ~obsolete a res =
  a.proof_state <- res;
  a.proof_obsolete <- obsolete;
  !notify_fun (Proof_attempt a)

(*************************)
(*         Scheduler     *)
(*************************) 


(* timeout handler *)

let maximum_running_proofs = ref 2
let running_proofs = ref []

let proof_attempts_queue = Queue.create ()

let timeout_handler_activated = ref false
let timeout_handler_running = ref false

let timeout_handler () =
  assert (not !timeout_handler_running);
  timeout_handler_running := true;
  let l = List.fold_left
    (fun acc ((callback,call) as c) ->
       match Call_provers.query_call call with
	 | None -> c::acc
	 | Some post ->
	     let res = post () in callback (Done res);
	     acc)
    [] !running_proofs
  in
  let l =
    if List.length l < !maximum_running_proofs then
      begin try
	let (callback,pre_call) = Queue.pop proof_attempts_queue in
	callback Running;
	let call = pre_call () in
	(callback,call)::l
      with Queue.Empty -> l
      end
    else l
  in
  running_proofs := l;
  let continue =
    match l with
      | [] ->
(*
          eprintf "Info: timeout_handler stopped@.";
*)
          false
      | _ -> true
  in
  timeout_handler_activated := continue;
  timeout_handler_running := false;
  continue


let run_timeout_handler () =
  if !timeout_handler_activated then () else
    begin
      timeout_handler_activated := true;
(*
      eprintf "Info: timeout_handler started@.";
*)
      O.timeout ~ms:100 timeout_handler
    end

(* idle handler *)


type action =
  | Action_proof_attempt of bool * int * int * in_channel option * string * Driver.driver *
    (proof_attempt_status -> unit) * Task.task
  | Action_delayed of (unit -> unit)

let actions_queue = Queue.create ()

let idle_handler_activated = ref false

let idle_handler () =
  try
    begin
      match Queue.pop actions_queue with
	| Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
			       callback,goal) ->
	    callback Scheduled;
	    if debug then
	      Format.eprintf "Task for prover: %a@."
		(Driver.print_task driver) goal;
	    let pre_call =
	      Driver.prove_task ?old ~command ~timelimit ~memlimit driver goal
	    in
	    Queue.push (callback,pre_call) proof_attempts_queue;
	    run_timeout_handler ()
        | Action_delayed callback -> callback ()
    end;
    true
  with Queue.Empty ->
    idle_handler_activated := false;
(*
    eprintf "Info: idle_handler stopped@.";
*)
    false

let run_idle_handler () =
  if !idle_handler_activated then () else
    begin
      idle_handler_activated := true;
(*
      eprintf "Info: idle_handler started@.";
*)
      O.idle idle_handler
    end

(* main scheduling functions *)

let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback goal =
  Queue.push
    (Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
			callback,goal))
    actions_queue;
  run_idle_handler ()

let schedule_edition command callback =
  let precall =
    Call_provers.call_on_buffer ~command ~regexps:[] ~timeregexps:[]
      ~exitcodes:[(0,Call_provers.Unknown "")] ~filename:"" (Buffer.create 1)
  in
  callback Running;
  running_proofs := (callback, precall ()) :: !running_proofs;
  run_timeout_handler ()

let schedule_delayed_action callback =
  Queue.push (Action_delayed callback) actions_queue;
  run_idle_handler ()

let apply_transformation ~callback transf goal =
  callback (Trans.apply transf goal)

let apply_transformation_l ~callback transf goal =
  callback (Trans.apply transf goal)


let edit_proof ~debug:_ ~editor ~file ~driver ~callback goal =
  let old =
    if Sys.file_exists file
    then
      begin
	let backup = file ^ ".bak" in
        Sys.rename file backup;
        Some(open_in backup)
      end
    else None
  in
  let ch = open_out file in
  let fmt = formatter_of_out_channel ch in
  Driver.print_task ?old driver fmt goal;
  Util.option_iter close_in old;
  close_out ch;
  let command = editor ^ " " ^ file in
  (*
  let _ = Sys.command command in
  callback ()
  *)
  schedule_edition command callback


(*******************************)
(* explanations *)
(****************)


  let expl_regexp = Str.regexp "expl:\\(.*\\)"

  let rec get_labels f =
    (match f.Term.f_node with
      | Term.Fbinop(Term.Fimplies,_,f) -> get_labels f
      | Term.Fquant(Term.Fforall,fq) ->
	  let (_,_,f) = Term.f_open_quant fq in get_labels f
      | Term.Flet(_,fb) ->
	  let (_,f) = Term.f_open_bound fb in get_labels f
      | Term.Fcase(_,[fb]) ->
	  let (_,f) = Term.f_open_branch fb in get_labels f
      | _ -> [])
    @ f.Term.f_label

  let get_explanation id fmla =
    let r = ref None in
(*
    let fl = Debug.lookup_flag "print_labels" in
    Debug.set_flag fl;
    Format.eprintf "searching expl in formula '%a'@." Pretty.print_fmla fmla;
*)
    List.iter
      (fun s ->
         if Str.string_match expl_regexp s 0 then
           begin
	     let e = Str.matched_group 1 s in
(*
	     Format.eprintf "found explanation: '%s'" e;
*)
	     r := Some e
	   end)
      (id.Ident.id_label @ get_labels fmla);
    !r



(******************************)
(* raw additions to the model *)
(******************************)

let raw_add_external_proof ~obsolete ~edit g p result =
  let key = O.create ~parent:g.goal_key () in
  let a = { prover = p;
            proof_goal = g;
            proof_key = key;
            proof_obsolete = obsolete;
	    proof_state = result;
            edited_as = edit;
          }
  in
  Hashtbl.add g.external_proofs p.prover_name a;
  !notify_fun (Proof_attempt a);
  (* !notify_fun (Goal g) ? *)
  a

(* [raw_add_goal parent name expl t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_goal parent name expl t =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
  in
  let key = O.create ~parent:parent_key () in
  let goal = { goal_name = name;
               goal_expl = expl;
	       parent = parent;
               task = t ;
               goal_key = key;
               external_proofs = Hashtbl.create 7;
               transformations = Hashtbl.create 3;
               proved = false;
             }
  in
  !notify_fun (Goal goal);
  goal


(* [raw_add_transformation g name adds a transformation to the given goal g
   Adds no subgoals, thus this should not be exported
*)
let raw_add_transformation g tr_name =
  let parent = g.goal_key in
  let key = O.create ~parent () in
  let tr = { parent_goal = g;
             transf_proved = false;
             transf_key = key;
             subgoals = [];
           }
  in
  Hashtbl.add g.transformations tr_name tr;
  tr

let raw_add_theory mfile th =
  let parent = mfile.file_key in
  let key = O.create ~parent () in
  let mth = { theory = th;
              theory_key = key;
              theory_parent = mfile;
              goals = [] ;
              verified = false }
  in
  mth







let add_theory mfile th =
  let tasks = List.rev (Task.split_theory th None None) in
  let mth = raw_add_theory mfile th in
  let goals =
    List.fold_left
      (fun acc t ->
         let id = (Task.task_goal t).Decl.pr_name in
         let name = id.Ident.id_string in
         let expl = get_explanation id (Task.task_goal_fmla t) in
         let goal = raw_add_goal (Parent_theory mth) name expl t in
         goal :: acc)
      []
      tasks
  in
  mth.goals <- List.rev goals;
  if goals = [] then set_theory_proved ~propagate:false mth;
  mth

let raw_add_file f =
  let parent = O.create () in
  let mfile = { file_name = f;
                file_key = parent;
                theories = [] ;
                file_verified = false }
  in
  all_files := !all_files @ [mfile];
  mfile

let add_file f theories =
  let theories =
    Theory.Mnm.fold
      (fun name th acc ->
         match th.Theory.th_name.Ident.id_origin with
           | Ident.User l -> (l,name,th)::acc
           | _ -> (Loc.dummy_position,name,th)::acc)
      theories []
  in
  let theories = List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    theories
  in
  let mfile = raw_add_file f in
  let mths =
    List.fold_left
      (fun acc (_,_,t) ->
         let mth = add_theory mfile t in
         mth :: acc)
      [] theories
  in
  mfile.theories <- List.rev mths;
  if theories = [] then set_file_verified mfile




(**********************************)
(* reload a file                  *)
(**********************************)

(*
let rec reimport_any_goal parent gid gname t db_goal goal_obsolete =
  let info = get_explanation gid (Task.task_goal_fmla t) in
  let goal = raw_add_goal parent gname info t in
  let proved = ref false in
  let external_proofs = Db.external_proofs db_goal in
  Db.Hprover.iter
    (fun pid a ->
       let pname = Db.prover_name pid in
       try
         let p = Util.Mstr.find pname gconfig.provers in
         let s,t,o,edit = Db.status_and_time a in
         if goal_obsolete && not o then Db.set_obsolete a;
         let obsolete = goal_obsolete or o in
         let s = match s with
           | Db.Undone -> Call_provers.HighFailure
           | Db.Done r ->
	       if r = Call_provers.Valid then
		 if not obsolete then proved := true;
	       r
         in
	 let r = { Call_provers.pr_answer = s;
		   Call_provers.pr_output = "";
		   Call_provers.pr_time = t;
		 }
	 in
         let (_pa : Model.proof_attempt) =
           Helpers.add_external_proof_row ~obsolete ~edit goal p a
	     (Gscheduler.Done r)
         in
         ((* something TODO ?*))
       with Not_found ->
         eprintf
           "Warning: prover %s appears in database but is not installed.@."
           pname
    )
    external_proofs;
  let transformations = Db.transformations db_goal in
  Db.Htransf.iter
    (fun tr_id tr ->
       let trname = Db.transf_name tr_id in
       eprintf "Reimporting transformation %s for goal %s @." trname gname;
       let trans = trans_of_name trname in
       let subgoals = apply_trans trans t in
       let mtr = Helpers.add_transformation_row goal tr trname in
       let db_subgoals = Db.subgoals tr in
       let reimported_goals,db_subgoals,_ =
         List.fold_left
           (fun (acc,db_subgoals,count) subtask ->
              let id = (Task.task_goal subtask).Decl.pr_name in
              let subgoal_name = gname ^ "." ^ (string_of_int count) in
              let sum = task_checksum subtask in
              let subtask_db,db_subgoals =
                try
		  let g = Util.Mstr.find sum db_subgoals in
		  (* a subgoal has the same check sum *)
		  (Some g, Util.Mstr.remove sum db_subgoals)
                with Not_found -> None,db_subgoals
              in
              ((count,id,subgoal_name,subtask,sum,subtask_db) :: acc,
	       db_subgoals,
	       count+1))
           ([],db_subgoals,1) subgoals
       in
       let other_goals =
	 Util.Mstr.fold
	   (fun _ g acc -> (Db.goal_name g,g)::acc)
	   db_subgoals
	   []
       in
       let other_goals =
	 List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2) other_goals
       in
       let rec merge_goals new_goals old_goals proved acc =
	 match new_goals with
	   | [] -> acc, proved
	   | (_,id,subgoal_name,subtask,sum,g_opt)::rem ->
	       let db_g,subgoal_obsolete,old_goals =
		 match g_opt with
		   | Some g -> g,false,old_goals
		   | None ->
		       match old_goals with
			 | [] ->
			     (* create a new goal in db *)
			     Db.add_subgoal tr subgoal_name sum,
			     false, old_goals
			 | (_goal_name,g) :: r ->
			     g, true, r
	       in
               let subgoal,subgoal_proved =
                 reimport_any_goal
                   (Model.Transf mtr) id
                   subgoal_name subtask db_g subgoal_obsolete
              in
              merge_goals rem old_goals (proved && subgoal_proved)
		(subgoal :: acc)
       in
       let goals, subgoals_proved =
	 merge_goals (List.rev reimported_goals) other_goals true []
       in
(*
       let goals,_,subgoals_proved =
         List.fold_left
           (fun (acc,count,proved) subtask ->
              let _id = (Task.task_goal subtask).Decl.pr_name in
              let subgoal_name = gname ^ "." ^ (string_of_int count) in
              let sum = task_checksum subtask in
              let subtask_db =
                try Util.Mstr.find sum db_subgoals
		  (* a subgoal has the same check sum *)
                with Not_found ->
		  (* otherwise, create a new one *)
                  Db.add_subgoal tr subgoal_name sum
              in
              let subgoal,subgoal_proved =
                reimport_any_goal
                  (Model.Transf mtr) subgoal_name subtask subtask_db
                  false (* subgoal_obsolete *)
              in
              (subgoal :: acc, count+1,proved && subgoal_proved))
           ([],1,true) subgoals
       in
*)
       mtr.Model.subgoals <- List.rev goals;
       if subgoals_proved (* TODO : && not obsolete *)
       then proved := true
    )
    transformations;
  if !proved then Helpers.set_proved ~propagate:false goal;
  goal,!proved


let reimport_root_goal mth tname goals t : Model.goal * bool =
  (* re-imports DB informations of a goal in theory mth (named tname)
     goals is a table, indexed by names of DB goals formerly known to be
     a in theory mth.  returns true whenever the task t is known to be
     proved *)
  let id = (Task.task_goal t).Decl.pr_name in
  let gname = id.Ident.id_string
  in
  let sum = task_checksum t in
  let db_goal,goal_obsolete =
    try
      let dbg = Util.Mstr.find gname goals in
      let db_sum = Db.task_checksum dbg in
      let goal_obsolete = sum <> db_sum in
      if goal_obsolete then
        begin
          eprintf "Goal %s.%s has changed@." tname gname;
          Db.change_checksum dbg sum
        end;
      dbg,goal_obsolete
    with Not_found ->
      let dbg = Db.add_goal mth.Model.theory_db gname sum in
      dbg,false
  in
  reimport_any_goal (Model.Theory mth) id gname t db_goal goal_obsolete

(* reimports all files *)
let files_in_db = Db.files ()

let () =
  List.iter
    (fun (f,fn) ->
       eprintf "Reimporting file '%s'@." fn;
       let mfile = Helpers.add_file_row fn f in
       try
	 let theories = read_file fn in
	 let ths = Db.theories f in
	 let (mths,file_proved) =
	   List.fold_left
             (fun (acc,file_proved) (_,tname,th) ->
		eprintf "Reimporting theory '%s'@."tname;
		let db_th =
		  try
                    Util.Mstr.find tname ths
		  with Not_found -> Db.add_theory f tname
		in
		let mth = Helpers.add_theory_row mfile th db_th in
		let goals = Db.goals db_th in
		let tasks = List.rev (Task.split_theory th None None) in
		let goals,proved = List.fold_left
		  (fun (acc,proved) t ->
                     let (g,p) = reimport_root_goal mth tname goals t in
                     (g::acc,proved && p))
		  ([],true) tasks
		in
		mth.Model.goals <- List.rev goals;
		(* TODO: what to do with remaining tasks in Db ???
		   for the moment they remain in the db, but they are not shown
		*)
		if proved then Helpers.set_theory_proved ~propagate:false mth;
		(mth::acc,file_proved && proved))
             ([],true) theories
	 in
	 (* TODO: detecter d'eventuelles vieilles theories, qui seraient donc
            dans [ths] mais pas dans [theories]
	 *)
	 mfile.Model.theories <- List.rev mths;
	 if file_proved then Helpers.set_file_verified mfile
      with e ->
	eprintf "@[Error while reading file@ '%s':@ %a@.@]" fn
          Exn_printer.exn_printer e;
	exit 1
    )
    files_in_db

*)


(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let redo_external_proof g a =
  (* check that the state is not Scheduled or Running *)
  let running = match a.proof_state with
    | Scheduled | Running -> true
    | Done _ | Undone | InternalFailure _ -> false
  in
  if running then ()
    (* info_window `ERROR "Proof already in progress" *)
  else
    let p = a.prover in
    let callback result =
      set_proof_state ~obsolete:false a result;
      match result with
	| Done r ->
	    if r.Call_provers.pr_answer = Call_provers.Valid then
	      set_proved ~propagate:true a.proof_goal
	| _ -> ()
    in
    let old = if a.edited_as = "" then None else
      begin
	Format.eprintf "Info: proving using edited file %s@." a.edited_as;
	(Some (open_in a.edited_as))
      end
    in
    schedule_proof_attempt
      ~debug:false ~timelimit:10 ~memlimit:0
      ?old ~command:p.command ~driver:p.driver
      ~callback
      g.task

let rec prover_on_goal p g =
  let id = p.prover_id in
  let a =
    try Hashtbl.find g.external_proofs id
    with Not_found ->
      raw_add_external_proof ~obsolete:false ~edit:"" g p Undone
  in
  let () = redo_external_proof g a in
  Hashtbl.iter
    (fun _ t -> List.iter (prover_on_goal p) t.subgoals)
    g.transformations

let rec prover_on_goal_or_children ~context_unproved_goals_only p g =
  if not (g.proved && context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter (prover_on_goal_or_children ~context_unproved_goals_only p)
             t.subgoals) g.transformations;
      if !r then prover_on_goal p g
    end

let run_prover ~context_unproved_goals_only pr a =
  match a with
    | Goal g -> 
	prover_on_goal_or_children ~context_unproved_goals_only pr g
    | Theory th -> 
	List.iter 
	  (prover_on_goal_or_children ~context_unproved_goals_only pr) 
	  th.goals
    | File file -> 
        List.iter
          (fun th ->
             List.iter 
	       (prover_on_goal_or_children ~context_unproved_goals_only pr)
	       th.goals)
          file.theories
    | Proof_attempt a ->
        prover_on_goal_or_children ~context_unproved_goals_only pr a.proof_goal
    | Transformation tr ->
        List.iter 
	  (prover_on_goal_or_children ~context_unproved_goals_only pr) 
	  tr.subgoals

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let proof_successful a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid } -> true
    | _ -> false

let rec replay_on_goal_or_children ~context_unproved_goals_only g =
  Hashtbl.iter
    (fun _ a ->
       if a.proof_obsolete then
         if not context_unproved_goals_only || proof_successful a
         then redo_external_proof g a)
    g.external_proofs;
  Hashtbl.iter
    (fun _ t -> 
       List.iter 
	 (replay_on_goal_or_children ~context_unproved_goals_only) 
	 t.subgoals)
    g.transformations

let replay ~context_unproved_goals_only a =
  match a with
    | Goal g ->
        replay_on_goal_or_children ~context_unproved_goals_only g
    | Theory th ->
        List.iter 
	  (replay_on_goal_or_children ~context_unproved_goals_only)
	  th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter 
	       (replay_on_goal_or_children ~context_unproved_goals_only)
	       th.goals)
          file.theories
    | Proof_attempt a ->
        replay_on_goal_or_children ~context_unproved_goals_only a.proof_goal
    | Transformation tr ->
        List.iter 
	  (replay_on_goal_or_children ~context_unproved_goals_only)
	  tr.subgoals


(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

(*

let transformation_on_goal g trans_name trans =
  if not g.proved then
    let callback subgoals =
      let b =
 	match subgoals with
	  | [task] ->
              let s1 = task_checksum g.task in
              let s2 = task_checksum task in
	      (*
                eprintf "Transformation returned only one task. sum before = %s, sum after = %s@." (task_checksum g.task) (task_checksum task);
                eprintf "addresses: %x %x@." (Obj.magic g.task) (Obj.magic task);
	      *)
              s1 <> s2
                (* task != g.task *)
	  | _ -> true
      in
      if b then
	let transf_id = Db.transf_from_name trans_name in
	let db_transf = Db.add_transformation g.goal_db transf_id	in
	let tr = Helpers.add_transformation_row g db_transf trans_name in
	let goal_name = g.goal_name in
	let fold =
	  fun (acc,count) subtask ->
	    let id = (Task.task_goal subtask).Decl.pr_name in
            let expl =
              get_explanation id (Task.task_goal_fmla subtask)
            in
	    let subgoal_name =
	      goal_name ^ "." ^ (string_of_int count)
	    in
	    let sum = task_checksum subtask in
	    let subtask_db =
	      Db.add_subgoal db_transf subgoal_name sum
	    in
	    let goal =
	      Helpers.add_goal_row (Transf tr)
		subgoal_name expl subtask subtask_db
	    in
	    (goal :: acc, count+1)
	in
	let goals,_ =
	  List.fold_left fold ([],1) subgoals
	in
	tr.subgoals <- List.rev goals;
	Hashtbl.add g.transformations trans_name tr
    in
    apply_transformation ~callback
      trans g.task

let split_goal g =
  Gscheduler.schedule_delayed_action
    (fun () ->
       transformation_on_goal g "split_goal" split_transformation)

let inline_goal g = transformation_on_goal g "inline_goal" inline_transformation

let rec split_goal_or_children g =
  if not g.proved then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter split_goal_or_children
             t.subgoals) g.transformations;
      if !r then split_goal g
    end

let rec inline_goal_or_children g =
  if not g.proved then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter inline_goal_or_children
             t.subgoals) g.transformations;
      if !r then inline_goal g
    end

let split_selected_goal_or_children row =
  let row = goals_model#get_iter row in
  match goals_model#get ~row ~column:index_column with
    | Row_goal g ->
        split_goal_or_children g
    | Row_theory th ->
        List.iter split_goal_or_children th.goals
    | Row_file file ->
        List.iter
          (fun th ->
             List.iter split_goal_or_children th.goals)
          file.theories
    | Row_proof_attempt a ->
        split_goal_or_children a.proof_goal
    | Row_transformation tr ->
        List.iter split_goal_or_children tr.subgoals


let inline_selected_goal_or_children row =
  let row = goals_model#get_iter row in
  match goals_model#get ~row ~column:index_column with
    | Row_goal g ->
        inline_goal_or_children g
    | Row_theory th ->
        List.iter inline_goal_or_children th.goals
    | Row_file file ->
        List.iter
          (fun th ->
             List.iter inline_goal_or_children th.goals)
          file.theories
    | Row_proof_attempt a ->
        inline_goal_or_children a.proof_goal
    | Row_transformation tr ->
        List.iter inline_goal_or_children tr.subgoals

let split_selected_goals () =
  List.iter
    split_selected_goal_or_children
    goals_view#selection#get_selected_rows


let inline_selected_goals () =
  List.iter
    inline_selected_goal_or_children
    goals_view#selection#get_selected_rows


*)


(*****************************)
(* method: edit current goal *)
(*****************************)

(*

let ft_of_th th =
  (Filename.basename th.theory_parent.file_name,
   th.theory.Theory.th_name.Ident.id_string)

let rec ft_of_goal g =
  match g.parent with
    | Transf tr -> ft_of_goal tr.parent_goal
    | Theory th -> ft_of_th th

let ft_of_pa a =
  ft_of_goal a.proof_goal

let edit_selected_row p =
  let row = goals_model#get_iter p in
  match goals_model#get ~row ~column:index_column with
    | Row_goal _g ->
        ()
    | Row_theory _th ->
        ()
    | Row_file _file ->
        ()
    | Row_proof_attempt a ->
        (* check that the state is not Scheduled or Running *)
        let running = match a.proof_state with
          | Gscheduler.Scheduled | Gscheduler.Running -> true
          | Gscheduler.Undone | Gscheduler.Done _ | Gscheduler.InternalFailure _ -> false
        in
        if running then
          info_window `ERROR "Edition already in progress"
        else
        let g = a.proof_goal in
	let t = g.task in
	let driver = a.prover.driver in
	let file =
          match a.edited_as with
            | "" ->
		let (fn,tn) = ft_of_pa a in
		let file = Driver.file_of_task driver
                  (Filename.concat project_dir fn) tn t
		in
		(* Uniquify the filename if it exists on disk *)
		let i =
                  try String.rindex file '.'
                  with _ -> String.length file
		in
		let name = String.sub file 0 i in
		let ext = String.sub file i (String.length file - i) in
		let i = ref 1 in
		while Sys.file_exists
		  (name ^ "_" ^ (string_of_int !i) ^ ext) do
		    incr i
		done;
		let file = name ^ "_" ^ (string_of_int !i) ^ ext in
		a.edited_as <- file;
		Db.set_edited_as a.proof_db file;
		file
	    | f -> f
	in
        let old_status = a.proof_state in
        let callback res =
          match res with
            | Gscheduler.Done _ ->
                Helpers.set_proof_state ~obsolete:false a old_status
            | _ ->
                Helpers.set_proof_state ~obsolete:false a res
        in
        let editor =
          match a.prover.editor with
            | "" -> gconfig.default_editor
            | _ -> a.prover.editor
        in
        Gscheduler.edit_proof ~debug:false ~editor
          ~file
          ~driver
          ~callback
          t
    | Row_transformation _tr ->
        ()

*)

(*************)
(* removing  *)
(*************)

(*

let remove_proof_attempt a =
  Db.remove_proof_attempt a.proof_db;
  let (_:bool) = goals_model#remove a.proof_row in
  let g = a.proof_goal in
  Hashtbl.remove g.external_proofs a.prover.prover_id;
  Helpers.check_goal_proved g

let remove_transf t =
  (* TODO: remove subgoals first !!! *)
  Db.remove_transformation t.transf_db;
  let (_:bool) = goals_model#remove t.transf_row in
  let g = t.parent_goal in
  Hashtbl.remove g.transformations "split" (* hack !! *);
  Helpers.check_goal_proved g


let confirm_remove_row r =
  let row = goals_model#get_iter r in
  match goals_model#get ~row ~column:index_column with
    | Row_goal _g ->
	info_window `ERROR "Cannot remove a goal"
    | Row_theory _th ->
	info_window `ERROR "Cannot remove a theory"
    | Row_file _file ->
	info_window `ERROR "Cannot remove a file"
    | Row_proof_attempt a ->
	info_window
	  ~callback:(fun () -> remove_proof_attempt a)
	  `QUESTION
	  "Do you really want to remove the selected proof attempt?"
    | Row_transformation tr ->
	info_window
	  ~callback:(fun () -> remove_transf tr)
	  `QUESTION
	  "Do you really want to remove the selected transformation
and all its subgoals?"

let confirm_remove_selection () =
  match goals_view#selection#get_selected_rows with
    | [] -> ()
    | [r] -> confirm_remove_row r
    | _ ->
        info_window `INFO "Please select exactly one item to remove"


let rec clean_goal g =
  if g.proved then
    begin
      Hashtbl.iter
        (fun _ a ->
           if a.proof_obsolete || not (proof_successful a) then
             remove_proof_attempt a)
        g.external_proofs;
      Hashtbl.iter
        (fun _ t ->
           if not t.transf_proved then
             remove_transf t)
        g.transformations
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter clean_goal t.subgoals)
      g.transformations


let clean_row r =
  let row = goals_model#get_iter r in
  match goals_model#get ~row ~column:index_column with
    | Row_goal g -> clean_goal g
    | Row_theory th ->
        List.iter clean_goal th.goals
    | Row_file file ->
        List.iter
          (fun th ->
             List.iter clean_goal th.goals)
          file.theories
    | Row_proof_attempt a ->
        clean_goal a.proof_goal
    | Row_transformation tr ->
        List.iter clean_goal tr.subgoals


*)

end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
