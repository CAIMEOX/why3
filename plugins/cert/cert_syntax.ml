open Why3
open Term
open Decl
open Theory
open Task

type ident = Ident.ident

type cterm = CTapp of ident
           | CTand of cterm * cterm
           | CTor of cterm * cterm

type ctask = { cctxt : (ident * cterm) list; cgoal : cterm }

type dir = Left | Right
type certif = Skip
            | Axiom of ident
            | Split of certif * certif
            | Dir of dir * certif

type ctrans = task -> task list * certif


(** Translating Why3 tasks to simplified certificate tasks *)

let rec translate_term (t : term) : cterm =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
  | Tbinop (Tand, t1, t2) -> CTand (translate_term t1, translate_term t2)
  | Tbinop (Tor, t1, t2) -> CTor (translate_term t1, translate_term t2)
  | _ -> invalid_arg "Cert_syntax.translate_term"

let translate_decl (d : decl) : (ident * cterm) list =
  match d.d_node with
  | Dprop (_, pr, f) -> [pr.pr_name, translate_term f]
  | _ -> []

let translate_tdecl (td : tdecl) : (ident * cterm) list =
  match td.td_node with
  | Decl d -> translate_decl d
  | _ -> []

let rec translate_ctxt = function
  | Some {task_decl = d; task_prev = p} ->
      translate_tdecl d @ translate_ctxt p
  | None -> []

let translate_task (t : task) =
  let gd, t = try task_separate_goal t
              with GoalNotFound -> invalid_arg "Cert_syntax.translate_task" in
  let g = match translate_tdecl gd with
    | [_, g] -> g
    | _ -> assert false in
  {cctxt = translate_ctxt t; cgoal = g}


(** Using ctasks and certificates *)

(* check_certif replays the certificate on a ctask *)
exception Certif_verif_failed
let rec check_certif ({cctxt = c; cgoal = t} as ctask) (cert : certif)  : ctask list =
  match cert with
    | Skip -> [ctask]
    | Axiom id ->
        begin try if List.assoc id c <> t then raise Not_found else []
              with Not_found -> raise Certif_verif_failed end
    | Split (c1, c2) ->
        begin match t with
        | CTand (t1, t2) -> check_certif {ctask with cgoal = t1} c1 @
                              check_certif {ctask with cgoal = t2} c2
        | _ -> raise Certif_verif_failed end
    | Dir (d, c) ->
        begin match t, d with
        | CTor (t, _), Left | CTor (_, t), Right ->
            check_certif {ctask with cgoal = t} c
        | _ -> raise Certif_verif_failed end


(* Creates a certified transformation from a transformation with certificate *)
let checker_ctrans ctr task =
  try let ltask, cert = ctr task in
      let ctask = translate_task task in
      let lctask = check_certif ctask cert in
      if lctask = List.map translate_task ltask then ltask
      else failwith "Certif verification failed."
  with e -> raise (Trans.TransFailure ("cert_trans", e))

(* Generalize ctrans on (task list * certif) *)
let ctrans_gen (ctr : ctrans) (ts, c) =
  let rec fill c ts = match c with
      | Skip -> begin match ts with
                | [] -> assert false
                | t::ts -> let l2, c2 = ctr t in
                           c2, l2, ts end
      | Axiom _ -> c, [], ts
      | Split (c1, c2) -> let c1, l1, ts1 = fill c1 ts in
                          let c2, l2, ts2 = fill c2 ts1 in
                          Split (c1, c2), l1 @ l2, ts2
      | Dir (d, c) -> let c, l, ts = fill c ts in
                      Dir (d, c), l, ts
  in
  let c, l, ts = fill c ts in
  assert (ts = []);
  l, c

let rec nocuts = function
  | Skip -> false
  | Axiom _ -> true
  | Split (c1, c2) -> nocuts c1 && nocuts c2
  | Dir (_, c) -> nocuts c

let same_cert (_, cert1) (_, cert2) = cert1 = cert2

(** Primitive transformations with certificate *)

(* Identity transformation with certificate *)
let id task = [task], Skip

(* Assumption with certificate *)
let assumption_decl g (d : decl) =
  match d.d_node with
  | Dprop (_, pr, f) -> if t_equal_nt_na g f
                        then Some pr.pr_name
                        else None
  | _ -> None

let assumption_tdecl g (td : tdecl) =
  match td.td_node with
  | Decl d -> assumption_decl g d
  | _ -> None

let rec assumption_ctxt g = function
  | Some {task_decl = d; task_prev = p} ->
      begin match assumption_tdecl g d with
      | Some h -> h
      | None -> assumption_ctxt g p end
  | None -> raise Not_found

let assumption t =
  let g = try task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption_task" in
  let _, t' = task_separate_goal t in
  try let h = assumption_ctxt g t' in [], Axiom h
  with Not_found -> [t], Skip

(* Split with certificate *)
let split t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split_certif" in
  let _, c = task_separate_goal t in
  match g.t_node with
  | Tbinop (Tand, f1, f2) ->
      let tf1 = add_decl c (create_prop_decl Pgoal pr f1) in
      let tf2 = add_decl c (create_prop_decl Pgoal pr f2) in
      [tf1;tf2], Split (Skip, Skip)
  | _ -> [t], Skip

(* Direction with certificate *)
let dir d t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split_certif" in
  let _, c = task_separate_goal t in
  match g.t_node, d with
  | Tbinop (Tor, f, _), Left | Tbinop (Tor, _, f), Right ->
      let tf = add_decl c (create_prop_decl Pgoal pr f) in
      [tf], Dir (d, Skip)
  | _ -> [t], Skip


(** Transformials *)

(* Compose transformations with certificate *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

(* If Then Else on transformations with certificate *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  let ((_, cert) as tri_task) = tri task in
  if cert <> Skip (* égalité de task fait (error : compare on functional values) *)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task

(* Try on transformations with certificate *)
let rec try_close (lctr : ctrans list) : ctrans = fun task ->
  match lctr with
  | [] -> id task
  | h::t -> let lctask_h, cert_h = h task in
            if lctask_h = []
            then [], cert_h
            else try_close t task

(* Repeat on transformations with certificate *)
let repeat (ctr : ctrans) : ctrans = fun task ->
  let gen_task = id task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if same_cert new_gt gt (* [new_gt = gt] égalité de task fait (error : compare on functional values) *)
    then gt
    else loop new_gt in
  loop gen_task


(** Derived transformations with certificate *)

let split_assumption = compose split assumption

let rec intuition task =
  repeat (compose assumption
          (compose split
           (try_close [ite (dir Left) intuition id;
                       ite (dir Right) intuition id]))) task


(** Certified transformations *)

let assumption_trans = checker_ctrans assumption
let split_trans = checker_ctrans split
let left_trans = checker_ctrans (dir Left)
let right_trans = checker_ctrans (dir Right)
let split_assumption_trans = checker_ctrans split_assumption
let intuition_trans = checker_ctrans intuition

let () =
  Trans.register_transform_l "assumption_cert" (Trans.store assumption_trans)
    ~desc:"A certified version of coq tactic [assumption]";
  Trans.register_transform_l "split_cert" (Trans.store split_trans)
    ~desc:"A certified version of (simplified) coq tactic [split]";
  Trans.register_transform_l "split_assumption_cert" (Trans.store split_assumption_trans)
    ~desc:"A certified version of (simplified) coq tactic [split; assumption]";
  Trans.register_transform_l "left_cert" (Trans.store left_trans)
    ~desc:"A certified version of coq tactic [left]";
  Trans.register_transform_l "right_cert" (Trans.store right_trans)
    ~desc:"A certified version of coq tactic [right]";
  Trans.register_transform_l "intuition_cert" (Trans.store intuition_trans)
    ~desc:"A certified version of (simplified) coq tactic [intuition]"
