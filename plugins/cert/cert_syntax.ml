open Why3
open Ident
open Term
open Decl
open Theory
open Task
open Format

type ident = Ident.ident

type binop = CTand | CTor | CTiff | CTimplies
type cterm = CTapp of ident
           | CTbinop of binop * cterm * cterm

type ctask = {hyp : cterm Mid.t; concl : cterm Mid.t}

type dir = Left | Right
type path = dir list
type certif = Skip
            | Axiom of ident
            | Split of certif * certif
            | Dir of dir * certif
            | Intro of ident * certif
            | Rewrite of ident * ident option * path * certif

type ctrans = task -> task list * certif

let rec cterm_equal t1 t2 =
  match t1, t2 with
  | CTapp i1, CTapp i2 -> Ident.id_equal i1 i2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | _ -> false

let ctask_equal {hyp = h1; concl = c1} {hyp = h2; concl = c2} =
  Mid.equal cterm_equal h1 h2 && Mid.equal cterm_equal c1 c2

exception Not_normalized_task
let normalized_goal (cta : ctask) : cterm option =
  try let fold_concl g_opt _ ng = match g_opt with
        | None -> Some ng
        | Some _ -> raise Not_normalized_task in
      match Mid.fold_left fold_concl None cta.concl with
      | None -> raise Not_normalized_task
      | Some x -> Some x
  with Not_normalized_task -> None

let new_ctask mid1 mid2 = { hyp = mid1; concl = mid2 }

(* for debugging *)
let rec print_certif where cert =
  let oc = open_out where in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prc (fmt : formatter) = function
  | Skip -> fprintf fmt "Skip"
  | Axiom i -> fprintf fmt "Axiom %a" pri i
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Dir (d, c) -> fprintf fmt "Dir @[(%a,@ %a)@]" prd d prc c
  | Intro (i, c) -> fprintf fmt "Intro @[(%a,@ %a)@]" pri i prc c
  | Rewrite (_, _, p, c) -> fprintf fmt "Rewrite @[([%a],@ term1,@ term2,@ %a)@]" pp p prc c
and pri fmt i =
  fprintf fmt "%s" Ident.(id_clone i |> preid_name)
and prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"
and pp l = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "; ") prd l

let mct mid1 mid2 = {hyp = mid1; concl = mid2}

(** Translating Why3 tasks to simplified certificate tasks *)

let rec translate_term (t : term) : cterm =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
  | Tbinop (Tand, t1, t2) -> CTbinop (CTand, translate_term t1, translate_term t2)
  | Tbinop (Tor , t1, t2) -> CTbinop (CTor , translate_term t1, translate_term t2)
  | Tbinop (Tiff, t1, t2) -> CTbinop (CTiff, translate_term t1, translate_term t2)
  | Tbinop (Timplies, t1, t2) -> CTbinop (CTimplies, translate_term t1, translate_term t2)
  | _ -> invalid_arg "Cert_syntax.translate_term"

let translate_decl (d : decl) : ctask =
  match d.d_node with
  | Dprop (Pgoal, pr, f) ->
      let hyp = Mid.singleton pr.pr_name (translate_term f) in
      mct hyp Mid.empty
  | Dprop (_, pr, f) ->
      let concl = Mid.singleton pr.pr_name (translate_term f) in
      mct Mid.empty concl
  | _ -> mct Mid.empty Mid.empty

let translate_tdecl (td : tdecl) : ctask =
  match td.td_node with
  | Decl d -> translate_decl d
  | _ -> mct Mid.empty Mid.empty

let union_ctask {hyp = h1; concl = c1} {hyp = h2; concl = c2} =
  mct (Mid.set_union h1 h2) (Mid.set_union c1 c2)

let rec translate_task_acc acc = function
  | Some {task_decl = d; task_prev = p} ->
      let new_acc = union_ctask acc (translate_tdecl d) in
      translate_task_acc new_acc p
  | None -> acc

let translate_task t =
  translate_task_acc (mct Mid.empty Mid.empty) t

(** Using ctasks and certificates *)

(* check_certif replays the certificate on a ctask *)
exception Certif_verif_failed

let rec check_rewrite p tl tr t =
  match p, t with
  | [], t when cterm_equal t tl -> Some tr
  | Left::prest, CTbinop (op, t1, t2) ->
      begin match check_rewrite prest tl tr t1 with
      | Some nt1 -> Some (CTbinop (op, nt1, t2))
      | None -> None end
  | Right::prest, CTbinop (op, t1, t2) ->
      begin match check_rewrite prest tl tr t2 with
      | Some nt2 -> Some (CTbinop (op, t1, nt2))
      | None -> None end
  | _ -> None

let rec check_certif cta (cert : certif) : ctask list =
  match cert with
    | Skip -> [cta]
    | Axiom id ->
        begin match Mid.find_opt id cta with
        | Some (te, b) when b = false -> []
        | _ -> raise Certif_verif_failed end
    | Split (c1, c2) ->
        begin match t with
        | CTbinop (CTand, t1, t2) -> check_certif {ctask with cgoal = t1} c1 @
                                       check_certif {ctask with cgoal = t2} c2
        | CTbinop (CTiff, t1, t2) -> let direct = CTbinop (CTimplies, t1, t2) in
                                     let indirect = CTbinop (CTimplies, t2, t1) in
                                     check_certif {ctask with cgoal = direct} c1 @
                                       check_certif {ctask with cgoal = indirect} c2
        | _ -> raise Certif_verif_failed end
    | Dir (d, cer) ->
        begin match t, d with
        | CTbinop(CTor, t, _), Left | CTbinop (CTor, _, t), Right ->
            check_certif {ctask with cgoal = t} cer
        | _ -> raise Certif_verif_failed end
    | Intro (i, c) ->
        begin match t with
        | CTbinop (CTimplies, f1, f2) ->
            let new_ctask = {cctxt = (i, f1) :: ctx; cgoal = f2} in
            check_certif new_ctask c
        | _ -> raise Certif_verif_failed end
    | Rewrite (rew_hyp, h, p, c) ->
        begin match check_rewrite p rew_hyp h t with
        | Some nt -> let ntask = change rew_hyp nt ctask in
                     check_certif ntask c
        | None -> raise Certif_verif_failed end

(* Creates a certified transformation from a transformation with certificate *)
let checker_ctrans ctr task =
  try let ltask, cert = ctr task in
      print_certif "/tmp/certif.log" cert;
      let ctask = translate_task task in
      let lctask = check_certif ctask cert in
      if Lists.equal ctask_equal lctask (List.map translate_task ltask)
      then ltask
      else raise Certif_verif_failed
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_trans", e))

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
      | Intro (i, c) -> let c, l, ts = fill c ts in
                        Intro (i, c), l, ts
      | Rewrite (p, t1, t2, c) -> let c, l, ts = fill c ts in
                                  Rewrite (p, t1, t2, c), l, ts
  in
  let c, l, ts = fill c ts in
  assert (ts = []);
  l, c

let rec nocuts = function
  | Skip -> false
  | Axiom _ -> true
  | Split (c1, c2) -> nocuts c1 && nocuts c2
  | Dir (_, c)
  | Intro (_, c)
  | Rewrite (_, _, _, c) -> nocuts c

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
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption" in
  let _, t' = task_separate_goal t in
  try let h = assumption_ctxt g t' in
      [], Axiom h
  with Not_found -> [t], Skip

(* Split with certificate *)
let split t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split" in
  let _, c = task_separate_goal t in
  let splitted = match g.t_node with
    | Tbinop (Tand, f1, f2) -> Some (f1, f2)
    | Tbinop (Tiff, f1, f2) ->
        let direct = t_implies f1 f2 in
        let indirect = t_implies f2 f1 in
        Some (direct, indirect)
    | _ -> None in
  match splitted with
    | Some (f1, f2) ->
        let tf1 = add_decl c (create_prop_decl Pgoal pr f1) in
        let tf2 = add_decl c (create_prop_decl Pgoal pr f2) in
        [tf1;tf2], Split (Skip, Skip)
    | None -> [t], Skip

(* Intro with certificate *)
let intro t =
  let i = Decl.create_prsymbol (Ident.id_fresh "i") in
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split" in
  let _, c = task_separate_goal t in
  match g.t_node with
  | Tbinop (Timplies, f1, f2) ->
      let decl1 = create_prop_decl Paxiom i f1 in
      let tf1 = add_decl c decl1 in
      let tf2 = add_decl tf1 (create_prop_decl Pgoal pr f2) in
      [tf2], Intro (i.pr_name, Skip)
  | _ -> [t], Skip

(* Direction with certificate *)
let dir d t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.dir" in
  let _, c = task_separate_goal t in
  match g.t_node, d with
  | Tbinop (Tor, f, _), Left | Tbinop (Tor, _, f), Right ->
      let tf = add_decl c (create_prop_decl Pgoal pr f) in
      [tf], Dir (d, Skip)
  | _ -> [t], Skip

let rec replace_in_term tl tr t : (term * path) option =
  if t_equal tl t
  then Some (tr, [])
  else match t.t_node with
       | Tbinop (op, t1, t2) ->
           begin match replace_in_term tl tr t1 with
           | Some (nt1, p) -> Some (t_binary op nt1 t2, Left::p)
           | None -> match replace_in_term tl tr t2 with
                     | Some (nt2, p) -> Some (t_binary op t1 nt2, Right::p)
                     | None -> None end
       | _ -> None

let rewrite (h : prsymbol) task =
  let prg, termg = try task_goal task, task_goal_fmla task
                   with GoalNotFound -> invalid_arg "Cert_syntax.dir" in
  let _, task_no_g = task_separate_goal task in
  let rew_terms =
    List.fold_left (fun acc d ->
        match d.d_node with
        | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
            (match t.t_node with
             | Tbinop (Tiff, t1, t2) -> Some (t1, t2)
             | _ -> raise Not_found)
        | _ -> acc) None (task_decls task) in
  match rew_terms with
  | Some (tl, tr) ->
      begin match replace_in_term tl tr termg with
      | Some (ntg, p) ->
          let task_new_g = add_decl task_no_g (create_prop_decl Pgoal prg ntg) in
          let ctl, ctr = translate_term tl, translate_term tr in
          [task_new_g], Rewrite (p, ctl, ctr, Skip)
      | _ -> [task], Skip end
  | _ -> raise Not_found


(** Transformials *)

(* Compose transformations with certificate *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

(* If Then Else on transformations with certificate *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  let ((lt, cert) as tri_task) = tri task in
  if not (Lists.equal task_equal lt [task] && cert = Skip)
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
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task


(** Derived transformations with certificate *)

let split_assumption = compose split assumption

let rec intuition task =
  repeat (compose assumption
            (compose intro
               (compose split
                  (try_close [ite (dir Left) intuition id;
                              ite (dir Right) intuition id])))) task


(** Certified transformations *)

let assumption_trans = checker_ctrans assumption
let split_trans = checker_ctrans split
let intro_trans = checker_ctrans intro
let left_trans = checker_ctrans (dir Left)
let right_trans = checker_ctrans (dir Right)
let rewrite_trans pr = checker_ctrans (rewrite pr)

let split_assumption_trans = checker_ctrans split_assumption
let intuition_trans = checker_ctrans intuition

let () =
  Trans.register_transform_l "assumption_cert" (Trans.store assumption_trans)
    ~desc:"A certified version of coq tactic [assumption]";
  Trans.register_transform_l "split_cert" (Trans.store split_trans)
    ~desc:"A certified version of (simplified) coq tactic [split]";
  Trans.register_transform_l "split_assumption_cert" (Trans.store split_assumption_trans)
    ~desc:"A certified version of (simplified) coq tactic [split; assumption]";
  Trans.register_transform_l "intro_cert" (Trans.store intro_trans)
    ~desc:"A certified version of (simplified) coq tactic [intro]";
  Trans.register_transform_l "left_cert" (Trans.store left_trans)
    ~desc:"A certified version of coq tactic [left]";
  Args_wrapper.(wrap_and_register ~desc:"A certified version of transformation rewrite"
                                  "rewrite_cert"
                                  (Tprsymbol Ttrans_l)
                                  (fun pr -> Trans.store (rewrite_trans pr)))


let () =
  Trans.register_transform_l "right_cert" (Trans.store right_trans)
    ~desc:"A certified version of coq tactic [right]";
  Trans.register_transform_l "intuition_cert" (Trans.store intuition_trans)
    ~desc:"A certified version of (simplified) coq tactic [intuition]"
