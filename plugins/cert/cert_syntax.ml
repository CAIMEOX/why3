open Why3
open Term
open Decl
open Theory
open Task

type ident = Ident.ident
type cterm = CTapp of ident
type ctask = { cctxt : (ident * cterm) list; cgoal : cterm }
type step = Axiom of ident
type certif = step list


(* Translating Why3 tasks to simplified certificate tasks *)
let translate_term (t : term) : cterm =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
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

(* Checker *)
let check_step {cctxt = c; cgoal = t} (s : step) =
  match s with
    | Axiom id -> begin match List.assoc_opt id c with
                  | Some t' when t = t' -> Some []
                  | _ -> None end

(* Creates a certified tactic from a tactic that produces certificates *)
let checked_tactic tac task =
  try let ltask, step = tac task in
      let ctask = translate_task task in
      match check_step ctask step with
      | Some lctask when lctask = List.map translate_task ltask -> ltask
      | _ -> failwith "Certif verification failed."
  with e -> raise (Trans.TransFailure ("test_cert", e))

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
  | None -> raise (Generic_arg_trans_utils.Arg_trans "No such assumption.")

let assumption_step (t : task) : task list * step =
  let g = try task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption_task" in
  let _, t = task_separate_goal t in
  let h = assumption_ctxt g t in
  [], Axiom h


(* Certified tactic *)
let cert_assumption = checked_tactic assumption_step

let () =
  Trans.register_transform_l "cert_assumption" (Trans.store cert_assumption)
    ~desc:"test certificates"
