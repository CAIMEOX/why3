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


(* traducteur des taches *)
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

(* checker de certificats *)
let check_step {cctxt = c; cgoal = t} (s : step) =
  match s with
    | Axiom id -> begin match List.assoc_opt id c with
                  | Some t' when t = t' -> Some []
                  | _ -> None end

(* transformation assumption *)
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

let assumption_task (t : task) : task list * step =
  let g = try task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption_task" in
  let _, t = task_separate_goal t in
  [], Axiom (assumption_ctxt g t)

let assumption_cert t =
  try let l, cert = assumption_task t in
      let t' = translate_task t in
      match check_step t' cert with
        | Some l' when l' = List.map translate_task l -> l
        | _ -> failwith "certif verification failed"
  with e -> raise (Trans.TransFailure ("test_cert", e))

let () =
  Trans.register_transform_l "assumption_cert" (Trans.store assumption_cert)
    ~desc:"test certificates"
