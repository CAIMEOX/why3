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

(* Translating Why3 tasks to simplified certificate tasks *)
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

(* check_certif replays the certificate on a ctask *)
exception Certif_verif_failed
let rec check_certif ({cctxt = c; cgoal = t} as ctask) (cert : certif)  : ctask list =
  match cert with
    | Skip -> [ctask]
    | Axiom id ->
        begin match List.assoc_opt id c with
        | Some t' when t = t' -> []
        | _ -> raise Certif_verif_failed end
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

let assumption_ctrans t =
  let g = try task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption_task" in
  let _, t' = task_separate_goal t in
  try let h = assumption_ctxt g t' in [], Axiom h
  with Not_found -> [t], Skip

(* Split with certificate *)
let split_ctrans t =
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
let dir_ctrans d t =
  let pr, g = try task_goal t, task_goal_fmla t
              with GoalNotFound -> invalid_arg "Cert_syntax.split_certif" in
  let _, c = task_separate_goal t in
  match g.t_node, d with
  | Tbinop (Tor, f, _), Left | Tbinop (Tor, _, f), Right ->
      let tf = add_decl c (create_prop_decl Pgoal pr f) in
      [tf], Dir (d, Skip)
  | _ -> [t], Skip

(* Compose transformations with certificate *)
let compose_ctrans (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  let ts, c = tr1 task in
  let rec fill c ts = match c with
      | Skip -> begin match ts with
                | [] -> assert false
                | t::ts -> let l2, c2 = tr2 t in
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

let split_assumption_ctrans = compose_ctrans split_ctrans assumption_ctrans

(* Certified transformations *)
let assumption_trans = checker_ctrans assumption_ctrans
let split_trans = checker_ctrans split_ctrans
let split_assumption_trans = checker_ctrans split_assumption_ctrans
let left_trans = checker_ctrans (dir_ctrans Left)
let right_trans = checker_ctrans (dir_ctrans Right)

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
    ~desc:"A certified version of coq tactic [right]"
