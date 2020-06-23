open Why3
open Term
open Ident
open Theory
open Decl
open Task


(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cquant = CTforall | CTexists | CTlambda

type cterm =
  { ct_node : cterm_node;
    ct_ty : Ty.ty option }

and cterm_node =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTint of BigInt.t
  | CTapp of cterm * cterm
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of cquant * cterm (* quantifier binding *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

type ctask = (cterm * bool) Mid.t
(* We will denote a ctask <M> by <Γ ⊢ Δ> where :
   • <Γ> contains all the declarations <H : P> where <H> is mapped to <(P, false)> in <M>
   • <Δ> contains all the declarations <H : P> where <H> is mapped to <(P, true)> in <M>
*)


(** Abstracting a Why3 <task> into a <ctask> : extract only the logical core *)

let abstract_quant = function
  | Tforall -> CTforall
  | Texists -> CTexists

let rec abstract_term { t_node = t; t_ty = ty } =
  { ct_node = abstract_term_node ty t;
    ct_ty = ty }

and abstract_term_node_rec ty bv_lvl lvl t =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  let term_from_id id = match Mid.find_opt id bv_lvl with
        | None -> CTfvar id
        | Some lvl_id ->
            (* a variable should not be above its definition *)
            assert (lvl_id <= lvl);
            CTbvar (lvl - lvl_id) in
  match t with
  | Tvar v ->
      term_from_id v.vs_name
  | Tapp (ls, lt) ->
      let vs = term_from_id ls.ls_name in
      let open Ty in
      let app_ty ty1 ty2 =
        match ty1.ty_node with
        | Tyvar v -> ty1 (* ty_app v [ty2] *)
        | Tyapp (v, l1) -> ty_app v (ty2::l1) in
      let app t1 t2 =
        let ty = match t1.ct_ty, t2.ct_ty with
          | Some ty1, Some ty2 -> Some (app_ty ty1 ty2)
          | _ -> None in
        { ct_node = CTapp (t1, t2);
          ct_ty = ty } in
      List.fold_left
        (fun acc t -> app acc (abstract_term_node_rec bv_lvl lvl t))
        vs lt
  | Tbinop (op, t1, t2) ->
      let ct1 = abstract_term_node_rec bv_lvl lvl t1 in
      let ct2 = abstract_term_node_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let lvs, _, t = t_open_quant tq in
      let lvl_ids = List.mapi (fun i vs -> lvl + i + 1, vs.vs_name) lvs in
      let bv_lvl = List.fold_left (fun m (lvl, ids) -> Mid.add ids lvl m) bv_lvl lvl_ids in
      let lvl = lvl + List.length lvs in
      let ctq = abstract_term_node_rec bv_lvl lvl t in
      let q = abstract_quant q in
      List.fold_right (fun _ t -> CTquant (q, t)) lvs ctq
  | Tnot t -> CTnot (abstract_term_node_rec bv_lvl lvl t)
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | Tconst (Constant.ConstInt i) -> CTint i.Number.il_int
  | Tconst _ ->
      let open Format in
      Pretty.print_term str_formatter t;
      let s = flush_str_formatter () in
      invalid_arg ("Cert_abstract.abstract_term Tconst : " ^ s)
  | Tif _ -> invalid_arg "Cert_abstract.abstract_term Tif"
  | Tlet _ -> invalid_arg "Cert_abstract.abstract_term Tlet"
  | Tcase _ -> invalid_arg "Cert_abstract.abstract_term Tcase"
  | Teps _ -> invalid_arg "Cert_abstract.abstract_term Teps"

and abstract_term_node ty t =
  abstract_term_node_rec ty Mid.empty 0 t

let abstract_decl decl =
  match decl.d_node with
  | Dprop (Pgoal, pr, t) ->
       Mid.singleton pr.pr_name (abstract_term t, true)
  | Dprop (_, pr, t) ->
      Mid.singleton pr.pr_name (abstract_term t, false)
  | _ -> Mid.empty

let abstract_tdecl td =
  match td.td_node with
  | Decl decl -> abstract_decl decl
  | _ -> Mid.empty

let rec abstract_task_acc acc = function
  | Some {task_decl = td; task_prev = task} ->
      let new_acc = Mid.set_union acc (abstract_tdecl td) in
      abstract_task_acc new_acc task
  | None -> acc

let abstract_task task =
  abstract_task_acc Mid.empty task

(** We equip existing transformations with a certificate <certif> *)

type 'certif ctransformation = (task list * 'certif) Trans.trans

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)


(** Create a certified transformation from a transformation with a certificate *)

let checker_ctrans
      (debug : ('certif -> unit) option)
      (make_core : ctask -> ctask list -> 'certif -> 'core_certif)
      (checker : 'core_certif -> ctask -> ctask list -> unit)
      (ctr : 'certif ctransformation)
      (init_t : task) =
  let res_t, certif = Trans.apply ctr init_t in
  Opt.iter (fun print -> print certif) debug;
  let init_ct = abstract_task init_t in
  let res_ct = List.map abstract_task res_t in
  let core_certif = make_core init_ct res_ct certif in
  checker core_certif init_ct res_ct;
  res_t
