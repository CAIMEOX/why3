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
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
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

let rec abstract_term_rec bv_lvl lvl t =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  match t.t_node with
  | Tvar v ->
      let ids = v.vs_name in
      begin match Mid.find_opt ids bv_lvl with
        | None -> CTfvar ids
        | Some lvl_s ->
            assert (lvl_s <= lvl); (* a variable should not be above its definition *)
            CTbvar (lvl - lvl_s)
      end
  | Tapp (ls, lt) ->
      let ids = ls.ls_name in
      let vs = match Mid.find_opt ids bv_lvl with
        | None -> CTfvar ids
        | Some lvl_s ->
            assert (lvl_s <= lvl); (* a variable should not be above its definition *)
            CTbvar (lvl - lvl_s) in
      List.fold_left (fun acc t -> CTapp (acc, abstract_term_rec bv_lvl lvl t))
        vs lt
  | Tbinop (op, t1, t2) ->
      let ct1 = abstract_term_rec bv_lvl lvl t1 in
      let ct2 = abstract_term_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let vs, _, t = t_open_quant tq in
      assert (List.length vs = 1);
      let ids = (List.hd vs).vs_name in
      let lvl = lvl + 1 in
      let ctq = abstract_term_rec (Mid.add ids lvl bv_lvl) lvl t in
      CTquant (abstract_quant q, ctq)
  | Tnot t -> CTnot (abstract_term_rec bv_lvl lvl t)
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | Tconst _ -> invalid_arg "Cert_abstract.abstract_term Tconst"
  | Tif _ -> invalid_arg "Cert_abstract.abstract_term Tif"
  | Tlet _ -> invalid_arg "Cert_abstract.abstract_term Tlet"
  | Tcase _ -> invalid_arg "Cert_abstract.abstract_term Tcase"
  | Teps _ -> invalid_arg "Cert_abstract.abstract_term Teps"

let abstract_term t =
  abstract_term_rec Mid.empty 0 t

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
      (make_core : ctask -> ctask list -> 'certif -> 'core_certif)
      (checker : 'core_certif -> ctask -> ctask list -> unit)
      (ctr : 'certif ctransformation)
      (init_t : task) =
  let res_t, certif = Trans.apply ctr init_t in
  let init_ct = abstract_task init_t in
  let res_ct = List.map abstract_task res_t in
  let core_certif = make_core init_ct res_ct certif in
  checker core_certif init_ct res_ct;
  res_t
