open Why3
open Term
open Ident
open Theory
open Decl
open Task
open Ty
open Format

open Cert_syntax

(** Abstracting a Why3 <task> into a <ctask> : extract only the logical core *)

module Abstract (E : Envm) = struct
  open E

  let abstract_quant = function
    | Tforall -> CTforall
    | Texists -> CTexists

  let rec abstract_otype = function
    | None -> CTprop
    | Some ty -> abstract_type ty

  and abstract_type { ty_node } =
    match ty_node with
    | Tyvar v -> CTyvar v
    | Tyapp (ts, lts) ->
        if ts_equal ts ts_func
        then let l1, l2 = match lts with
               | [l1; l2] -> l1, l2
               | _ -> assert false in
             CTarrow (abstract_type l1, abstract_type l2)
        else CTyapp (ts, List.map abstract_type lts)

  let type_lsymbol ls =
    List.fold_right (fun t acc -> CTarrow (abstract_type t, acc))
      ls.ls_args (abstract_otype ls.ls_value)

  let rec abstract_term t =
    abstract_term_rec Mid.empty 0 t

  and abstract_term_rec bv_lvl lvl t =
    let abstract = abstract_term_rec bv_lvl lvl in
    (* level <lvl> is the number of forall above in the whole term *)
    (* <bv_lvl> is mapping bound variables to their respective level *)
    let cterm_node_sig_from_id id  = match Mid.find_opt id bv_lvl with
      | None -> CTfvar id
      | Some lvl_id ->
          (* a variable should not be above its definition *)
          assert (lvl_id <= lvl);
          CTbvar (lvl - lvl_id) in
    match t.t_node with
    | Ttrue  -> CTtrue
    | Tfalse -> CTfalse
    | Tvar v -> cterm_node_sig_from_id v.vs_name
    | Tapp (ls, lt) ->
        let cts = cterm_node_sig_from_id ls.ls_name in
        let ctapp ct t = CTapp (ct, abstract t) in
        List.fold_left ctapp cts lt
    | Tbinop (op, t1, t2) ->
        let ct1 = abstract t1 in
        let ct2 = abstract t2 in
        CTbinop (op, ct1, ct2)
    | Tquant (q, tq) ->
        let lvs, _, t_open = t_open_quant tq in
        let ids_lvl = List.mapi (fun i vs -> vs.vs_name, lvl + i + 1) lvs in
        let bv_lvl = List.fold_left (fun m (ids, lvl) -> Mid.add ids lvl m)
                       bv_lvl ids_lvl in
        let lvl = lvl + List.length lvs in
        let ctn_open = abstract_term_rec bv_lvl lvl t_open in
        let q = abstract_quant q in
        let ctquant vs ct = let cty = abstract_type vs.vs_ty in
                            CTquant (q, cty, ct) in
        let ct_closed = List.fold_right ctquant lvs ctn_open in
        ct_closed
    | Tnot t -> CTnot (abstract t)
    | Tconst (Constant.ConstInt i) -> CTint i.Number.il_int
    | Tconst _ ->
        let s = asprintf "Cert_abstract.abstract_term Tconst : %a"
                  Pretty.print_term t in
        invalid_arg s
    | Tif _ -> invalid_arg "Cert_abstract.abstract_term Tif"
    | Tlet _ -> invalid_arg "Cert_abstract.abstract_term Tlet"
    | Tcase _ -> invalid_arg "Cert_abstract.abstract_term Tcase"
    | Teps _ -> invalid_arg "Cert_abstract.abstract_term Teps"

  let abstract_decl_acc acc decl =
    match decl.d_node with
    | Dtype tys ->
        add_type interp_type tys.ts_name acc
    | Dprop (k, pr, t) ->
        let ct = abstract_term t in
        add pr.pr_name (ct, k = Pgoal) acc
    | Dparam ls ->
        let cty = type_lsymbol ls in
        add_var interp_var ls.ls_name cty acc
    | Dlogic l ->
        List.fold_left (fun cta (ls, ax) ->
            let cty = type_lsymbol ls in
            let ct = abstract_term (ls_defn_axiom ax) in
            add_var interp_var ls.ls_name cty cta
            |> add ls.ls_name (ct, false))
          acc l
    | _ -> acc

  let abstract_tdecl_acc acc td =
    match td.td_node with
    | Decl decl -> abstract_decl_acc acc decl
    | _ -> acc

  let rec abstract_task_acc acc = function
    | Some {task_decl; task_prev} ->
        let new_acc = abstract_tdecl_acc acc task_decl in
        abstract_task_acc new_acc task_prev
    | None -> acc

  let abstract_task task =
    abstract_task_acc ctask_empty task
end
