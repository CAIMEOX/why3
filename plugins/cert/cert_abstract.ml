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

let abstract_quant = function
  | Tforall -> CTforall
  | Texists -> CTexists

let rec abstract_type { ty_node } =
  match ty_node with
  | Tyvar v -> CTyvar v
  | Tyapp (ts, lts) ->
      if ts_equal ts ts_func
      then let l1, l2 = match lts with
             | [l1; l2] -> l1, l2
             | _ -> assert false in
           CTarrow (abstract_type l1, abstract_type l2)
      else CTyapp (ts, List.map abstract_type lts)

let abstract_otype = function
  | None -> CTprop
  | Some ty -> abstract_type ty

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
      let s = asprintf "Does not handle Tconst yet : %a"
                Pretty.print_term t in
      invalid_arg s
  | Tif _ -> invalid_arg "Does not handle Tif yet"
  | Tlet _ -> invalid_arg "Does not handle Tlet yet"
  | Tcase _ -> invalid_arg "Does not handle Tcase yet"
  | Teps _ -> invalid_arg "Does not handle Teps yet"

let abstract_decl_acc acc decl =
  match decl.d_node with
  | Dtype tys ->
      add_type tys.ts_name acc
  | Dprop (k, pr, t) ->
      let ct = abstract_term t in
      add pr.pr_name (ct, k = Pgoal) acc
  | Dparam ls ->
      let cty = type_lsymbol ls in
      add_var ls.ls_name cty acc
  | Dlogic l ->
      List.fold_left (fun cta (ls, ax) ->
          let cty = type_lsymbol ls in
          let ct = abstract_term (ls_defn_axiom ax) in
          add_var ls.ls_name cty cta
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

(** The interpreted symbols are saved as part of the task *)

let types_sigma_interp env =
  let interp_type = ref [] in
  let interp_var = ref [] in
  let str_id = ref [] in

  let _ =
    let add ts = interp_type := ts.ts_name :: !interp_type in
    List.iter add [ts_int; ts_real; ts_bool] in

  let _ =
    let add (id, cty) = interp_var := (id, cty) :: !interp_var in
    List.iter add [ id_true, ctbool;
                    id_false, ctbool;
                    id_eq, CTarrow (ctint, CTarrow (ctint, CTprop))];

    try let env = Opt.get env in
        let th_int = Env.read_theory env ["int"] "Int" in
        let le = ns_find_ls th_int.th_export [le_str] in
        let ge = ns_find_ls th_int.th_export [ge_str] in
        let lt = ns_find_ls th_int.th_export [lt_str] in
        let gt = ns_find_ls th_int.th_export [gt_str] in
        let pl = ns_find_ls th_int.th_export [pl_str] in
        let mn = ns_find_ls th_int.th_export [mn_str] in

        let add (str, id, cty) = add (id, cty);
                                 str_id := [str, id] in
        List.iter add
          [le_str, le.ls_name, type_lsymbol le;
           ge_str, ge.ls_name, type_lsymbol ge;
           lt_str, lt.ls_name, type_lsymbol lt;
           gt_str, gt.ls_name, type_lsymbol gt;
           pl_str, pl.ls_name, type_lsymbol pl;
           mn_str, mn.ls_name, type_lsymbol mn;
          ]
    with _ -> () in

  let interp_type = Sid.of_list !interp_type in
  let interp_var = Mid.of_list !interp_var in
  let get_ident =
    let open Wstdlib in let open Mstr in
    let tbl = of_list !str_id in
    fun str -> find str tbl in
  get_ident, interp_type, interp_var

let abstract_task env =
  let get_ident, types_interp, sigma_interp = types_sigma_interp env  in
  fun task ->
  abstract_task_acc (ctask_new get_ident types_interp sigma_interp) task
