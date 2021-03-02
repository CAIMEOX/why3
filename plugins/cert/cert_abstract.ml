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
let ctint = CTyapp (ts_int, [])

let interp_type =
  let name ts = ts.ts_name in
  let l = List.map name [ts_int; ts_real; ts_str] in
  Sid.of_list l

let interp_var =
  let l = [ id_true, ctbool;
            id_false, ctbool;
            id_eq, CTarrow (ctint, CTarrow (ctint, CTprop))
          ] in
  Mid.of_list l

(** Utility functions on ctask *)

let find_ident s h cta =
  match Mid.find_opt h cta.gamma_delta with
  | Some x -> x
  | None ->
      let s = asprintf "%s : Can't find ident %a in the task" s prhyp h in
      verif_failed s

let ctask_empty =
  { types = Sid.empty;
    sigma = Mid.empty;
    gamma_delta = Mid.empty }

let ctask_union ct1 ct2 =
  { types = Sid.union ct1.types ct2.types;
    sigma = Mid.set_union ct1.sigma ct2.sigma;
    gamma_delta = Mid.set_union ct1.gamma_delta ct2.gamma_delta }

let lift_mid_cta f cta =
  { types = cta.types;
    sigma = cta.sigma;
    gamma_delta = f (cta.gamma_delta) }

(* Make sure to not add interpreted types to the abstract types *)
let add_type i cta =
  { types = if Sid.mem i interp_type
            then cta.types
            else Sid.add i cta.types;
    sigma = cta.sigma;
    gamma_delta = cta.gamma_delta }

(* Make sure to not add interpreted variables to the signature *)
let add_var i cty cta =
  { types = cta.types;
    sigma = if Mid.mem i interp_var
            then cta.sigma
            else Mid.add i cty cta.sigma;
    gamma_delta = cta.gamma_delta }

let remove i cta = lift_mid_cta (Mid.remove i) cta

let add i ct cta = lift_mid_cta (Mid.add i ct) cta

let ctask_equal cta1 cta2 =
  Mid.equal cty_equal cta1.sigma cta2.sigma &&
  let cterm_pos_equal (t1, p1) (t2, p2) =
    ct_equal t1 t2 && p1 = p2 in
  Mid.equal cterm_pos_equal cta1.gamma_delta cta2.gamma_delta

(* Typing algorithm *)

let infer_type cta t =
  let rec infer_type sigma t = match t with
  | CTfvar v -> Mid.find v sigma
  | CTbvar _ -> assert false
  | CTtrue | CTfalse -> CTprop
  | CTnot t -> let ty = infer_type sigma t in
               assert (cty_equal ty CTprop);
               CTprop
  | CTquant (_, ty1, t) ->
      let ni = id_register (id_fresh "type_ident") in
      let sigma = Mid.add ni ty1 sigma in
      let t = ct_open t (CTfvar ni) in
      let ty2 = infer_type sigma t in
      CTarrow (ty1, ty2)
  | CTapp (t1, t2) ->
      begin match infer_type sigma t1, infer_type sigma t2 with
      | CTarrow (ty1, ty2), ty3 when cty_equal ty1 ty3 -> ty2
      | _ -> assert false end
  | CTbinop (_, t1, t2) ->
      let ty1, ty2 = infer_type sigma t1, infer_type sigma t2 in
      assert (cty_equal ty1 CTprop);
      assert (cty_equal ty2 CTprop);
      CTprop
  | CTint _ -> ctint in
  let sigma_interp = Mid.set_union cta.sigma interp_var in
  infer_type sigma_interp t


let infers_into cta t ty =
  try assert (cty_equal (infer_type cta t) ty)
  with e -> eprintf "wrong type for %a@." pcte t;
            raise e


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

let abstract_task task =
  abstract_task_acc ctask_empty task
