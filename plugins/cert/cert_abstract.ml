open Why3
open Term
open Ident
open Theory
open Decl
open Task
open Ty
open Format

(** Utility **)
let print_list pre = pp_print_list ~pp_sep:pp_print_space pre

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol
  | CTyapp of tysymbol * ctype list
  | CTarrow of ctype * ctype

let ts_prop = create_tysymbol (id_fresh "prop") [] NoDef
let ctprop = CTyapp (ts_prop, [])
let ctbool = CTyapp (ts_bool, [])
let ctint = CTyapp (ts_int, [])

(** Utility functions on ctype *)

let rec cty_equal l1 l2 = match l1, l2 with
  | CTyvar v1, CTyvar v2 -> Ty.tv_equal v1 v2
  | CTyapp (ty1, l1), CTyapp (ty2, l2) ->
      ts_equal ty1 ty2 && List.for_all2 cty_equal l1 l2
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      cty_equal f1 f2 && cty_equal a1 a2
  | (CTyvar _ | CTyapp _ | CTarrow _), _ -> false

(* Pretty printing of ctype (compatible with lambdapi) *)

let san =
  let lower_h c = if c = 'H' then "h" else char_to_alnum c in
  sanitizer lower_h char_to_alnum

let hsan s = "H" ^ san s

let ip = create_ident_printer ~sanitizer:san []
let hip = create_ident_printer ~sanitizer:hsan []

let prid fmt i = fprintf fmt "%s" (id_unique ip i)

let prhyp fmt i = fprintf fmt "%s" (id_unique hip i)

let prpr fmt pr = prhyp fmt pr.pr_name

let rec prty fmt ty = match ty with
  | CTyapp (ts, l) when l <> [] ->
      fprintf fmt "@[<2>%a@ %a@]"
        prts ts
        (print_list prtyparen) l
  | CTarrow (t1, t2) ->
      fprintf fmt "@[%a ⇒@ %a@]"
        prtyparen t1
        prty t2
  | _ -> prtyparen fmt ty

and prtyparen fmt = function
  | CTyvar _ -> fprintf fmt "Nat"
  (* TODO handle polymorphic symbols *)
  (* Pretty.print_tv fmt v *)
  | CTyapp (ts, []) -> prts fmt ts
  | cty -> fprintf fmt "(%a)" prty cty

and prts fmt ts =
  if ts_equal ts ts_bool then fprintf fmt "Bool"
  else if ts_equal ts ts_int then fprintf fmt "Nat"
  else if ts_equal ts ts_prop then fprintf fmt "Prop"
  else Pretty.print_ts fmt ts



type cterm =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTint of BigInt.t
  | CTapp of cterm * cterm (* binary application *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of cquant * ctype * cterm (* quantifier binding *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

let id_eq = ps_equ.ls_name
let eq = CTfvar id_eq
let id_true = fs_bool_true.ls_name
let id_false = fs_bool_false.ls_name

let interp_type =
  let name ts = ts.ts_name in
  let l = List.map name [ts_int; ts_real; ts_str] in
  Sid.of_list l

let interp_var =
  let l = [ id_true, ctbool;
            id_false, ctbool;
            id_eq, CTarrow (ctint, CTarrow (ctint, ctprop))
          ] in
  Mid.of_list l


(** Utility functions on cterm *)

let ct_map f ct = match ct with
  | CTbvar _ | CTfvar _ | CTint _ | CTtrue | CTfalse -> ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, f ct)
  | CTapp (ct1, ct2) -> CTapp (f ct1, f ct2)
  | CTbinop (op, ct1, ct2) ->  CTbinop (op, f ct1, f ct2)
  | CTnot ct -> CTnot (f ct)

let rec ct_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      ct_equal tl1 tl2 && ct_equal tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && ct_equal tl1 tl2 && ct_equal tr1 tr2
  | CTquant (q1, ty1, t1), CTquant (q2, ty2, t2) when q1 = q2 ->
      cty_equal ty1 ty2 && ct_equal t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> ct_equal t1 t2
  | CTint i1, CTint i2 -> BigInt.eq i1 i2
  | (CTbvar _ | CTfvar _ | CTapp _ | CTbinop _ | CTquant _
     | CTtrue | CTfalse | CTnot _ | CTint _), _ -> false

(* Bound variable substitution *)
let rec ct_bv_subst k u ctn = match ctn with
  | CTbvar i -> if i = k then u else ctn
  | CTint _ | CTfvar _ -> ctn
  | CTapp (ct1, ct2) ->
      let nt1 = ct_bv_subst k u ct1 in
      let nt2 = ct_bv_subst k u ct2 in
      CTapp (nt1, nt2)
  | CTbinop (op, ct1, ct2) ->
      let nt1 = ct_bv_subst k u ct1 in
      let nt2 = ct_bv_subst k u ct2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, cty, ct) ->
      let nct = ct_bv_subst (k+1) u ct in
      CTquant (q, cty, nct)
  | CTnot ct -> CTnot (ct_bv_subst k u ct)
  | CTtrue -> CTtrue
  | CTfalse -> CTfalse

let ct_open t u = ct_bv_subst 0 u t

(* Checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let rec term ct = match ct with
    | CTbvar _ -> false
    | CTapp (ct1, ct2)
    | CTbinop (_, ct1, ct2) -> term ct1 && term ct2
    | CTquant (_, _, t) -> term (ct_open t (CTfvar di))
    | CTnot ct -> term ct
    | CTint _ | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* Free variable substitution *)
let rec ct_fv_subst z u ctn = match ctn with
  | CTfvar x -> if id_equal z x then u else ctn
  | CTapp (ct1, ct2) ->
      let nt1 = ct_fv_subst z u ct1 in
      let nt2 = ct_fv_subst z u ct2 in
      CTapp (nt1, nt2)
  | CTbinop (op, ct1, ct2) ->
      let nt1 = ct_fv_subst z u ct1 in
      let nt2 = ct_fv_subst z u ct2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, cty, ct) ->
      let nct = ct_fv_subst z u ct in
      CTquant (q, cty, nct)
  | CTnot ct -> CTnot (ct_fv_subst z u ct)
  | CTint _ | CTbvar _ | CTtrue | CTfalse -> ctn

let ct_subst (m : cterm Mid.t) ct =
  Mid.fold ct_fv_subst m ct

(* Variable closing *)
let rec ct_fv_close x k ct = match ct with
  | CTint _ | CTbvar _ | CTtrue | CTfalse-> ct
  | CTfvar y -> if id_equal x y then CTbvar k else ct
  | CTnot ct -> CTnot (ct_fv_close x k ct)
  | CTapp (ct1, ct2) ->
      let nt1 = ct_fv_close x k ct1 in
      let nt2 = ct_fv_close x k ct2 in
      CTapp (nt1, nt2)
  | CTbinop (op, ct1, ct2) ->
      let nt1 = ct_fv_close x k ct1 in
      let nt2 = ct_fv_close x k ct2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, cty, ct) -> CTquant (q, cty, ct_fv_close x (k+1) ct)

let ct_close x t = ct_fv_close x 0 t

(* Find free variable with respect to a term *)
let rec mem_cont x ctn cont = match ctn with
  | CTfvar y -> cont (id_equal x y)
  | CTapp (ct1, ct2)
  | CTbinop (_, ct1, ct2) ->
      mem_cont x ct1 (fun m1 ->
      mem_cont x ct2 (fun m2 ->
          cont (m1 || m2)))
  | CTquant (_, _, ct)
  | CTnot ct -> mem_cont x ct cont
  | CTint _ | CTbvar _ | CTtrue | CTfalse -> cont false

let mem x t = mem_cont x t (fun x -> x)

(* Pretty printing of terms (compatible with lambdapi) *)

let rec pcte fmt = function
  | CTquant (CTlambda, _, t) ->
      let x = id_register (id_fresh "x") in
      let t_open = ct_open t (CTfvar x) in
      fprintf fmt "λ %a, %a"
        prid x
        pcte t_open;
      forget_id ip x
  | ct -> prarr fmt ct

and prarr fmt = function
  | CTbinop (Timplies, ct1, ct2) ->
      fprintf fmt "%a ⇨ %a"
        prdisj ct1
        prarr ct2
  | CTbinop (Tiff, ct1, ct2) ->
      fprintf fmt "%a ⇔ %a"
        prdisj ct1
        prarr ct2
  | ct -> prdisj fmt ct

and prdisj fmt = function
  | CTbinop (Tor, ct1, ct2) ->
      fprintf fmt "%a ∨ %a"
        prconj ct1
        prdisj ct2
  | ct -> prconj fmt ct

and prconj fmt = function
  | CTbinop (Tand, ct1, ct2) ->
      fprintf fmt "%a ∧ %a"
        prnot ct1
        prconj ct2
  | ct -> prnot fmt ct

and prnot fmt = function
  | CTnot ct ->
      fprintf fmt "¬ %a"
        prpv ct
  | ct -> prapp fmt ct

and prapp fmt = function
  | CTapp (ct1, ct2) ->
      fprintf fmt "%a %a"
        prapp ct1
        prpv ct2
  | CTquant (q, ty, t) when q <> CTlambda ->
      let x = id_register (id_fresh "x") in
      let q_str = match q with CTforall -> "∀"
                             | CTexists -> "∃"
                             | CTlambda -> assert false in
      let t_open = ct_open t (CTfvar x) in
      fprintf fmt "%s %a (λ %a, %a)"
        q_str
        prty ty
        prid x
        pcte t_open;
      forget_id ip x
  | ct -> prpv fmt ct

and prpv fmt = function
  | CTbvar n -> pp_print_int fmt n
  | CTfvar id -> prid fmt id
  | CTint i -> pp_print_string fmt (BigInt.to_string i)
  | CTfalse -> fprintf fmt "false"
  | CTtrue -> fprintf fmt "true"
  | ct -> fprintf fmt "(%a)" pcte ct

type ctask =
  { types : Sid.t;
    sigma : ctype Mid.t;
    gamma_delta : (cterm * bool) Mid.t
  }
(* We will denote a ctask <sigma; gamma_delta> by <Σ | Γ ⊢ Δ> where:
   • <Σ> contains all the signature declarations <x : ty>
     where <x> is mapped to <ty> in <sigma>
   • <Γ> contains all the declarations <H : P>
     where <H> is mapped to <(P, false)> in <gamma_delta>
   • <Δ> contains all the declarations <H : P>
     where <H> is mapped to <(P,  true)> in <gamma_delta>

   We sometimes omit signature (when it's not confusing) and write <Γ ⊢ Δ>
*)

(* Typing algorithm *)

let infer_type cta t =
  let rec infer_type sigma t = match t with
  | CTfvar v -> Mid.find v sigma
  | CTbvar _ -> assert false
  | CTtrue | CTfalse -> ctprop
  | CTnot t -> let ty = infer_type sigma t in
               assert (cty_equal ty ctprop);
               ctprop
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
      assert (cty_equal ty1 ctprop);
      assert (cty_equal ty2 ctprop);
      ctprop
  | CTint _ -> ctint in
  let sigma_interp = Mid.set_union cta.sigma interp_var in
  infer_type sigma_interp t


let infers_into cta t ty =
  try assert (cty_equal (infer_type cta t) ty)
  with e -> eprintf "wrong type for %a@." pcte t;
            raise e


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

(* Pretty printing of ctask *)

let po p fmt = function
  | None -> fprintf fmt "None"
  | Some x -> fprintf fmt "%a" p x

let prs fmt mid =
  Mid.iter (fun x ty -> fprintf fmt "%a : %a\n" prid x prty ty) mid

let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prgd fmt mid =
  Mid.iter (fun h (cte, pos) -> fprintf fmt "%a%a : %a\n" prpos pos prhyp h pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n%a\n" prs cta.sigma prgd cta.gamma_delta

let plcta =
  pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "========\n") pcta

let eplcta cta lcta =
  eprintf "INIT :\n%a==========\nRES :\n%a\n@." pcta cta plcta lcta

let print_ctasks filename lcta =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  plcta fmt lcta;
  close_out oc

(** Abstracting a Why3 <task> into a <ctask> : extract only the logical core *)

let abstract_quant = function
  | Tforall -> CTforall
  | Texists -> CTexists

let rec abstract_otype = function
  | None -> ctprop
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



(** We equip existing transformations with a certificate <certif> *)

type 'certif ctransformation = (task list * 'certif) Trans.trans

(** Create a certified transformation from a transformation with a certificate *)

type 'certif debug =
  ('certif -> unit) option *
  (ctask -> ctask list -> unit) option

let checker_ctrans
      (debug : 'certif debug )
      (make_core : ctask -> ctask list -> 'certif -> 'core_certif)
      (checker : 'core_certif -> ctask -> ctask list -> unit)
      (ctr : 'certif ctransformation)
      (init_t : task) =
  let dbg_cert, dbg_cta = debug in
  let res_t, certif = Trans.apply ctr init_t in
  Opt.iter (fun eprcertif -> eprcertif certif) dbg_cert;
  let init_ct = abstract_task init_t in
  let res_ct = List.map abstract_task res_t in
  Opt.iter (fun eplcta -> eplcta init_ct res_ct) dbg_cta;
  let core_certif = make_core init_ct res_ct certif in
  checker core_certif init_ct res_ct;
  res_t
