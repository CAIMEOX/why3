open Why3
open Term
open Ident
open Theory
open Decl
open Task
open Ty
open Format

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol
  | CTyapp of tysymbol * ctype list
  | CTarrow of ctype * ctype

let ctbool = CTyapp (Ty.ts_bool, [])
let ctint = CTyapp (Ty.ts_int, [])

(** Utility functions on ctype *)

let rec ctype_equal_uncurr = function
  | CTyvar v1, CTyvar v2 -> Ty.tv_equal v1 v2
  | CTyapp (ty1, l1), CTyapp (ty2, l2) ->
      Ty.ts_equal ty1 ty2 && List.for_all ctype_equal_uncurr (List.combine l1 l2)
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      ctype_equal f1 f2 && ctype_equal a1 a2
  | (CTyvar _ | CTyapp _ | CTarrow _), _ -> false

and ctype_equal cty1 cty2 = ctype_equal_uncurr (cty1, cty2)

(* Pretty printing of ctype (compatible with lambdapi) *)

let ip = create_ident_printer []
let san = sanitizer char_to_alnum char_to_alnum

let pri fmt i =
  fprintf fmt "%s" (id_unique ip ~sanitizer:san i)

let prpr fmt pr =
  pri fmt pr.pr_name

let prle sep pre fmt le =
  let prl = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep) pre in
  fprintf fmt "[%a]" prl le

let rec prty fmt = function
  | CTyapp (ts, l)
      when not (Ty.ts_equal ts Ty.ts_bool || Ty.ts_equal ts Ty.ts_int ) ->
      fprintf fmt "%a %a"
        Pretty.print_ts ts
        (prle " " prtyparen) l
  | CTarrow (t1, t2) ->
      fprintf fmt "%a ⇒ %a"
        prtyparen t1
        prty t2
  | ty -> prtyparen fmt ty

and prtyparen fmt = function
  | CTyvar v -> prvar fmt v
  | CTyapp (ts, _) when Ty.ts_equal ts Ty.ts_bool -> fprintf fmt "dottype"
  | CTyapp (ts, _) when Ty.ts_equal ts Ty.ts_int -> fprintf fmt "Nat"
  | cty -> fprintf fmt "(%a)" prty cty

and prvar fmt _ =
  fprintf fmt "Nat"
  (* TODO include some types in lamdapi and translate to them *)
  (* for now we only have Nat *)
  (* Pretty.print_tv fmt v *)



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

let eq = CTfvar ps_equ.ls_name

(** Utility functions on cterm *)

let cterm_map f ct = match ct with
  | CTbvar _ | CTfvar _ | CTint _ | CTtrue | CTfalse -> ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, f ct)
  | CTapp (ct1, ct2) -> CTapp (f ct1, f ct2)
  | CTbinop (op, ct1, ct2) ->  CTbinop (op, f ct1, f ct2)
  | CTnot ct -> CTnot (f ct)

let rec cterm_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTquant (q1, ty1, t1), CTquant (q2, ty2, t2) when q1 = q2 ->
      ctype_equal ty1 ty2 && cterm_equal t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> cterm_equal t1 t2
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
        pri x
        pcte t_open
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
      fprintf fmt "(%s %a) (λ %a, %a)"
        q_str
        prty ty
        pri x
        pcte t_open
  | ct -> prpv fmt ct

and prpv fmt = function
  | CTbvar n -> pp_print_int fmt n
  | CTfvar id -> pri fmt id
  | CTint i -> pp_print_string fmt (BigInt.to_string i)
  | CTfalse -> fprintf fmt "false"
  | CTtrue -> fprintf fmt "true"
  | ct -> fprintf fmt "(%a)" pcte ct

(* Typing algorithm *)
let rec infer_type sigma t = match t with
  | CTfvar v -> Mid.find v sigma
  | CTbvar _ -> assert false
  | CTtrue | CTfalse -> ctbool
  | CTnot t -> let ty = infer_type sigma t in
               assert (ctype_equal ty ctbool);
               ctbool
  | CTquant (q, ty1, t) ->
      let ni = id_register (id_fresh "type_ident") in
      let sigma = Mid.add ni ty1 sigma in
      let t = ct_open t (CTfvar ni) in
      let ty2 = infer_type sigma t in
      begin match q with
      | CTlambda -> CTarrow (ty1, ty2)
      | _ ->  assert (ctype_equal ty2 ctbool); ctbool
      end
  | CTapp (t1, t2) ->
      begin match infer_type sigma t1, infer_type sigma t2 with
      | CTarrow (ty1, ty2), ty3 when ctype_equal ty1 ty3 -> ty2
      | _ -> assert false end
  | CTbinop (_, t1, t2) ->
      let ty1, ty2 = infer_type sigma t1, infer_type sigma t2 in
      assert (ctype_equal ty1 ctbool);
      assert (ctype_equal ty2 ctbool);
      ctbool
  | CTint _ -> ctint


let infers_into sigma t ty =
  try assert (ctype_equal (infer_type sigma t) ty)
  with _ -> let err_str = fprintf str_formatter "wrong type for %a" pcte t;
                          flush_str_formatter () in
            verif_failed err_str

type ctask =
  { sigma : ctype Mid.t;
    gamma_delta : (cterm * bool) Mid.t
  }
(* We will denote a ctask <sigma; gamma_delta> by <Σ | Γ ⊢ Δ> where:
   • <Σ> contains all the signature declarations <x : ty>
     where <x> is mapped to <ty> in <sigma>
   • <Γ> contains all the declarations <H : P>
     where <H> is mapped to <(P, false)> in <gamma_delta>
   • <Δ> contains all the declarations <H : P>
     where <H> is mapped to <(P,  true)> in <gamma_delta>
*)

(** Utility functions on ctask *)

let ctask_empty =
  { sigma = Mid.empty;
    gamma_delta = Mid.empty }

let ctask_union ct1 ct2 =
  { sigma = Mid.set_union ct1.sigma ct2.sigma;
    gamma_delta = Mid.set_union ct1.gamma_delta ct2.gamma_delta }

let lift_mid_cta f cta =
  { sigma = cta.sigma;
    gamma_delta = f (cta.gamma_delta) }

let add_var i cty cta =
  { sigma = Mid.add i cty cta.sigma;
    gamma_delta = cta.gamma_delta }

let remove i cta = lift_mid_cta (Mid.remove i) cta

let add i ct cta = lift_mid_cta (Mid.add i ct) cta

let ctask_equal cta1 cta2 =
  (* TODO fix finding the 'right' signature when abstracting a task *)
  (* Mid.equal ctype_equal cta1.sigma cta2.sigma && *)
  let cterm_pos_equal (t1, p1) (t2, p2) =
    cterm_equal t1 t2 && p1 = p2 in
  Mid.equal cterm_pos_equal cta1.gamma_delta cta2.gamma_delta

(* Pretty printing of ctask *)

let po p fmt = function
  | None -> fprintf fmt "None"
  | Some x -> fprintf fmt "%a" p x

let prs fmt mid =
  Mid.iter (fun x ty -> fprintf fmt "%a : %a\n" pri x prty ty) mid

let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prdg fmt mid =
  Mid.iter (fun h (cte, pos) -> fprintf fmt "%a%a : %a\n" prpos pos pri h pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n%a\n" prs cta.sigma prdg cta.gamma_delta

let plcta fmt lcta =
  fprintf fmt "%a" (prle "========\n" pcta) lcta

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
  | None -> ctbool
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
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  let cterm_node_sig_from_id id  = match Mid.find_opt id bv_lvl with
        | None ->
            CTfvar id
        | Some lvl_id ->
            (* a variable should not be above its definition *)
            assert (lvl_id <= lvl);
            CTbvar (lvl - lvl_id) in
  match t.t_node with
  | Ttrue  -> CTtrue
  | _ when t_equal t t_bool_true -> CTtrue
  | Tfalse -> CTfalse
  | _ when t_equal t t_bool_false -> CTfalse
  | Tvar v ->
      cterm_node_sig_from_id v.vs_name
  | Tapp (ls, lt) ->
      let ctls = cterm_node_sig_from_id ls.ls_name in
      List.fold_left (fun acc h -> CTapp (acc, abstract_term_rec bv_lvl lvl h))
        ctls lt
  | Tbinop (op, t1, t2) ->
      let ct1 = abstract_term_rec bv_lvl lvl t1 in
      let ct2 = abstract_term_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let lvs, _, t_open = t_open_quant tq in
      let lvl_ids = List.mapi (fun i vs -> lvl + i + 1, vs.vs_name) lvs in
      let bv_lvl = List.fold_left (fun m (lvl, ids) -> Mid.add ids lvl m) bv_lvl lvl_ids in
      let lvl = lvl + List.length lvs in
      let ctn_open = abstract_term_rec bv_lvl lvl t_open in
      let q = abstract_quant q in
      let ctquant vs ct = let cty = abstract_type vs.vs_ty in
                          CTquant (q, cty, ct) in
      let ct_closed = List.fold_right ctquant lvs ctn_open in
      ct_closed
  | Tnot t -> let ct = abstract_term_rec bv_lvl lvl t in
              CTnot ct
  | Tconst (Constant.ConstInt i) -> CTint i.Number.il_int
  | Tconst _ ->
      let s = "" in
      (* let open Format in
       * Pretty.print_term str_formatter t;
       * let s = flush_str_formatter () in *)
      invalid_arg ("Cert_abstract.abstract_term Tconst : " ^ s)
  | Tif _ -> invalid_arg "Cert_abstract.abstract_term Tif"
  | Tlet _ -> invalid_arg "Cert_abstract.abstract_term Tlet"
  | Tcase _ -> invalid_arg "Cert_abstract.abstract_term Tcase"
  | Teps _ -> invalid_arg "Cert_abstract.abstract_term Teps"

let abstract_decl_acc acc decl =
  match decl.d_node with
  | Dprop (k, pr, t) ->
      let ct = abstract_term t in
      add pr.pr_name (ct, k = Pgoal) acc
  | Dparam ls ->
      let cty = type_lsymbol ls in
      add_var ls.ls_name cty acc
  | _ -> acc

let abstract_tdecl_acc acc td =
  match td.td_node with
  | Decl decl -> abstract_decl_acc acc decl
  | _ -> acc

let rec abstract_task_acc acc = function
  | Some {task_decl = td; task_prev = task} ->
      let new_acc = abstract_tdecl_acc acc td in
      abstract_task_acc new_acc task
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
