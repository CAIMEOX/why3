open Why3
open Term
open Ident
open Decl
open Task
open Ty
open Format

(** Utility **)

let print_list pre = pp_print_list ~pp_sep:pp_print_space pre

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

(** To certify transformations, we will represent Why3 tasks by ctask, its terms
   by cterm and type those terms with ctype *)

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol (* type variable *)
  | CTprop (* type of formulas *)
  | CTyapp of tysymbol * ctype list (* (possibly) applied type constant *)
  | CTarrow of ctype * ctype (* arrow type *)

let ctint = CTyapp (ts_int, [])
let ctreal = CTyapp (ts_real, [])
let ctbool = CTyapp (ts_bool, [])

(** Utility functions on ctype *)

(* Syntactic equality *)
let rec cty_equal ty1 ty2 = match ty1, ty2 with
  | CTprop, CTprop -> true
  | CTyvar v1, CTyvar v2 -> Ty.tv_equal v1 v2
  | CTyapp (ty1, l1), CTyapp (ty2, l2) ->
      ts_equal ty1 ty2 && List.for_all2 cty_equal l1 l2
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      cty_equal f1 f2 && cty_equal a1 a2
  | (CTyvar _ | CTyapp _ | CTarrow _ | CTprop), _ -> false

(* Equality modulo α-conversion *)
let rec cty_same map ty1 ty2 = match ty1, ty2 with
  | CTprop, CTprop -> true, map
  | CTyvar v1, CTyvar v2 ->
      begin match Mtv.find_opt v1 map with
      | None -> true, Mtv.add v1 v2 map
      | Some v2' -> Ty.tv_equal v2' v2, map end
  | CTyapp (ty1, l1), CTyapp (ty2, l2) ->
      let b, map = for_all2_cty_equal map l1 l2 in
      ts_equal ty1 ty2 && b, map
  | CTarrow (f1, a1), CTarrow (f2, a2) ->
      for_all2_cty_equal map [f1; a1] [f2; a2]
  | (CTyvar _ | CTyapp _ | CTarrow _ | CTprop), _ -> false, map

and for_all2_cty_equal map l1 l2 = match l1, l2 with
  | [], [] -> true, map
  | h1::t1, h2::t2 ->
      let b, map = cty_same map h1 h2 in
      if b then for_all2_cty_equal map t1 t2
      else false, map
  | _ -> false, map

let cty_same ty1 ty2 = cty_same Mtv.empty ty1 ty2 |> fst

(* Warning: beware variable capture *)
let rec cty_ty_subst subst = function
  | CTyvar tv' when Mtv.mem tv' subst -> Mtv.find tv' subst
  | CTarrow (cty1, cty2) ->
      CTarrow (cty_ty_subst subst cty1, cty_ty_subst subst cty2)
  | CTyapp (ts, l) ->
      CTyapp (ts, List.map (cty_ty_subst subst) l)
  | (CTyvar _ | CTprop) as cty -> cty


let rec is_predicate = function
  | CTprop -> true
  | CTarrow (_, ct) -> is_predicate ct
  | _ -> false

(** Pretty printing of ctype (compatible with lambdapi) *)

let san =
  let lower_h c = if c = 'H' then "h" else char_to_alnum c in
  sanitizer lower_h char_to_alnum

let hsan s = "H" ^ san s

let ip = create_ident_printer ~sanitizer:san []
let hip = create_ident_printer ~sanitizer:hsan []

let prid fmt i = fprintf fmt "%s" (id_unique ip i)

let prhyp fmt i = fprintf fmt "%s" (id_unique hip i)

let prpr fmt pr = prhyp fmt pr.pr_name

(* pred functions know if we are printing the type of a predicate or not *)
let rec pred_ty pred fmt ty = match ty with
  | CTyapp (ts, l) when l <> [] ->
      fprintf fmt "@[<2>%a@ %a@]"
        prts ts
        (print_list (pred_typaren pred)) l
  | CTarrow (t1, t2) ->
      fprintf fmt "@[%a %a@ %a@]"
        (pred_typaren pred) t1
        prarrow pred
        (pred_ty pred) t2
  | _ -> pred_typaren pred fmt ty

and pred_typaren pred fmt = function
  | CTyvar _ -> fprintf fmt "Z"
  (* TODO handle polymorphic symbols *)
  (* Pretty.print_tv fmt v *)
  | CTprop -> fprintf fmt "DType"
  | CTyapp (ts, []) -> prts fmt ts
  | cty -> fprintf fmt "(%a)" (pred_ty pred) cty

and prts fmt ts =
  if ts_equal ts ts_bool then fprintf fmt "Bool"
  else if ts_equal ts ts_int then fprintf fmt "Z"
  else Pretty.print_ts fmt ts

and prarrow fmt pred =
  if pred then fprintf fmt "⇀"
  else fprintf fmt "⇁"

(* Prints a type without outside parentheses *)
let prty fmt ty =
  pred_ty (is_predicate ty) fmt ty

(* Prints a type with outside parentheses if needed *)
let prtyparen fmt ty =
  pred_typaren (is_predicate ty) fmt ty

type cterm =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTint of BigInt.t
  | CTapp of cterm * cterm (* binary application *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of cquant * ctype * cterm (* quantifier binding *)
  | CTqtype of tvsymbol * cterm
  (* type quantifier binding, they are assumed to only be in prenex form *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

let id_eq = ps_equ.ls_name
let eq = CTfvar id_eq
let id_true = fs_bool_true.ls_name
let id_false = fs_bool_false.ls_name

let le_str = op_infix "<="
let ge_str = op_infix ">="
let lt_str = op_infix "<"
let gt_str = op_infix ">"
let pl_str = op_infix "+"
let ml_str = op_infix "*"
let pre_mn_str = op_infix "-"
let inf_mn_str = op_prefix "-"

(** Utility functions on cterm *)

let ct_map f ct = match ct with
  | CTbvar _ | CTfvar _ | CTint _ | CTtrue | CTfalse -> ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, f ct)
  | CTqtype (i, ct) -> CTqtype (i, f ct)
  | CTapp (ct1, ct2) -> CTapp (f ct1, f ct2)
  | CTbinop (op, ct1, ct2) ->  CTbinop (op, f ct1, f ct2)
  | CTnot ct -> CTnot (f ct)

(* Warning: beware variable capture *)
let rec ct_ty_subst subst = function
  | CTquant (q, qcty, ct) ->
      CTquant (q, cty_ty_subst subst qcty,
               ct_ty_subst subst ct)
  | ct -> ct_map (ct_ty_subst subst) ct

let rec ct_equal subst1 subst2 t1 t2 =
  let ct_eq = ct_equal subst1 subst2 in
  match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      ct_eq tl1 tl2 && ct_eq tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && ct_eq tl1 tl2 && ct_eq tr1 tr2
  | CTquant (q1, ty1, t1), CTquant (q2, ty2, t2) when q1 = q2 ->
      let ty1 = cty_ty_subst subst1 ty1 in
      let ty2 = cty_ty_subst subst2 ty2 in
      cty_equal ty1 ty2 && ct_eq t1 t2
  | CTqtype (tv1, t1), CTqtype (tv2, t2) ->
      let tv = create_tvsymbol (id_fresh "cteq") in
      let subst1 = Mtv.add tv1 (CTyvar tv) subst1 in
      let subst2 = Mtv.add tv2 (CTyvar tv) subst2 in
      ct_equal subst1 subst2 t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> ct_eq t1 t2
  | CTint i1, CTint i2 -> BigInt.eq i1 i2
  | (CTbvar _ | CTfvar _ | CTapp _ | CTbinop _ | CTquant _
     | CTqtype _ | CTtrue | CTfalse | CTnot _ | CTint _), _ -> false

let ct_equal = ct_equal Mtv.empty Mtv.empty

(* Bound variable substitution *)
let rec ct_bv_subst k u ctn = match ctn with
  | CTbvar i -> if i = k then u else ctn
  | CTquant (q, cty, ct) ->
      let nct = ct_bv_subst (k+1) u ct in
      CTquant (q, cty, nct)
  | _ -> ct_map (ct_bv_subst k u) ctn

let ct_open t u = ct_bv_subst 0 u t

(* Checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let rec term ct = match ct with
    | CTbvar _ -> false
    | CTapp (ct1, ct2)
    | CTbinop (_, ct1, ct2) -> term ct1 && term ct2
    | CTquant (_, _, t) -> term (ct_open t (CTfvar di))
    | CTqtype (_, ct)
    | CTnot ct -> term ct
    | CTint _ | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* Free variable substitution (u should be locally closed) *)
let rec ct_fv_subst z u ctn = match ctn with
  | CTfvar x -> if id_equal z x then u else ctn
  | _ -> ct_map (ct_fv_subst z u) ctn

let ct_subst (m : cterm Mid.t) ct =
  Mid.fold ct_fv_subst m ct

(* Variable closing *)
let rec ct_fv_close x k ct = match ct with
  | CTfvar y -> if id_equal x y then CTbvar k else ct
  | CTquant (q, cty, ct) -> CTquant (q, cty, ct_fv_close x (k+1) ct)
  | _ -> ct_map (ct_fv_close x k) ct

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
  | CTqtype (_, ct)
  | CTnot ct -> mem_cont x ct cont
  | CTint _ | CTbvar _ | CTtrue | CTfalse -> cont false

let mem x t = mem_cont x t (fun x -> x)

let rec replace_cterm tl tr t =
  if ct_equal t tl
  then tr
  else ct_map (replace_cterm tl tr) t

(** Pretty printing of terms (compatible with lambdapi) *)

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
      fprintf fmt "%a ↝ %a"
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

(* TODO : update this
   We will denote a ctask <sigma; gamma_delta> by <Σ | Γ ⊢ Δ> where:
   • <Σ> contains all the signature declarations <x : ty>
     where <x> is mapped to <ty> in <sigma>
   • <Γ> contains all the declarations <H : P>
     where <H> is mapped to <(P, false)> in <gamma_delta>
   • <Δ> contains all the declarations <H : P>
     where <H> is mapped to <(P,  true)> in <gamma_delta>

   We sometimes omit signature (when it's not confusing) and write <Γ ⊢ Δ>
*)
type ('t, 'ty) ctask =
  { get_ls : string -> lsymbol;
    types_interp : Sid.t;
    types : Sid.t;
    sigma_interp : 'ty Mid.t;
    sigma : 'ty Mid.t;
    gamma_delta : ('t * bool) Mid.t
  }

type kernel_ctask = (cterm, ctype) ctask

(** Pretty printing of ctask *)

let po p fmt = function
  | None -> fprintf fmt "None"
  | Some x -> fprintf fmt "%a" p x

let prt fmt sid =
  Sid.iter (fun i -> fprintf fmt "%a@ " prid i) sid

let prs fmt mid =
  Mid.iter (fun x ty -> fprintf fmt "%a : %a@ " prid x prty ty) mid

let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prprop fmt h (cte, pos) =
  fprintf fmt "%a%a : %a@ " prpos pos prhyp h pcte cte

let prgd fmt mid =
  Mid.iter (prprop fmt) mid

let pcta fmt cta =
  fprintf fmt "@[<v>TYPES INTERP:@ %a@ \
               TYPES:@ %a@ \
               SIGMA INTERP:@ %a@ \
               SIGMA:@ %a@ \
               %a@]@."
    prt cta.types_interp
    prt cta.types
    prs cta.sigma_interp
    prs cta.sigma
    prgd cta.gamma_delta

let plcta =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "========@ ") pcta

let eplcta cta lcta =
  eprintf "@[<v>INIT :@ \
           %a==========@ \
           RES :@ \
           %a@]@."
    pcta cta
    plcta lcta

let print_ctasks filename lcta =
  let filename = Sysutil.uniquify filename in
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "@[<v>RESULTING TASKS:@ @ \
               %a@]@."
    plcta lcta;
  close_out oc

(** Utility functions on ctask *)

let ctask_equal cta1 cta2 =
  Mid.equal cty_same cta1.sigma cta2.sigma &&
    let cterm_pos_equal (t1, p1) (t2, p2) =
      ct_equal t1 t2 && p1 = p2 in
    Mid.equal cterm_pos_equal cta1.gamma_delta cta2.gamma_delta

let find_ident s h cta =
  match Mid.find_opt h cta.gamma_delta with
  | Some x -> x
  | None ->
      let s = asprintf "%s : Can't find ident %a in the task" s prhyp h in
      verif_failed s

let ctask_new get_ls types_interp sigma_interp =
  { get_ls;
    types_interp;
    types = Sid.empty;
    sigma_interp;
    sigma = Mid.empty;
    gamma_delta = Mid.empty }

let lift_mid_cta f cta =
  { cta with
    gamma_delta = f (cta.gamma_delta) }

(* Make sure to not add interpreted types to the abstract types *)
let add_type i cta =
  { cta with
    types = if Sid.mem i cta.types_interp
            then cta.types
            else Sid.add i cta.types  }

(* Make sure to not add interpreted variables to the signature *)
let add_var i cty cta =
  { cta with
    sigma = if Mid.mem i cta.sigma_interp
            then cta.sigma
            else Mid.add i cty cta.sigma  }

let remove i cta = lift_mid_cta (Mid.remove i) cta

let add i ct cta = lift_mid_cta (Mid.add i ct) cta


(* Separates hypotheses and goals *)
let split_hyp_goal cta =
  let open Mid in
  fold (fun h (ct, pos) (gamma, delta) ->
      if pos then gamma, add h (ct, pos) delta
      else add h (ct, pos) gamma, delta)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the
   second argument *)
let set_goal cta =
  let gamma, delta = split_hyp_goal cta.gamma_delta in
  let gpr, _ = Mid.choose gamma in
  fun ct ->
  { cta with
    gamma_delta = Mid.add gpr (ct, true) delta }


let instantiate f a =
  match f with
  | CTquant (CTlambda, _, f) -> ct_open f a
  | _ -> assert false

(* Typing algorithm *)


let infer_type cta t =
  let rec infer_type sigma t = match t with
    | CTfvar v -> Mid.find v sigma
    | CTbvar _ -> failwith "unbound variable"
    | CTtrue | CTfalse -> CTprop
    | CTnot t -> let ty = infer_type sigma t in
                 begin try assert (cty_equal ty CTprop);
                     CTprop
                 with _ -> failwith "not should apply on prop" end
    | CTquant (quant, ty1, t) ->
        let ni = id_register (id_fresh "type_ident") in
        let sigma = Mid.add ni ty1 sigma in
        let t = ct_open t (CTfvar ni) in
        let ty2 = infer_type sigma t in
        begin match quant with
        | CTlambda -> CTarrow (ty1, ty2)
        | CTforall | CTexists ->
            try assert (cty_equal ty2 CTprop);
                CTprop
            with _ -> failwith "quantification on non prop" end
    | CTapp (t1, t2) ->
        begin match infer_type sigma t1, infer_type sigma t2 with
        | CTarrow (ty1, ty2), ty3 ->
            if cty_equal ty1 ty3 then ty2
            else begin eprintf "@[<v>try to apply ty1 -> ty2 to ty3@ \
                                ty1 : %a@ \
                                ty2 : %a@ \
                                ty3 : %a@]@."
                         prty ty1
                         prty ty2
                         prty ty3;
                       assert false end
        | _ -> failwith "can't apply non functions"
        end
    | CTbinop (_, t1, t2) ->
        let ty1, ty2 = infer_type sigma t1, infer_type sigma t2 in
        begin try assert (cty_equal ty1 CTprop);
                  assert (cty_equal ty2 CTprop);
                  CTprop
              with _ -> failwith "binop on non prop" end
    | CTqtype (_, ct) -> infer_type sigma ct
    | CTint _ -> ctint in
  let sigma_plus_interp = Mid.set_union cta.sigma cta.sigma_interp in
  infer_type sigma_plus_interp t

let well_typed cta t =
  ignore (infer_type cta t)

let infers_into cta t ty =
  try assert (cty_equal (infer_type cta t) ty)
  with e -> eprintf "@[<v>wrong type for: %a@ \
                     expected: %a@]@." pcte t prty ty;
            raise e

let instantiate_safe cta f a =
  well_typed cta f;
  let ty = infer_type cta a in
  match f with
  | CTquant (CTlambda, ty', f) when cty_equal ty ty' ->
      ct_open f a
  | _ -> assert false


(** We instrument existing transformations to produce a certificate *)

type 'certif ctransformation = (task list * 'certif) Trans.trans


