open Why3
open Ident
open Format

open Cert_syntax
open Cert_certificates

(* We represent a ctask
    ι₁ : n₁, .., ιₕ : nₕ  |
    x₁ : ty₁,.., xᵢ : tyᵢ |
    H₁ : A₁,.., Hⱼ : Aⱼ   ⊢
    G₁ : B₁, ..., Gₖ : Bₖ
   by the formula
   ∀ ι₁, .. ∀ ιₕ,
   ∀ x₁ : ty₁, ... ∀ xᵢ: tyᵢ,
   A₁ → ... → Aⱼ →
   ¬B₁ → ... → ¬Bₖ → ⊥
 *)

let prquant fmt pred =
  if pred then fprintf fmt "`π"
  else fprintf fmt "`∀"

let print_decl fmt id cty =
  let pred = is_predicate cty in
  fprintf fmt "%a %a : %a,@ "
    prquant pred
    prid id
    prty cty

let encode_neg (ct, pos) = if pos then CTnot ct else ct

let print_task_type fmt {types; sigma; gamma_delta} =
  fprintf fmt "@<6>%s@[<hv>" "  εₜ (";
  Sid.iter (fun id -> print_decl fmt id CTprop) types;
  Mid.iter (print_decl fmt) sigma;
  Mid.iter (fun _ tp -> fprintf fmt "%a ⇒@ "
                          prdisj (encode_neg tp)) gamma_delta;
  prpv fmt CTfalse;
  fprintf fmt "@])"

let decl_hyp_ids ct =
  let decl_ids = Sid.elements ct.types @ Mid.keys ct.sigma in
  let hyp_ids = Mid.keys ct.gamma_delta in
  decl_ids, hyp_ids

let print_certif fmt (c : kcert) =
  let rstr pos = if pos then "Goal" else "Hyp" in
  let rec pc fmt = function
  | KDuplicate _ | KFoldArr _
  | KFoldIff _  | KSwapNegate _| KEqSym _ | KEqTrans _ ->
      verif_failed "Construct/Duplicate/Fold/SwapNeg/Eq/Let left"
  | KReduce (_, _, _, _, c) ->
      pc fmt c
  | KHole ct ->
      let decl_ids, hyp_ids = decl_hyp_ids ct in
      fprintf fmt "@[%a %a@]"
        (print_list prid) (ct.uid :: decl_ids)
        (print_list prhyp) hyp_ids
  | KAxiom (t, i1, i2) ->
      fprintf fmt "Axiom %a %a %a"
        prpv t prhyp i1 prhyp i2
  | KTrivial (pos, i) ->
      fprintf fmt "Trivial%s %a"
        (rstr pos)
        prhyp i
  | KEqRefl (_, t, i) ->
      fprintf fmt "EqRefl %a %a"
        prpv t prhyp i
  | KAssert (i, t, c1, c2) ->
      fprintf fmt "Assert %a@ \
                   @[<hv 3>(λ %a,@ %a)@]@ \
                   @[<hv 3>(λ %a,@ %a)@]"
        prpv t
        prhyp i pc c1
        prhyp i pc c2
  | KSplit (pos, t1, t2, i, c1, c2) ->
      fprintf fmt "Split%s %a %a %a@ \
                   @[<hv 3>(λ %a,@ %a)@]@ \
                   @[<hv 3>(λ %a,@ %a)@]"
        (rstr pos) prpv t1 prpv t2 prhyp i
        prhyp i pc c1
        prhyp i pc c2
  | KUnfoldIff (pos, t1, t2, i, c) ->
      fprintf fmt "UnfoldIff%s %a %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i
        pc c
  | KUnfoldArr (pos, t1, t2, i, c) ->
      fprintf fmt "UnfoldArr%s %a %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i
        pc c
  | KSwap (pos, t, i, c) ->
      fprintf fmt "Swap%s %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t prhyp i prhyp i
        pc c
  | KDestruct (pos, t1, t2, i, i1, i2, c) ->
      fprintf fmt "Destruct%s %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i1 prhyp i2
        pc c
  | KClear (pos, t, i, c) ->
      fprintf fmt "Clear%s %a %a (@,\
                   @[<hv>%a@])"
        (rstr pos) prpv t prhyp i
        pc c
  | KForget (_, c) ->
      fprintf fmt "Forget (@,\
                   @[<hv>%a@])"
        pc c
  | KIntroQuant (pos, _, p, i, y, c) ->
      fprintf fmt "IntroQuant%s %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv p prhyp i prid y prhyp i
        pc c
  | KInstQuant (pos, _, p, i1, i2, t, c) ->
      fprintf fmt "InstQuant%s %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv p prpv t prhyp i1 prhyp i1 prhyp i2
        pc c
  | KIntroType (t, p, ts::lts, c) ->
      begin match t with
      | CTqtype (tv::ltv, t') ->
          let nt = CTqtype (ltv, t') in
          let nt_subst = ct_ty_subst (Ty.Mtv.singleton tv (CTyapp (ts, []))) nt in
          fprintf fmt "IntroType (λ %a, %a) %a (λ %a %a,@ \
                       @[<hv>%a@])"
            Pretty.print_tv tv prpv nt prhyp p
            prid ts prhyp p
            pc (KIntroType (nt_subst, p, lts, c))
      | _ -> assert false
      end
  | KIntroType (_, _, [], c) -> pc fmt c
  | KInstType (t, p1, p2, ty::lty, c) ->
      begin match t with
      | CTqtype (tv::ltv, t') ->
          let nt = CTqtype (ltv, t') in
          let nt_subst = ct_ty_subst (Ty.Mtv.singleton tv ty) nt in
          fprintf fmt "InstType (λ %a, %a) %a (λ %a %a,@ \
                       @[<hv>%a@])"
            Pretty.print_tv tv prpv (CTqtype (ltv, t')) prty_paren ty
            prhyp p1 prhyp p2
            pc (KInstType (nt_subst, p2, p2, lty, c))
      | _ -> assert false
      end
  | KInstType (_, _, _, [], c) -> pc fmt c
  | KRewrite (pos, is_eq, _, t1, t2, ctxt, i1, i2, c) ->
      let str_fmla = match is_eq with None -> "" | _ -> "Fmla" in
      fprintf fmt "Rewrite%s%s %a %a %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        str_fmla (rstr pos) prpv t1 prpv t2 prpv ctxt
        prhyp i1 prhyp i2 prhyp i1 prhyp i2
        pc c
  | KInduction (g, hi1, hi2, hr, x, a, ctxt, c1, c2) ->
      fprintf fmt "Induction %a %a %a %a@ \
                   @[<hv 3>(λ %a %a %a,@ %a)@]@ \
                   @[<hv 3>(λ %a %a %a %a,@ %a)@]"
        prpv a prpv ctxt prpv x prhyp g
        prpv x prhyp hi1 prhyp g pc c1
        prpv x prhyp hi2 prhyp hr prhyp g pc c2
  in
  pc fmt c

let print fmt init res certif =
  (* The type we need to check is inhabited. *)
  let p_type fmt () =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " →@ ")
      print_task_type fmt (res @ [init]) in
  (* The term that has the correct type. *)
  let p_term fmt () =
    let decl_ids, hyp_ids = decl_hyp_ids init in
    let task_ids = List.map (fun ct -> ct.uid) res in
    fprintf fmt "@[<2>@<1>%s %a@ %a@]"
      "λ"
      (print_list prid) (task_ids @ decl_ids)
      (print_list prhyp) hyp_ids;
    fprintf fmt ",@ ";
    print_certif fmt certif in

  fprintf fmt "@[<v>require open cert_lambdapi.preamble;@ @ \
               symbol to_verify :@ \
               @[<v>%a@]@ \
               @<2>%s@[<v>%a@]@];@."
    p_type ()
    "≔ "
    p_term ()


let checker_lambdapi certif init res =
  try
    let check_cert = "/tmp/check_cert.lp" in
    let oc = open_out check_cert in
    let fmt = formatter_of_out_channel oc in
    print fmt init res certif;
    close_out oc;
    let quiet = ">/dev/null 2>&1" in
    let ret = Sys.command ("lambdapi check --map-dir check:/tmp/ "
                           ^ check_cert ^ quiet) in
    if ret <> 0 then verif_failed "Not verified by Lambdapi"
  with e -> raise (Trans.TransFailure ("checker_lambdapi", e))
