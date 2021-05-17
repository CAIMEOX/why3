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
  fprintf fmt "tEv (@[<hv>";
  Sid.iter (fun id -> print_decl fmt id CTprop) types;
  Mid.iter (print_decl fmt) sigma;
  Mid.iter (fun _ tp -> fprintf fmt "%a ⇒@ "
                          prdisj (encode_neg tp)) gamma_delta;
  prpv fmt CTfalse;
  fprintf fmt "@])"

let print_certif print_next fmt c =
  let rstr pos = if pos then "Goal" else "Hyp" in
  let rec pc fmt = function
  | EConstruct _ | EDuplicate _ | EFoldArr _
  | EFoldIff _ | EEqSym _ | EEqTrans _ ->
      verif_failed "Construct/Duplicate/Fold/Eq/Let left"
  | EHole task_id ->
      (* TODO *)
      print_next fmt task_id
  | EAxiom (t, i1, i2) ->
      fprintf fmt "Axiom %a %a %a"
        prpv t prhyp i1 prhyp i2
  | ETrivial (pos, i) ->
      fprintf fmt "Trivial%s %a"
        (rstr pos)
        prhyp i
  | EEqRefl (_, t, i) ->
      fprintf fmt "EqRefl %a %a"
        prpv t prhyp i
  | EAssert (i, t, c1, c2) ->
      fprintf fmt "Assert %a@ \
                   @[<hv 3>(λ %a,@ %a)@]@ \
                   @[<hv 3>(λ %a,@ %a)@]"
        prpv t
        prhyp i pc c1
        prhyp i pc c2
  | ESplit (pos, t1, t2, i, c1, c2) ->
      fprintf fmt "Split%s %a %a %a@ \
                   @[<hv 3>(λ %a,@ %a)@]@ \
                   @[<hv 3>(λ %a,@ %a)@]"
        (rstr pos) prpv t1 prpv t2 prhyp i
        prhyp i pc c1
        prhyp i pc c2
  | EUnfoldIff (pos, t1, t2, i, c) ->
      fprintf fmt "UnfoldIff%s %a %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i
        pc c
  | EUnfoldArr (pos, t1, t2, i, c) ->
      fprintf fmt "UnfoldArr%s %a %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i
        pc c
  | ESwapNeg (pos, t, i, c) ->
      fprintf fmt "SwapNeg%s %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t prhyp i prhyp i
        pc c
  | ESwap (pos, t, i, c) ->
      fprintf fmt "Swap%s %a %a (λ %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t prhyp i prhyp i
        pc c
  | EDestruct (pos, t1, t2, i, i1, i2, c) ->
      fprintf fmt "Destruct%s %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv t1 prpv t2 prhyp i prhyp i1 prhyp i2
        pc c
  | EClear (pos, t, i, c) ->
      fprintf fmt "Clear%s %a %a (@,\
                   @[<hv>%a@])"
        (rstr pos) prpv t prhyp i
        pc c
  | EForget (_, c) ->
      fprintf fmt "Forget (@,\
                   @[<hv>%a@])"
        pc c
  | EIntroQuant (pos, _, p, i, y, c) ->
      fprintf fmt "IntroQuant%s %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv p prhyp i prpv y prhyp i
        pc c
  | EInstQuant (pos, _, p, i1, i2, t, c) ->
      fprintf fmt "InstQuant%s %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        (rstr pos) prpv p prpv t prhyp i1 prhyp i1 prhyp i2
        pc c
  | ERewrite (pos, is_eq, _, t1, t2, ctxt, i1, i2, c) ->
      let str_fmla = match is_eq with None -> "" | _ -> "Fmla" in
      fprintf fmt "Rewrite%s%s %a %a %a %a %a (λ %a %a,@ \
                   @[<hv>%a@])"
        str_fmla (rstr pos) prpv t1 prpv t2 prpv ctxt
        prhyp i1 prhyp i2 prhyp i1 prhyp i2
        pc c
  | EInduction (g, hi1, hi2, hr, x, a, ctxt, c1, c2) ->
      fprintf fmt "Induction %a %a %a %a@ \
                   @[<hv 3>(λ %a %a %a,@ %a)@]@ \
                   @[<hv 3>(λ %a %a %a %a,@ %a)@]"
        prpv a prpv ctxt prpv x prhyp g
        prpv x prhyp hi1 prhyp g pc c1
        prpv x prhyp hi2 prhyp hr prhyp g pc c2
  in
  pc fmt c

let print fmt init res (task_ids, certif) =
  let res = List.map simplify_task res in
  let init = simplify_task init in
  (* The type we need to check is inhabited. *)
  let p_type fmt () =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " →@ ")
      print_task fmt (res @ [init]) in
  (* The following function is used to fill the holes. *)
  let print_applied_task =
    let map = Mid.of_list (List.combine task_ids res) in
    fun fmt task_id ->
    let {t; s; gd} = Mid.find task_id map in
    let fv_ids, _ = List.split s in
    let hyp_ids, _ = List.split gd in
    fprintf fmt "@[%a %a@]"
      (print_list prid) (task_id :: t @ fv_ids)
      (print_list prhyp) hyp_ids in
  (* The term that has the correct type. *)
  let p_term fmt () =
    let {t; s; gd} = init in
    let fv_ids, _ = List.split s in
    let hyp_ids, _ = List.split gd in
    fprintf fmt "@[<2>@<1>%s %a@ %a@]"
      "λ"
      (print_list prid) (task_ids @ t @ fv_ids)
      (print_list prhyp) hyp_ids;
    fprintf fmt ",@ ";
    print_certif print_applied_task fmt certif in

  fprintf fmt "@[<v>require open cert_lambdapi.preamble;@ @ \
               unif_rule Type ≡ kEv $t ↪ [ $t ≡ DType ];@ \
               unif_rule tEv $a ≡ tEv $b ↪ [ $a ≡ $b ];@ \
               unif_rule kEv $a ≡ kEv $b ↪ [ $a ≡ $b ];@ \
               unif_rule $a → $b ≡ kEv $c ↪ [ $a ≡ tEv $a'; $b ≡ kEv $b'; $c ≡ $a' ⇁ $b' ];@ \
               unif_rule $a → $b ≡ tEv $c ↪ [ $a ≡ tEv $a'; $b ≡ tEv $b'; $c ≡ $a' ⇒ $b' ];@ @ \
               symbol to_verify :@ \
               @[<v>%a@]@ \
               @<3>%s@[<v>%a@]@];@."
    p_type ()
    "≔  "
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
