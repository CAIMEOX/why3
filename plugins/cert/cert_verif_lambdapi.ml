open Why3
open Ident
open Format

open Cert_abstract
open Cert_certificates

(* We represent a ctask
   x₁ : ty₁,.., xᵢ : tyᵢ | H₁ : A₁,.., Hⱼ : Aⱼ ⊢ G₁ : B₁, ..., Gₖ : Bₖ
   by the formula
   ∀ x₁ : ty₁, ... ∀ xᵢ: tyᵢ, A₁ → ... → Aⱼ → ¬B₁ → ... → ¬Bₖ → ⊥
   As an intermediate data structure we use lists to fix the order
 *)
type ctask_simple =
  { s  : (ident * ctype) list;
    gd : (ident * cterm) list }

let simplify_task (cta : ctask) : ctask_simple =
  let encode_neg (k, (ct, pos)) = k, if pos then CTnot ct else ct in
  { s = Mid.bindings cta.sigma;
    gd = Mid.bindings cta.gamma_delta
         |> List.map encode_neg }

let print_task fmt {s; gd} =
  fprintf fmt "@[<3>(Π ";
  pp_print_list ~pp_sep:pp_print_space
    (fun fmt (id, cty) ->
      fprintf fmt "(%a : ekind %a)"
        pri id
        prtyparen cty) fmt s;
  let _, terms = List.split gd in
  let tp = terms @ [CTfalse] in
  fprintf fmt ",@]@  @[<hv 7>etype (";
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ⇨@ ") prdisj fmt tp;
  fprintf fmt ")@])"

let print_certif print_next fmt c =
  let rstr goal = if goal then "_goal" else "_hyp" in
  let rec pc fmt = function
  | ELet _ | EConstruct _ | ERename _ | EFoldArr _ ->
      verif_failed "Construct/Let/Rename/Fold left"
  | EHole _ ->
      print_next fmt ()
  | EAxiom (t, h, g) ->
      fprintf fmt "axiom %a %a %a"
        prpv t
        hpri h
        hpri g
  | ETrivial (goal, g) ->
      fprintf fmt "trivial%s %a"
        (rstr goal)
        hpri g
  | ECut (i, a, ce1, ce2) ->
      fprintf fmt "cut %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   (λ %a, @[<hv>%a@])"
        prpv a
        hpri i pc ce1
        hpri i pc ce2
  | ESplit (goal, a, b, i, c1, c2) ->
      fprintf fmt "split%s %a %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   (λ %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        hpri i pc c1
        hpri i pc c2
        hpri i
  | EUnfoldIff (goal, a, b, i, c) ->
      fprintf fmt "unfold_iff%s %a %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        hpri i pc c
        hpri i
  | EUnfoldArr (goal, a, b, i, c) ->
      fprintf fmt "unfold_arr%s %a %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        hpri i pc c
        hpri i
  | ESwapNeg (goal, a, i, c) ->
      fprintf fmt "swap_neg%s %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        hpri i pc c
        hpri i
  | ESwap (goal, a, i, c) ->
      fprintf fmt "swap%s %a@ \
                   (λ %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        hpri i pc c
        hpri i
  | EDestruct (goal, a, b, i, j1, j2, c) ->
      fprintf fmt "destruct%s %a %a@ \
                   (λ %a %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        hpri j1 hpri j2 pc c
        hpri i
  | EWeakening (goal, a, i, c) ->
      fprintf fmt "weakening%s %a@ \
                   (@[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        pc c
        hpri i
  | EIntroQuant (goal, (CTquant (_, cty, _) as p), i, y, c) ->
      fprintf fmt "intro_quant%s %a %a@ \
                   (λ %a %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prty cty
        prpv p
        pri y hpri i pc c
        hpri i
  | EInstQuant (goal, (CTquant (_, cty, _) as p), i, j, t, c) ->
      fprintf fmt "inst_quant%s %a %a %a@ \
                   (λ %a %a, @[<hv>%a@])@ \
                   %a"
        (rstr goal)
        prty cty
        prpv p
        prpv t
        hpri i hpri j pc c
        hpri i
  | ERewrite (goal, ty, a, b, ctxt, i, h, c) ->
      fprintf fmt "rewrite%s %a %a %a %a@ \
                   (λ %a %a, @[<hv>%a@])@ \
                   %a@ \
                   %a"
        (rstr goal)
        prtyparen ty prpv a prpv b prpv ctxt
        hpri h hpri i pc c
        hpri h
        hpri i
  | _ -> assert false
  in
  pc fmt c

let print fmt init res (task_ids, certif) =
  let res = List.map simplify_task res in
  let init = simplify_task init in
  (* The type we need to check is inhabited *)
  let p_type fmt () =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " →@ ")
      print_task fmt (res @ [init]) in
  (* Print next applied_task, used to fill the holes *)
  let print_next =
    let str = Stream.of_list (List.combine task_ids res) in
    fun fmt () ->
    let task_id, {s; gd } = Stream.next str in
    let fv_ids, _ = List.split s in
    let hyp_ids, _ = List.split gd in
    fprintf fmt "@[%a %a@]"
      (print_list pri) (task_id :: fv_ids)
      (print_list hpri) hyp_ids in
  (* The term that has the correct type *)
  let p_term fmt () =
    let {s; gd} = init in
    let fv_ids, _ = List.split s in
    let hyp_ids, _ = List.split gd in
    fprintf fmt "@[<2>@<1>%s %a@ %a@]"
      "λ"
      (print_list pri) (task_ids @ fv_ids)
      (print_list hpri) hyp_ids;
    fprintf fmt ",@ ";
    print_certif print_next fmt certif in

  fprintf fmt "@[<v>definition to_verify :@   \
               @[<v>%a@]@ \
               @<3>%s@[<v>%a@]@]@."
    p_type ()
    "≔  "
    p_term ();
  forget_all ip;
  forget_all hip

let checker_lambdapi certif init res =
  try
    let oc = open_out "/tmp/check_line.lp" in
    let fmt = formatter_of_out_channel oc in
    print fmt init res certif;
    close_out oc;
    let coc = Filename.(concat Config.datadir (concat "lambdapi" "CoC.lp")) in
    let pkg_conf = Filename.(concat Config.datadir (concat "lambdapi" "lambdapi.pkg")) in
    Sys.command ("cat " ^ coc ^ " > /tmp/check_all.lp") |> ignore;
    Sys.command "cat /tmp/check_line.lp >> /tmp/check_all.lp" |> ignore;
    Sys.command ("cp " ^ pkg_conf ^ " /tmp/lambdapi.pkg") |> ignore;
    let ret = Sys.command "lambdapi check /tmp/check_all.lp 2> /dev/null 1> /dev/null" in
    if ret <> 0 then verif_failed "Not verified by Lambdapi"
  with e -> raise (Trans.TransFailure ("Cert_verif_lambdapi.checker_lambdapi", e))
