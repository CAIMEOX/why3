open Why3
open Ident
open Format

open Cert_abstract
open Cert_certificates

(* We represent a ctask
   x₁ : ty₁,.., xᵢ : tyᵢ | H₁ : A₁,.., Hⱼ : Aⱼ ⊢ G₁ : B₁, ..., Gₖ : Bₖ
   by the formula
   ∀ x₁ : ty₁, ... ∀ xᵢ: tyᵢ, A₁ → ... → Aⱼ → ¬B₁ → ... → ¬Bₖ → ⊥
   As an intermediate data structure, we use lists in order to fix the order
   and remember the idents which are used to construct the proof term.
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
  fprintf fmt "@[<hov 3>(Π ";
  pp_print_list ~pp_sep:pp_print_space
    (fun fmt (id, cty) ->
      fprintf fmt "(%a : %a)"
        pri id
        prty cty) fmt s;
  let _, terms = List.split gd in
  let tp = terms @ [CTfalse] in
  fprintf fmt ",@]@  @[<hv 7>etype (";
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ⇨@ ") prdisj fmt tp;
  fprintf fmt ")@])"

let print_certif at fmt c =
  let s = Stream.of_list at in
  let rstr goal = if goal then "_goal" else "_hyp" in
  let rec pc fmt = function
  | ELet _ | EConstruct _ | ERename _ | EFoldArr _ ->
      verif_failed "Construct/Let/Rename/Fold left"
  | EHole _ ->
      fprintf fmt "%s" (Stream.next s)
  | EAxiom (t, h, g) ->
      fprintf fmt "axiom %a %a %a"
        prpv t
        pri h
        pri g
  | ETrivial (goal, g) ->
      fprintf fmt "trivial%s %a"
        (rstr goal)
        pri g
  | ECut (i, a, ce1, ce2) ->
      fprintf fmt "cut %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   (λ %a, @[<hv 0>%a@])"
        prpv a
        pri i pc ce1
        pri i pc ce2
  | ESplit (goal, a, b, i, c1, c2) ->
      fprintf fmt "split%s %a %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        pri i pc c1
        pri i pc c2
        pri i
  | EUnfoldIff (goal, a, b, i, c) ->
      fprintf fmt "unfold_iff%s %a %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        pri i pc c
        pri i
  | EUnfoldArr (goal, a, b, i, c) ->
      fprintf fmt "unfold_arr%s %a %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        pri i pc c
        pri i
  | ESwapNeg (goal, a, i, c) ->
      fprintf fmt "swap_neg%s %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        pri i pc c
        pri i
  | ESwap (goal, a, i, c) ->
      fprintf fmt "swap%s %a@ \
                   (λ %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        pri i pc c
        pri i
  | EDestruct (goal, a, b, i, j1, j2, c) ->
      fprintf fmt "destruct%s %a %a@ \
                   (λ %a %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        prpv b
        pri j1 pri j2 pc c
        pri i
  | EWeakening (goal, a, i, c) ->
      fprintf fmt "weakening%s %a@ \
                   (@[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv a
        pc c
        pri i
  | EIntroQuant (goal, p, i, y, c) ->
      fprintf fmt "intro_quant%s %a@ \
                   (λ %a %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv p
        pri y pri i pc c
        pri i
  | EInstQuant (goal, p, i, j, t, c) ->
      fprintf fmt "inst_quant%s %a %a@ \
                   (λ %a %a, @[<hv 0>%a@])@ \
                   %a"
        (rstr goal)
        prpv p
        prpv t
        pri i pri j pc c
        pri i
  | ERewrite (goal, a, b, ctxt, i, h, c) ->
      fprintf fmt "rewrite%s %a %a %a@ \
                   (λ %a %a, @[<hv 0>%a@])@ \
                   %a@ \
                   %a"
        (rstr goal)
        prpv a prpv b prpv ctxt
        pri h pri i pc c
        pri h
        pri i
      (* verif_failed "Rewrite is not yet supported by the Lambdapi checker" *)
  in
  pc fmt c

let pp_print_blank fmt () =
  fprintf fmt " "

let print fmt init res (task_ids, certif) =
  let res = List.map simplify_task res in
  let init = simplify_task init in
  (* The type we need to check is inhabited *)
  let p_type fmt () =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " →@ ")
      print_task fmt (res @ [init]) in
  (* applied_tasks are used to fill the holes *)
  let applied_tasks =
    List.map2 (fun task_id {s; gd} ->
        let fv_ids, _ = List.split s in
        let hyp_ids, _ = List.split gd in
        pp_print_list ~pp_sep:pp_print_blank
          pri str_formatter (task_id :: fv_ids @ hyp_ids);
        flush_str_formatter ())
      task_ids
      res in
  (* The term that has the correct type *)
  let p_term fmt () =
    let {s; gd} = init in
    let fv_ids, _ = List.split s in
    let hyp_ids, _ = List.split gd in
    let vars = task_ids @ fv_ids @ hyp_ids in
    fprintf fmt "λ ";
    pp_print_list ~pp_sep:pp_print_blank pri fmt vars;
    fprintf fmt ",@ ";
    print_certif applied_tasks fmt certif in

  fprintf fmt "@[<v 0>definition to_verify :@   \
               @[<v 0>%a@]@ \
               ≔  @[<v 0>%a@]@]@."
    p_type ()
    p_term ()

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
