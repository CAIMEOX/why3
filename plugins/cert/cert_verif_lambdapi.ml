open Why3
open Ident
open Format

open Cert_abstract
open Cert_certificates

let find_goal cta =
  let _, (t, _) = Mid.(filter (fun _ (_, b) -> b) cta |> choose) in
  t

(* We represent a ctask <H₁ : A₁, ..., Hₘ : Aₘ ⊢ G₁ : B₁, ..., Gₘ : Bₘ >
   by the formula <A₁ → ... → Aₘ → ¬B₁ → ... → ¬Bₙ → ⊥ >
   As an intermediate data structure, we use a list in order to :
     • fix the order
     • remember the idents which are used to construct the proof term
 *)
type ctask_simple = (ident * cterm) list


(* on [e1; ...; en], print_list sep gives :
   e1 sep e2 sep ... en sep
 *)
let print_list sep pe fmt l =
  List.iter (fun h -> fprintf fmt "%a%s" pe h sep) l

let print_list_inter sep pe fmt l =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "%s" sep)
    pe fmt l

(* on [e1; ...; en], print_list_pre gives :
   sep (e1) (sep (e2) ...)
 *)
let rec print_list_pre sep pe fmt = function
  | [] -> failwith "cannot print empty list with preorder"
  | [x] -> pe fmt x
  | h::t -> fprintf fmt "%s (%a) (%a)"
              sep
              pe h
              (print_list_pre sep pe) t

(* let rec collect typ ct = match ct with
 *   | CTint _ | CTbvar _  -> Mid.empty
 *   | CTfvar id -> Mid.singleton id typ
 *   | CTapp (ct1, ct2) -> Mid.set_union (collect (Arrow (Term, typ)) ct1) (collect Term ct2)
 *   | CTbinop (_, ct1, ct2) -> Mid.set_union (collect typ ct1) (collect typ ct2)
 *   | CTquant (_, ct)
 *   | CTnot ct -> collect typ ct
 *   | CTtrue | CTfalse -> Mid.empty
 *
 * let collect_stask (ta : ctask_simple) =
 *   List.fold_left (fun acc (_, ct) -> Mid.set_union acc (collect Prop ct))
 *     Mid.empty ta *)

let print_task fmt (fv, ts) =
  fprintf fmt "@[<hov 0>(Π ";
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")
    (fun fmt (id, cty) ->
      fprintf fmt "(%a : %a)"
        pri id
        prty cty) fmt fv;
  let tp = snd (List.split ts) @ [CTfalse] in
  fprintf fmt ",@]@   @[<hv 5>etype (";
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ⇨@ ") prpv fmt tp;
  fprintf fmt ")@])"

let rstr goal = if goal then "_goal" else "_hyp"

let print_certif at fmt c =
  let s = Stream.of_list at in
  let rec pc fmt = function
  | ELet _ | EConstruct _ | ERename _ | EFoldArr _ ->
      verif_failed "Construct/Let/Rename/Fold left"
  | EHole _ ->
      fprintf fmt "%s" (Stream.next s)
  | EAxiom (t, h, g) ->
      fprintf fmt "axiom (%a) %a %a"
        pcte t
        pri h
        pri g
  | ETrivial (goal, g) ->
      fprintf fmt "trivial%s %a" (rstr goal)
        pri g
  | ECut (i, a, ce1, ce2) ->
      fprintf fmt "cut (%a) (λ %a, %a) (λ %a, %a)"
        pcte a
        pri i pc ce1
        pri i pc ce2
  | ESplit (goal, a, b, i, c1, c2) ->
      fprintf fmt "split%s (%a) (%a) (λ %a, %a) (λ %a, %a) %a" (rstr goal)
        pcte a
        pcte b
        pri i pc c1
        pri i pc c2
        pri i
  | EUnfoldIff (goal, a, b, i, c) ->
      fprintf fmt "unfold_iff%s (%a) (%a) (λ %a, %a) %a" (rstr goal)
        pcte a
        pcte b
        pri i pc c
        pri i
  | EUnfoldArr (goal, a, b, i, c) ->
      fprintf fmt "unfold_arr%s (%a) (%a) (λ %a, %a) %a" (rstr goal)
        pcte a
        pcte b
        pri i pc c
        pri i
  | ESwapNeg (goal, a, i, c) ->
      fprintf fmt "swap_neg%s (%a) (λ %a, %a) %a" (rstr goal)
        pcte a
        pri i pc c
        pri i
  | ESwap (goal, a, i, c) ->
      fprintf fmt "swap%s (%a) (λ %a, %a) %a" (rstr goal)
        pcte a
        pri i pc c
        pri i
  | EDestruct (goal, a, b, i, j1, j2, c) ->
      fprintf fmt "destruct%s (%a) (%a) (λ %a %a, %a) %a" (rstr goal)
        pcte a
        pcte b
        pri j1 pri j2 pc c
        pri i
  | EWeakening (goal, a, i, c) ->
      fprintf fmt "weakening%s (%a) (%a) %a" (rstr goal)
        pcte a
        pc c
        pri i
  | EIntroQuant (goal, p, i, y, c) ->
      fprintf fmt "intro_quant%s (%a) (λ %a %a, %a) %a" (rstr goal)
        pcte p
        pri y pri i pc c
        pri i
  | EInstQuant (goal, p, i, j, t, c) ->
      fprintf fmt "inst_quant%s (%a) (%a) (λ %a %a, %a) %a" (rstr goal)
        pcte p
        pcte t
        pri i pri j pc c
        pri i
  | ERewrite _ -> verif_failed "Rewrite is not yet supported by the Lambdapi checker" in
  pc fmt c

let fv_ts (cta : ctask) =
  let encode_neg (k, (ct, pos)) = k, if pos then CTnot ct else ct in
  let fv = Mid.bindings cta.sigma in
  let ts = Mid.bindings cta.gamma_delta
           |> List.map encode_neg in
  fv, ts

let print fmt init_ct res_ct (task_id, certif) =
  let res = List.map fv_ts res_ct in
  let init = fv_ts init_ct in
  (* The type we need to check is inhabited *)
  let p_type fmt () =
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " →@ ")
      print_task fmt (res @ [init]) in
  (* applied_tasks are used to fill the holes *)
  let applied_tasks =
    List.map2 (fun id (fv_t, t) ->
        let fv, _ = List.split fv_t in
        let hyp, _ = List.split t in
        print_list_inter " " pri str_formatter (id :: fv @ hyp);
        flush_str_formatter ())
      task_id
      res in
  (* The term that has the correct type *)
  let p_term fmt () =
    let fv, ts = init in
    let fv_ids, _ = List.split fv in
    let hyp_ids, _ = List.split ts in
    let vars = task_id @ fv_ids @ hyp_ids in
    fprintf fmt "λ %a, " (print_list_inter " " pri) vars;
    print_certif applied_tasks fmt certif in

  fprintf fmt "@[<v 0>definition to_verify :@    \
               @[<v 0>%a@]@ \
               ≔  %a@]@."
    p_type ()
    p_term ()

let checker_lambdapi certif init_ct res_ct =
  try
    let oc = open_out "/tmp/check_line.lp" in
    let fmt = formatter_of_out_channel oc in
    print fmt init_ct res_ct certif;
    close_out oc;
    let coc = Filename.(concat Config.datadir (concat "lambdapi" "CoC.lp")) in
    let pkg_conf = Filename.(concat Config.datadir (concat "lambdapi" "lambdapi.pkg")) in
    Sys.command ("cat " ^ coc ^ " > /tmp/check_all.lp") |> ignore;
    Sys.command "cat /tmp/check_line.lp >> /tmp/check_all.lp" |> ignore;
    Sys.command ("cp " ^ pkg_conf ^ " /tmp/lambdapi.pkg") |> ignore;
    let ret = Sys.command "lambdapi check /tmp/check_all.lp 2> /dev/null 1> /dev/null" in
    if ret <> 0 then verif_failed "Not verified by Lambdapi"
  with e -> raise (Trans.TransFailure ("Cert_verif_lambdapi.checker_lambdapi", e))
