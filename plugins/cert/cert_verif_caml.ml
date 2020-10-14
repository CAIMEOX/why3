open Why3

open Ident
open Term (* only for binop *)

open Cert_abstract
open Cert_certificates


(** Utility verification functions *)



(** This is the main verification function : <check_certif> replays the certificate on a ctask *)

let union : ctask Mid.t -> ctask Mid.t -> ctask Mid.t =
  let merge_no_conflicts id cta1 cta2 =
    if ctask_equal cta1 cta2
    then Some cta1
    else (* Important : gives an error and not None *)
      let open Format in
      eprintf "Conflict on ident : %a\n\
               task 1 : %a\n\
               task 2 : %a@."
        pri id
        pcta cta1
        pcta cta2;
      verif_failed "Conflict of ident, see stderr" in
  Mid.union merge_no_conflicts

let rec ccheck c cta =
  match c with
  | ELet _ | EConstruct _ | ERename _ | EFoldArr _ ->
      verif_failed "Construct/Let/Rename/Fold left"
    | EHole i -> Mid.singleton i cta
    | EAxiom (_, i1, i2) ->
        let t1, pos1 = find_ident "axiom1" i1 cta in
        let t2, pos2 = find_ident "axiom2" i2 cta in
        if not pos1 && pos2
        then if cterm_equal t1 t2 then Mid.empty
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | ETrivial (_, i) ->
        let t, pos = find_ident "trivial" i cta in
        begin match t, pos with
        | CTfalse, false | CTtrue, true -> Mid.empty
        | _ -> verif_failed "Non trivial hypothesis"
        end
    | ECut (i, a, c1, c2) ->
        let cta1 = add i (a, true) cta in
        let cta2 = add i (a, false) cta in
        union (ccheck c1 cta1) (ccheck c2 cta2)
    | ESplit (_, _, _, i, c1, c2) ->
        let t, pos = find_ident "split" i cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
            let cta1 = add i (t1, pos) cta in
            let cta2 = add i (t2, pos) cta in
            union (ccheck c1 cta1) (ccheck c2 cta2)
        | _ -> verif_failed "Not splittable" end
    | EUnfoldIff (_, _, _, i, c) ->
        let t, pos = find_ident "unfold" i cta in
        begin match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            let cta = add i unfolded_iff cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | EUnfoldArr (_, _, _, i, c) ->
        let t, pos = find_ident "unfold" i cta in
        begin match t with
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            let cta = add i unfolded_imp cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | ESwap (_, _, i, c) | ESwapNeg (_, _, i, c) ->
        let t, pos = find_ident "Swap" i cta in
        let neg_t = match t with CTnot t -> t | _ -> CTnot t in
        let cta = add i (neg_t, not pos) cta in
        ccheck c cta
    | EDestruct (_, _, _, i, j1, j2, c) ->
        let t, pos = find_ident "destruct" i cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
            let cta = remove i cta
                      |> add j1 (t1, pos)
                      |> add j2 (t2, pos) in
            ccheck c cta
        | _ -> verif_failed "Nothing to destruct" end
    | EWeakening (_, _, i, c) ->
        let cta = remove i cta in
        ccheck c cta
    | EIntroQuant (_, _, i, y, c) ->
        let t, pos = find_ident "intro_quant" i cta in
        begin match t, pos with
        | CTquant (CTforall, cty, t), true | CTquant (CTexists, cty, t), false ->
            if Mid.mem y cta.sigma || mem y t
            then verif_failed "non-free variable"
            else let cta = add i (ct_open t (CTfvar y), pos) cta
                           |> add_var y cty in
                 ccheck c cta
        | _ -> verif_failed "Nothing to introduce" end
    | EInstQuant (_, _, i, j, t_inst, c) ->
        let t, pos = find_ident "inst_quant" i cta in
        begin match t, pos with
        | CTquant (CTforall, ty, t), false | CTquant (CTexists, ty, t), true ->
            infers_into cta.sigma t_inst ty;
            let cta = add j (ct_open t t_inst, pos) cta in
            ccheck c cta
        | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
        end
    | ERewrite (i, h, ctxt, c) ->
        let t, pos = find_ident "inst_quant" h cta in
        begin match t, pos with
        | CTbinop (Tiff, a, b), false ->
            let cta = rewrite_ctask cta i a b ctxt in
            ccheck c cta
        | _ -> verif_failed "Non-rewritable proposition"
        end

let checker_caml (vs, certif) init_ct res_ct =
  try let map_cert = ccheck certif init_ct in
      let map_trans = Mid.of_list (List.combine vs res_ct) in
      if not (Mid.equal ctask_equal map_cert map_trans)
      then begin
          let res_ct' = Mid.values map_cert in
          print_ctasks "/tmp/from_trans.log" res_ct;
          print_ctasks "/tmp/from_cert.log" res_ct';
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_verif_caml.checker_caml", e))
