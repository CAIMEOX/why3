open Why3

open Ident
open Term (* only for binop *)

open Cert_syntax
open Cert_certificates

(* To collect tasks with their names *)
let union estr =
  let merge_no_conflicts id cta1 cta2 =
    if ctask_equal cta1 cta2
    then Some cta1
    else (* Important : gives an error and not None *)
      let open Format in
      eprintf "@[<v>Conflict on ident: %a@ \
               Shown when checking: %s@ \
               task 1: %a@ \
               task 2: %a@]@."
        prhyp id
        estr
        pcta cta1
        pcta cta2;
      verif_failed "Conflict of ident, see stderr" in
  Mid.union merge_no_conflicts

exception Found

(* This is the main verification function : <ccheck> replays the certificate on
   a ctask *)
let rec ccheck c cta =
  match c with
  | EConstruct _ | EDuplicate _
  | EFoldArr _ | EFoldIff _ | EEqSym _ | EEqTrans _ ->
      verif_failed "Construct/Duplicate/Fold/Eq/Let left"
  | EHole i -> Mid.singleton i cta
  | EAxiom (_, i1, i2) ->
      let t1, pos1 = find_ident "axiom1" i1 cta in
      let t2, pos2 = find_ident "axiom2" i2 cta in
      if not pos1 && pos2
      then if ct_equal t1 t2 then Mid.empty
           else begin
               Format.eprintf "@[<v>t1: %a@ \
                               t2: %a@]@."
                 pcte t1
                 pcte t2;
               verif_failed "The hypothesis and goal given do not match"
             end
      else verif_failed "Terms have wrong positivities in the task"
  | ETrivial (_, i) ->
      let t, pos = find_ident "trivial" i cta in
      begin match t, pos with
      | CTfalse, false | CTtrue, true -> Mid.empty
      | _ -> verif_failed "Non trivial hypothesis"
      end
  | EEqRefl (_, _, i) ->
      let t, pos = find_ident "eqrefl" i cta in
      begin match t, pos with
      | CTapp (CTapp (e, t1), t2), _ when ct_equal t1 t2 && ct_equal e eq ->
          Mid.empty
      | _ -> verif_failed "Non eqrefl hypothesis" end
  | EAssert (i, a, c1, c2) ->
      infers_into ~e_str:"EAssert" cta a CTprop;
      let cta1 = add i (a, true) cta in
      let cta2 = add i (a, false) cta in
      union "assert" (ccheck c1 cta1) (ccheck c2 cta2)
  | ESplit (_, _, _, i, c1, c2) ->
      let t, pos = find_ident "split" i cta in
      begin match t, pos with
      | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
          let cta1 = add i (t1, pos) cta in
          let cta2 = add i (t2, pos) cta in
          union "split" (ccheck c1 cta1) (ccheck c2 cta2)
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
  | EClear (_, _, i, c) ->
      let cta = remove i cta in
      ccheck c cta
  | EIntroQuant (_, _, i, y, c) ->
      let t, pos = find_ident "intro_quant" i cta in
      begin match t, pos with
      | CTquant (CTforall, cty, t), true | CTquant (CTexists, cty, t), false ->
          if (* TODO : check that y does not appear in cta, maybe with:
                Mid.mem y cta.sigma || *)
            mem y t
          then begin
              Format.eprintf "@[<v>TASK@ %a@ \
                       i : %a@ \
                       y : %a@]@."
                pcta cta
                prhyp i
                prid y;
              verif_failed "non-free variable"
            end
          else let cta = add i (ct_open t (CTfvar y), pos) cta
                         |> add_var y cty in
               ccheck c cta
      | _ -> verif_failed "Nothing to introduce" end
  | EInstQuant (_, _, i, j, t_inst, c) ->
      let t, pos = find_ident "inst_quant" i cta in
      begin match t, pos with
      | CTquant (CTforall, ty, t), false | CTquant (CTexists, ty, t), true ->
          infers_into ~e_str:"EInstquant" cta t_inst ty;
          let cta = add j (ct_open t t_inst, pos) cta in
          ccheck c cta
      | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
      end
  | ERewrite (_, is_eq, _, _, _, ctxt, i1, i2, c) ->
      let a, b = match find_ident "rew" i1 cta, is_eq with
        | (CTbinop (Tiff, a, b), false), false -> a, b
        | (CTapp (CTapp (f, a), b), false), true when ct_equal f eq -> a, b
        | _ -> verif_failed "Non-rewritable proposition" in
      let t, pos = find_ident "rew" i2 cta in
      assert (ct_equal t (instantiate_safe cta ctxt a));
      let cta =  add i2 (instantiate ctxt b, pos) cta in
      ccheck c cta
  | EInduction (g, hi1, hi2, hr, ix, a, ctxt, c1, c2) ->
      let le = CTfvar (cta.get_ident le_str) in
      let lt = CTfvar (cta.get_ident lt_str) in
      let t, pos = find_ident "induction" g cta in
      let x = CTfvar ix in
      let has_ident_cta i cta =
        let rec found_ident_term i t = match t with
          | CTfvar i' when id_equal i i' -> raise Found
          | _ -> ct_map (found_ident_term i) t in
        try Mid.map (fun (t, _) -> found_ident_term i t)
              (remove g cta).gamma_delta |> ignore; false
        with Found -> true in
      (* check that we are in the case of application and that we preserve
         typing *)
      infers_into ~e_str:"EInduction, var" cta x ctint;
      infers_into ~e_str:"EInduction, bound" cta a ctint;
      assert (ct_equal t (instantiate_safe cta ctxt x));
      assert (not (has_ident_cta ix cta) && pos);
      let cta1 = add hi1 (CTapp (CTapp (le, x), a), false) cta in
      let idn = id_register (id_fresh "ctxt_var") in
      let n = CTfvar idn in
      let cta2 = add hi2 (CTapp (CTapp (lt, a), x), false) cta
                 |> add hr (CTquant (CTforall, ctint, ct_close idn (
                            CTbinop (Timplies, CTapp (CTapp (lt, n), x),
                                     instantiate ctxt n))), false) in
      union "induction" (ccheck c1 cta1) (ccheck c2 cta2)

let checker_caml (vs, certif) init_ct res_ct =
  try let map_cert = ccheck certif init_ct in
      let map_trans = Mid.of_list (List.combine vs res_ct) in
      if not (Mid.equal ctask_equal map_cert map_trans)
      then begin
          let res_ct' = Mid.values map_cert in
          print_ctasks "/tmp/from_trans.log" res_ct;
          print_ctasks "/tmp/from_cert.log" res_ct';
          verif_failed "Replaying certif gives different result, log available"
        end
  with e -> raise (Trans.TransFailure ("checker_caml", e))
