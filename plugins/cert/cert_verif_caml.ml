open Why3
open Ident
open Term (* only for binop *)

open Cert_syntax
open Cert_certificates

(* This is the main verification function : <ccheck> replays the certificate on
   a ctask *)
let rec ccheck c cta =
  match c with
  | KDuplicate _ | KFoldArr _
  | KFoldIff _  | KSwapNegate _| KEqSym _ | KEqTrans _ ->
      verif_failed "Construct/Duplicate/Fold/SwapNeg/Eq/Let left"
  | KReduce _ ->
      verif_failed "Reduce is not implemented in the OCaml checker yet"
  | KHole cta' -> if not (ctask_equal cta cta')
                  then begin
                      Format.eprintf "@[<v>Conflict of tasks: @ \
                                      Actual task: %a@ \
                                      Certif task: %a@]@."
                        pacta cta'
                        pacta cta;
                      verif_failed "Tasks differ, look at std_err" end
  | KClear (_, _, i, c) ->
      let cta = remove i cta in
      ccheck c cta
  | KForget (i, c) ->
      assert (not (has_ident_context i cta.gamma_delta));
      let cta = remove_var i cta in
      ccheck c cta
  | KAxiom (_, i1, i2) ->
      let t1, pos1 = find_formula "axiom1" i1 cta in
      let t2, pos2 = find_formula "axiom2" i2 cta in
      if not pos1 && pos2
      then (if not (ct_equal t1 t2)
            then begin
                Format.eprintf "@[<v>t1: %a@ \
                                t2: %a@]@."
                  pcte t1
                  pcte t2;
                verif_failed "The hypothesis and goal given do not match"
              end)
      else verif_failed "Terms have wrong positivities in the task"
  | KTrivial (_, i) ->
      let t, pos = find_formula "trivial" i cta in
      begin match t, pos with
      | CTfalse, false | CTtrue, true -> ()
      | _ -> verif_failed "Non trivial hypothesis"
      end
  | KEqRefl (cty, _, i) ->
      let t, pos = find_formula "eqrefl" i cta in
      begin match t, pos with
      | CTapp (CTapp (e, t1), t2), true
          when ct_equal t1 t2 && ct_equal e (eq cty) -> ()
      | _ -> verif_failed "Non eqrefl goal" end
  | KAssert (i, a, c1, c2) ->
      infers_into ~e_str:"KAssert" cta a CTprop;
      let cta1 = add i (a, true) cta in
      let cta2 = add i (a, false) cta in
      ccheck c1 cta1; ccheck c2 cta2
  | KSplit (_, _, _, i, c1, c2) ->
      let t, pos = find_formula "split" i cta in
      begin match t, pos with
      | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
          let cta1 = add i (t1, pos) cta in
          let cta2 = add i (t2, pos) cta in
          ccheck c1 cta1; ccheck c2 cta2
      | _ -> verif_failed "Not splittable" end
  | KUnfoldIff (_, _, _, i, c) ->
      let t, pos = find_formula "unfold" i cta in
      begin match t with
      | CTbinop (Tiff, t1, t2) ->
          let imp_pos = CTbinop (Timplies, t1, t2) in
          let imp_neg = CTbinop (Timplies, t2, t1) in
          let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
          let cta = add i unfolded_iff cta in
          ccheck c cta
      | _ -> verif_failed "Nothing to unfold" end
  | KUnfoldArr (_, _, _, i, c) ->
      let t, pos = find_formula "unfold" i cta in
      begin match t with
      | CTbinop (Timplies, t1, t2) ->
          let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
          let cta = add i unfolded_imp cta in
          ccheck c cta
      | _ -> verif_failed "Nothing to unfold" end
  | KSwap (_, _, i, c) ->
      let t, pos = find_formula "Swap" i cta in
      begin match t with
      | CTnot t ->
          let cta = add i (t, not pos) cta in
          ccheck c cta
      | _ -> verif_failed "Not a negation"
      end
  | KDestruct (_, _, _, i, j1, j2, c) ->
      let t, pos = find_formula "destruct" i cta in
      begin match t, pos with
      | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
          let cta = remove i cta
                    |> add j1 (t1, pos)
                    |> add j2 (t2, pos) in
          ccheck c cta
      | _ -> verif_failed "Nothing to destruct" end
  | KIntroQuant (_, _, _, i, y, c) ->
      let t, pos = find_formula "intro_quant" i cta in
      begin match t, pos with
      | CTquant (CTforall, cty, t), true
      | CTquant (CTexists, cty, t), false ->
          if Mid.mem y cta.sigma
          then begin
              Format.eprintf "@[<v>i : %a@ \
                              y : %a@ \
                              TASK@ %a@]@."
                prhyp i
                prid y
                pacta cta;
              verif_failed "non-free variable"
            end
          else let cta = add i (ct_open t (CTfvar (y, [])), pos) cta
                         |> add_var y cty in
               ccheck c cta
      | _ -> verif_failed "Nothing to introduce" end
  | KInstQuant (_, _, _, i, j, t_inst, c) ->
      let t, pos = find_formula "inst_quant" i cta in
      begin match t, pos with
      | CTquant (CTforall, ty, t), false | CTquant (CTexists, ty, t), true ->
          infers_into ~e_str:"KInstquant" cta t_inst ty;
          let cta = add j (ct_open t t_inst, pos) cta in
          ccheck c cta
      | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
      end
  | KRewrite (_, is_eq, cty, _, _, ctxt, i1, i2, c) ->
      let a, b = match find_formula "rew" i1 cta, is_eq with
        | (CTbinop (Tiff, a, b), false), Some _ -> a, b
        | (CTapp (CTapp (f, a), b), false), None when ct_equal f (eq cty) -> a, b
        | _ -> verif_failed "Non-rewritable proposition" in
      let t, pos = find_formula "rew" i2 cta in
      assert (ct_equal t (instantiate_safe cta ctxt a));
      let cta =  add i2 (instantiate ctxt b, pos) cta in
      ccheck c cta
  | KInduction (g, hi1, hi2, hr, x, a, ctxt, c1, c2) ->
      let le = CTfvar ((cta.get_ls le_str).ls_name, []) in
      let lt = CTfvar ((cta.get_ls lt_str).ls_name, []) in
      let t, pos = find_formula "induction" g cta in
      let ix =  match x with CTfvar (ix, _) -> ix | _ -> assert false in
       (* check that we are in the case of application and that we preserve
         typing *)
      infers_into ~e_str:"KInduction, var" cta x ctint;
      infers_into ~e_str:"KInduction, bound" cta a ctint;
      assert (ct_equal t (instantiate_safe cta ctxt x));
      assert (not (has_ident_context ix (remove g cta).gamma_delta) && pos);
      let cta1 = add hi1 (CTapp (CTapp (le, x), a), false) cta in
      let idn = id_register (id_fresh "ctxt_var") in
      let n = CTfvar (idn, []) in
      let cta2 = add hi2 (CTapp (CTapp (lt, a), x), false) cta
                 |> add hr (CTquant (CTforall, ctint, ct_close idn (
                            CTbinop (Timplies, CTapp (CTapp (lt, n), x),
                                     instantiate ctxt n))), false) in
      ccheck c1 cta1; ccheck c2 cta2

let checker_caml kc init_ct _res_ct =
  try ccheck kc init_ct
  with e -> raise (Trans.TransFailure ("checker_caml", e))
