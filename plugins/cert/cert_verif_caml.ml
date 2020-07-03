open Why3

open Ident
open Term (* only for binop *)

open Cert_abstract
open Cert_certificates


(** Utility verification functions *)




let rec check_rewrite_term tl (tr : cterm) (t : cterm) path =
  (* returns <t> where the instance at <path> of <tl> is replaced by <tr> *)
  match path, t with
  | [], t when cterm_equal t tl -> tr
  | Left::prest, { ct_node = CTbinop (op, t1, t2) } ->
      let t1' = check_rewrite_term tl tr t1 prest in
      add_ty CTprop (CTbinop (op, t1', t2))
  | Right::prest, { ct_node = CTbinop (op, t1, t2) } ->
      let t2' = check_rewrite_term tl tr t2 prest in
      add_ty CTprop (CTbinop (op, t1, t2'))
  | _ -> verif_failed "Can't follow the rewrite path"

let check_rewrite (cta : ctask) rev h g (terms : cterm list) path : ctask list =
  let rec introduce acc (inst_terms : cterm list) (t : cterm) = match t.ct_node, inst_terms with
    | CTbinop (Timplies, t1, t2), _ -> introduce (t1::acc) inst_terms t2
    | CTquant (CTforall, t), inst::inst_terms -> introduce acc inst_terms (ct_open t inst.ct_node)
    | t, [] -> acc, t
    | _ -> verif_failed "Can't instantiate the hypothesis" in
  let lp, tl, tr =
    let ct, pos = find_ident "check_rewrite" h cta in
    if pos then verif_failed "Can't use goal as an hypothesis to rewrite" else
      match introduce [] terms ct with
      | lp, CTbinop (Tiff, t1, t2) -> if rev then lp, t1, t2 else lp, t2, t1
      | _ -> verif_failed "Can't find the hypothesis used to rewrite" in
  let rewrite_decl h (te, pos) =
    if id_equal h g
    then check_rewrite_term tl tr te path, pos
    else te, pos in
  Mid.mapi rewrite_decl cta :: List.map (set_goal cta) lp
  (* To check a rewriting rule, you need to :
       • check the rewritten task
       • check every premises of rewritten equality in the current context
   *)


(** This is the main verification function : <check_certif> replays the certificate on a ctask *)

let union : ctask Mid.t -> ctask Mid.t -> ctask Mid.t =
  let merge_no_conflicts id cta1 cta2 =
    if ctask_equal cta1 cta2
    then Some cta1
    else (* Important : gives an error and not None *)
      let open Format in
      eprintf "Conflict on ident : %a\n\
               task 1 : %a\n\
               task 2 : %a\n"
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
        begin match t.ct_node, pos with
        | CTfalse, false | CTtrue, true -> Mid.empty
        | _ -> verif_failed "Non trivial hypothesis"
        end
    | ECut (i, a, c1, c2) ->
        let cta1 = Mid.add i (a, true) cta in
        let cta2 = Mid.add i (a, false) cta in
        union (ccheck c1 cta1) (ccheck c2 cta2)
    | ESplit (_, _, _, i, c1, c2) ->
        let t, pos = find_ident "split" i cta in
        begin match t.ct_node, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
            let cta1 = Mid.add i (t1, pos) cta in
            let cta2 = Mid.add i (t2, pos) cta in
            union (ccheck c1 cta1) (ccheck c2 cta2)
        | _ -> verif_failed "Not splittable" end
    | EUnfoldIff (_, _, _, i, c) ->
        let t, pos = find_ident "unfold" i cta in
        begin match t.ct_node with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = add_ty CTprop (CTbinop (Timplies, t1, t2)) in
            let imp_neg = add_ty CTprop (CTbinop (Timplies, t2, t1)) in
            let unfolded_iff = add_ty CTprop (CTbinop (Tand, imp_pos, imp_neg)), pos in
            let cta = Mid.add i unfolded_iff cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | EUnfoldArr (_, _, _, i, c) ->
        let t, pos = find_ident "unfold" i cta in
        begin match t.ct_node with
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = add_ty CTprop (CTbinop (Tor, add_ty CTprop (CTnot t1), t2)), pos in
            let cta = Mid.add i unfolded_imp cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | ESwap (_, _, i, c) | ESwapNeg (_, _, i, c) ->
        let t, pos = find_ident "Swap" i cta in
        let neg_t = match t.ct_node with CTnot t -> t | _ -> add_ty CTprop (CTnot t) in
        let cta = Mid.add i (neg_t, not pos) cta in
        ccheck c cta
    | EDestruct (_, _, _, i, j1, j2, c) ->
        let t, pos = find_ident "destruct" i cta in
        begin match t.ct_node, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
            let cta = Mid.remove i cta
                      |> Mid.add j1 (t1, pos)
                      |> Mid.add j2 (t2, pos) in
            ccheck c cta
        | _ -> verif_failed "Nothing to destruct" end
    | EWeakening (_, _, i, c) ->
        let cta = Mid.remove i cta in
        ccheck c cta
    | EIntroQuant (_, _, i, y, c) ->
        let t, pos = find_ident "intro_quant" i cta in
        begin match t.ct_node, pos with
        | CTquant (CTforall, t), true | CTquant (CTexists, t), false ->
            if mem y t then verif_failed "non-free variable" else
              let cta = Mid.add i (ct_open t (CTfvar y), pos) cta in
              ccheck c cta
        | _ -> verif_failed "Nothing to introduce" end
    | EInstQuant (_, _, i, j, t_inst, c) ->
        let t, pos = find_ident "inst_quant" i cta in
        begin match t.ct_node, pos with
        | CTquant (CTforall, t), false | CTquant (CTexists, t), true ->
            let cta = Mid.add j (ct_open t t_inst.ct_node, pos) cta in
            ccheck c cta
        | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
        end
    | ERewrite (i, j, path, rev, lc) ->
        let lcta = check_rewrite cta rev j i [] path in
        List.map2 ccheck lc lcta |> List.fold_left union Mid.empty


let checker_caml (vs, certif) init_ct res_ct =
  try let map_res = ccheck certif init_ct in
      let res_ct' = List.map (fun id -> Mid.find id map_res) vs in
      if not (Lists.equal ctask_equal res_ct res_ct')
      then begin
          print_ctasks "/tmp/from_trans.log" res_ct;
          print_ctasks "/tmp/from_cert.log"  res_ct';
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_verif_caml.checker_caml", e))
