open Why3

open Ident
open Term (* only for binop *)

open Cert_abstract
open Cert_certificates


(** Utility verification functions *)




let rec check_rewrite_term tl tr t path =
  (* returns <t> where the instance at <path> of <tl> is replaced by <tr> *)
  match path, t with
  | [], t when cterm_equal t tl -> tr
  | Left::prest, CTbinop (op, t1, t2) ->
      let t1' = check_rewrite_term tl tr t1 prest in
      CTbinop (op, t1', t2)
  | Right::prest, CTbinop (op, t1, t2) ->
      let t2' = check_rewrite_term tl tr t2 prest in
      CTbinop (op, t1, t2')
  | _ -> verif_failed "Can't follow the rewrite path"

let check_rewrite cta rev h g terms path : ctask list =
  let rec introduce acc inst_terms t = match t, inst_terms with
    | CTbinop (Timplies, t1, t2), _ -> introduce (t1::acc) inst_terms t2
    | CTquant (CTforall, t), inst::inst_terms -> introduce acc inst_terms (ct_open t inst)
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

let rec ccheck (c : core_certif) cta : ctask list =
  match c with
    | Nc ->
        verif_failed "No certificates for this case"
    | Let _ -> verif_failed "Some Let left"
    | Hole -> [cta]
    | Axiom (h, g) ->
        let th, posh = find_ident "axiom1" h cta in
        let tg, posg = find_ident "axiom2" g cta in
        if not posh && posg
        then if cterm_equal th tg
             then []
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | Trivial i ->
        let t, pos = find_ident "trivial" i cta in
        begin match t, pos with
        | CTfalse, false | CTtrue, true -> []
        | _ -> verif_failed "Non trivial hypothesis"
        end
    | Cut (i, a, c1, c2) ->
        let cta1 = Mid.add i (a, true) cta in
        let cta2 = Mid.add i (a, false) cta in
        ccheck c1 cta1 @ ccheck c2 cta2
    | Split (i, c1, c2) ->
        let t, pos = find_ident "split" i cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
            let cta1 = Mid.add i (t1, pos) cta in
            let cta2 = Mid.add i (t2, pos) cta in
            ccheck c1 cta1 @ ccheck c2 cta2
        | _ -> verif_failed "Not splittable" end
    | Unfold (i, c) ->
        let t, pos = find_ident "unfold" i cta in
        begin match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            let cta = Mid.add i unfolded_iff cta in
            ccheck c cta
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            let cta = Mid.add i unfolded_imp cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | Swap_neg (i, c) ->
        let t, pos = find_ident "swap_neg" i cta in
        let neg_t = match t with CTnot t -> t | t -> CTnot t in
        let cta = Mid.add i (neg_t, not pos) cta in
        ccheck c cta
    | Destruct (i, j1, j2, c) ->
        let t, pos = find_ident "destruct" i cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
            let cta = Mid.remove i cta
                      |> Mid.add j1 (t1, pos)
                      |> Mid.add j2 (t2, pos) in
            ccheck c cta
        | _ -> verif_failed "Nothing to destruct" end
    (* | Construct (i1, i2, j, c) ->
     *     let a, pos1 = find_ident "construct1" i1 cta in
     *     let b, pos2 = find_ident "construct2" i2 cta in
     *     if pos1 = pos2
     *     then
     *       let t = if pos1 then CTbinop (Tor, a, b) else CTbinop (Tand, a, b) in
     *       let cta = Mid.remove i1 cta
     *                 |> Mid.remove i2
     *                 |> Mid.add j (t, pos1) in
     *       ccheck c cta
     *     else verif_failed "Can't construct" *)
    | Weakening (i, c) ->
        let cta = Mid.remove i cta in
        ccheck c cta
    | Intro_quant (i, y, c) ->
        let t, pos = find_ident "intro_quant" i cta in
        begin match t, pos with
        | CTquant (CTforall, t), true | CTquant (CTexists, t), false ->
            if mem y t then verif_failed "non-free variable" else
            let cta = Mid.add i (ct_open t (CTfvar y), pos) cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to introduce" end
    | Inst_quant (i, j, t_inst, c) ->
        let t, pos = find_ident "inst_quant" i cta in
        begin match t, pos with
        | CTquant (CTforall, t), false | CTquant (CTexists, t), true ->
            let cta = Mid.add j (ct_open t t_inst, pos) cta in
            ccheck c cta
        | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
        end
    | Rewrite (i, j, path, rev, lc) ->
        let lcta = check_rewrite cta rev j i [] path in
        List.map2 ccheck lc lcta |> List.concat


let checker_caml certif init_ct res_ct =
  try let res_ct' = ccheck certif init_ct in
      if not (Lists.equal ctask_equal res_ct res_ct')
      then begin
          print_ctasks "/tmp/from_trans.log" res_ct;
          print_ctasks "/tmp/from_cert.log"  res_ct';
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_verif_caml.checker_caml", e))
