open Why3

open Ident
open Term (* only for binop *)
open Cert_syntax



(** Utility verification functions *)


let find_ident h cta =
  match Mid.find_opt h cta with
  | Some x -> x
  | None -> verif_failed "Can't find ident in the task"

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
    let ct, pos = find_ident h cta in
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

let rec ccheck (r, g : certif) cta : ctask list =
  Format.eprintf "i@.";
  match r with
    | Hole -> [cta]
    | Axiom h ->
        let th, posh = find_ident h cta in
        let tg, posg = find_ident g cta in
        if not posh && posg
        then if cterm_equal th tg
             then []
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | Trivial ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTfalse, false | CTtrue, true -> []
        | _ -> verif_failed "Non trivial hypothesis"
        end
    | Cut (a, c1, c2) ->
        let cta1 = Mid.add g (a, true) cta in
        let cta2 = Mid.add g (a, false) cta in
        ccheck c1 cta1 @ ccheck c2 cta2
    | Split (c1, c2) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
            let cta1 = Mid.add g (t1, pos) cta in
            let cta2 = Mid.add g (t2, pos) cta in
            ccheck c1 cta1 @ ccheck c2 cta2
        | _ -> verif_failed "Not splittable" end
    | Unfold c ->
        let t, pos = find_ident g cta in
        begin match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            let cta = Mid.add g unfolded_iff cta in
            ccheck c cta
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            let cta = Mid.add g unfolded_imp cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to unfold" end
    | Swap_neg c ->
        let t, pos = find_ident g cta in
        let neg_t = match t with CTnot t -> t | t -> CTnot t in
        let cta = Mid.add g (neg_t, not pos) cta in
        ccheck c cta
    | Destruct (h1, h2, c) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
            let cta = Mid.remove g cta
                      |> Mid.add h1 (t1, pos)
                      |> Mid.add h2 (t2, pos) in
            ccheck c cta
        | _ -> verif_failed "Nothing to destruct"  end
    | Weakening c ->
        let cta = Mid.remove g cta in
        ccheck c cta
    | Intro_quant (h, c) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTquant (CTforall, t), true | CTquant (CTexists, t), false ->
            if mem h t then verif_failed "non-free variable" else
            let cta = Mid.add g (ct_open t (CTfvar h), pos) cta in
            ccheck c cta
        | _ -> verif_failed "Nothing to introduce" end
    | Inst_quant (h, t_inst, c) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTquant (CTforall, t), false | CTquant (CTexists, t), true ->
            let cta = Mid.add h (ct_open t t_inst, pos) cta in
            ccheck c cta
        | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
        end
    | Rewrite (h, path, rev, lc) ->
        let lcta = check_rewrite cta rev h g [] path in
        List.map2 ccheck lc lcta |> List.concat


let checker_caml certif init_t res_t =
  try let init_ct = translate_task init_t in
      let res_ct  = List.map translate_task res_t in
      let res_ct' = ccheck certif init_ct in
      if Lists.equal ctask_equal res_ct res_ct'
      then res_t
      else begin
          print_ctasks "/tmp/from_trans.log" res_ct;
          print_ctasks "/tmp/from_cert.log"  res_ct';
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_ctrans", e))
