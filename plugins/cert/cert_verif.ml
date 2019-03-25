open Why3
open Ident
open Cert_syntax


(** Utility functions on <cterm> and <ctask> *)

let rec cterm_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> Ident.id_equal i1 i2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTforall t1, CTforall t2 -> cterm_equal t1 t2
  | _ -> false

let cterm_pos_equal (t1, p1) (t2, p2) =
  cterm_equal t1 t2 && p1 = p2

let ctask_equal cta1 cta2 = Mid.equal cterm_pos_equal cta1 cta2

let rec noskip (r, _) = (* checks if the transformation closes the task *)
  match r with
  | Skip -> false
  | Axiom _ -> true
  | Split (c1, c2) -> noskip c1 && noskip c2
  | Unfold c
  | Destruct (_, _, c)
  | Dir (_, c)
  | Weakening c
  | Intro (_, c) -> noskip c
  | Rewrite (_, _, _, lc) -> List.for_all noskip lc

let split_cta cta = (* separates hypotheses and goals *)
  let open Mid in
  fold (fun h (ct, pos) (mh, mg) ->
      if pos then mh, add h (ct, pos) mg
      else add h (ct, pos) mh, mg)
    cta (empty, empty)

let set_goal : ctask -> cterm -> ctask = fun cta ->
  (* creates a new ctask with the same hypotheses but sets the goal with the second argument *)
  let mh, mg = split_cta cta in
  let hg, _ = Mid.choose mg in
  fun ct -> Mid.add hg (ct, true) mh


(** Utility verification functions *)

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

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

let check_rewrite cta rev h g path : ctask list =
  let rec introduce acc = function
    | CTbinop (CTimplies, t1, t2) -> introduce (t1::acc) t2
    | t -> acc, t in
  let lp, tl, tr =
    let ct, pos = find_ident h cta in
    if pos then verif_failed "Can't use goal as an hypothesis to rewrite" else
      match introduce [] ct with
      | lp, CTbinop (CTiff, t1, t2) -> if rev then lp, t1, t2 else lp, t2, t1
      | _ -> verif_failed "Can't find the hypothesis used to rewrite" in
  let rewrite_decl h (te, pos) =
    if id_equal h g
    then check_rewrite_term tl tr te path, pos
    else te, pos in
  Mid.mapi rewrite_decl cta :: List.map (set_goal cta) lp
  (* To check a rewriting rule, you need to :
       • check the rewritten task
       • check every premisses of rewritten equality in the current context
   *)


(** This is the main verification function : <check_certif> replays the certificate on a ctask *)

let rec check_certif cta (r, g : certif) : ctask list =
  match r with
    | Skip -> [cta]
    | Axiom h ->
        let th, posh = find_ident h cta in
        let tw, posw = find_ident g cta in
        if not posh && posw
        then if cterm_equal th tw
             then []
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | Split (c1, c2) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTbinop (CTand, t1, t2), true | CTbinop (CTor, t1, t2), false ->
            let cta1 = Mid.add g (t1, pos) cta in
            let cta2 = Mid.add g (t2, pos) cta in
            check_certif cta1 c1 @ check_certif cta2 c2
        | _ -> verif_failed "Not splittable" end
    | Unfold c ->
        let t, pos = find_ident g cta in
        begin match t with
        | CTbinop (CTiff, t1, t2) ->
            let imp_pos = CTbinop (CTimplies, t1, t2) in
            let imp_neg = CTbinop (CTimplies, t2, t1) in
            let destruct_iff = CTbinop (CTand, imp_pos, imp_neg), pos in
            let cta = Mid.add g destruct_iff cta in
            check_certif cta c
        | _ -> verif_failed "Not decodable" end
    | Destruct (h1, h2, c) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTbinop (CTand, t1, t2), false | CTbinop (CTor, t1, t2), true ->
            let cta = Mid.remove g cta
                      |> Mid.add h1 (t1, pos)
                      |> Mid.add h2 (t2, pos) in
            check_certif cta c
        | _ -> verif_failed "Not destructible"  end
    | Dir (d, c) ->
        let t, pos = find_ident g cta in
        begin match t, d, pos with
        | CTbinop (CTor, t, _), Left, true | CTbinop (CTor, _, t), Right, true
        | CTbinop (CTand, t, _), Left, false | CTbinop (CTand, _, t), Right, false ->
          let cta = Mid.add g (t, pos) cta in
          check_certif cta c
        | _ -> verif_failed "Can't follow a direction" end
    | Intro (h, c) ->
        let t, pos = find_ident g cta in
        begin match t, pos with
        | CTbinop (CTimplies, f1, f2), true ->
            let cta = Mid.add h (f1, false) cta
                      |> Mid.add g (f2, true) in
            check_certif cta c
        | _ -> verif_failed "Nothing to introduce" end
    | Weakening c ->
        let cta = Mid.remove g cta in
        check_certif cta c
    | Rewrite (h, path, rev, lc) ->
        let lcta = check_rewrite cta rev h g path in
        List.map2 check_certif lcta lc |> List.concat
