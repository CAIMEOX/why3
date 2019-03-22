open Why3
open Ident
open Term
open Decl
open Theory
open Task
open Generic_arg_trans_utils
open Format

type ident = Ident.ident

type binop = CTand | CTor | CTiff | CTimplies
type cterm = CTapp of ident
           | CTbinop of binop * cterm * cterm


type ctask = (cterm * bool) Mid.t

type dir = Left | Right
type path = dir list

type certif = rule * ident
(* The ident indicates where to apply the rule.
   In the following rules, we will call it <H> *)
(* Replaying a certif <c> against a list of ctask <l> will be denoted <c ⇓ l>,
   it (somewhat) corresponds to the function check_certif defined later *)

and rule =
  | Skip
  (* Skip ⇓ [Γ ⊢ Δ] ≜  [Γ ⊢ Δ] *)
  | Axiom of ident
  (* Axiom G ⇓ [Γ, G : P ⊢ Δ, H : P]  ≜  [] *)
  | Split of certif * certif
  (* Split (c₁, c₂) ⇓ [Γ, H : A ∨ B ⊢ Δ]  ≜  (c₁ ⇓ [Γ, H : A ⊢ Δ])  @  (c₂ ⇓ [Γ, H : B ⊢ Δ]) *)
  (* Split (c₁, c₂) ⇓ [Γ ⊢ Δ, H : A ∧ B]  ≜  (c₁ ⇓ [Γ ⊢ Δ, H : A])  @  (c₂ ⇓ [Γ ⊢ Δ, H : B]) *)
  | Unfold of certif
  (* Unfold c ⇓ [Γ, H : A ↔ B ⊢ Δ]  ≜  c ⇓ [Γ, H : (A → B) ∧ (B → A) ⊢ Δ] *)
  (* Unfold c ⇓ [Γ ⊢ Δ, H : A ↔ B]  ≜  c ⇓ [Γ ⊢ Δ, H : (A → B) ∧ (B → A)] *)
  | Destruct of certif * ident * ident
  (* Destruct (c, H₁, H₂) ⇓ [Γ, H : A ∧ B ⊢ Δ]  ≜  c ⇓ [Γ, H₁ : A, H₂ : B ⊢ Δ *)
  (* Destruct (c, H₁, H₂) ⇓ [Γ ⊢ Δ, H : A ∨ B]  ≜  c ⇓ [Γ ⊢ Δ, H₁ : A, H₂ : B *)
  | Dir of dir * certif
  (* Dir (Left, c) ⇓ [Γ ⊢ Δ, H : A ∧ B]  ≜  c ⇓ [Γ ⊢ Δ, H : A] *)
  (* Dir (Left, c) ⇓ [Γ, H : A ∨ B ⊢ Δ]  ≜  c ⇓ [Γ, H : A ⊢ Δ] *)
  (* and similar definition for Right instead of Left *)
  | Intro of certif * ident
  (* Intro (c, G) ⇓ [Γ ⊢ Δ, H : A → B]  ≜  c ⇓ [Γ, G : A ⊢ Δ, H : B  *)
  | Weakening of certif
  (* Weakening c ⇓ [Γ ⊢ Δ, H : A]  ≜  c ⇓ [Γ ⊢ Δ] *)
  (* Weakening c ⇓ [Γ, H : A ⊢ Δ]  ≜  c ⇓ [Γ ⊢ Δ] *)
  | Rewrite of bool * ident * path * certif list
  (* Rewrite (rev, G, p, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <H> an equality that is in <G>, following the path <p>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <G> can have premisses, those are then matched against the certificates <lc> *)


type ctrans = task -> task list * certif

let rec cterm_equal t1 t2 =
  match t1, t2 with
  | CTapp i1, CTapp i2 -> Ident.id_equal i1 i2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | _ -> false

let cterm_pos_equal (t1, p1) (t2, p2) =
  cterm_equal t1 t2 && p1 = p2

let ctask_equal = Mid.equal cterm_pos_equal


(* For debugging purposes *)
let ip = create_ident_printer []

let pri fmt i =
  fprintf fmt "%s" (id_unique ip i)
and prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"
and prle sep pre fmt le =
  let prl = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep) pre in
  fprintf fmt "[%a]" prl le

let rec print_certif where cert =
  let oc = open_out where in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prc (fmt : formatter) = function
  | Skip -> fprintf fmt "Skip"
  | Axiom (h, where) -> fprintf fmt "Axiom @[(%a,@ %a)@]" pri h pri where
  | Split (c1, c2, where) -> fprintf fmt "Split @[(%a,@ %a,@ %a)@]" prc c1 prc c2 pri where
  | Unfold (c, where) -> fprintf fmt "Unfold @[(%a,@ %a)@]" prc c pri where
  | Destruct (c, i1, i2, where) -> fprintf fmt "Destruct @[(%a,@ %a,@ %a,@ %a)@]"
                                     prc c pri i1 pri i2 pri where
  | Dir (d, c, where) -> fprintf fmt "Dir @[(%a,@ %a,@ %a)@]" prd d prc c pri where
  | Intro (name, c, where) -> fprintf fmt "Intro @[(%a,@ %a,@ %a)@]" pri name prc c pri where
  | Weakening (c, where) -> fprintf fmt "Weakening @[(%a,@ %a)@]" prc c pri where
  | Rewrite (rev, h, p, lc, where) ->
      fprintf fmt "Rewrite @[(%b,@ %a,@ %a,@ %a,@ %a)@]"
        rev pri h (prle "; " prd) p (prle "; " prc) lc pri where

let rec pcte fmt = function
  | CTapp i -> pri fmt i
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
and pro fmt = function
  | CTor -> fprintf fmt "\\/"
  | CTand -> fprintf fmt "/\\"
  | CTimplies -> fprintf fmt "->"
  | CTiff -> fprintf fmt "<->"

let prpos fmt = function
  | true  -> fprintf fmt "GOAL: "
  | false -> fprintf fmt "HYP : "

let prmid fmt mid =
  Mid.iter (fun i (cte, pos) -> fprintf fmt "%a%a ==> %a\n" prpos pos pri i pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n" prmid cta

let print_ctasks where lcta =
  let oc = open_out where in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." (prle "==========\n" pcta) lcta;
  close_out oc


(** Translating Why3 tasks to simplified certificate tasks *)

let translate_op = function
  | Tand -> CTand
  | Tor -> CTor
  | Timplies -> CTimplies
  | Tiff -> CTiff

let rec translate_term (t : term) : cterm =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
  | Tbinop (op, t1, t2) -> CTbinop (translate_op op, translate_term t1, translate_term t2)
  | _ -> invalid_arg "Cert_syntax.translate_term"

let translate_decl (dec : decl) : ctask =
  match dec.d_node with
  | Dprop (Pgoal, pr, f) ->
       Mid.singleton pr.pr_name (translate_term f, true)
  | Dprop (_, pr, f) ->
      Mid.singleton pr.pr_name (translate_term f, false)
  | _ -> Mid.empty

let translate_tdecl (td : tdecl) : ctask =
  match td.td_node with
  | Decl d -> translate_decl d
  | _ -> Mid.empty

let rec translate_task_acc acc = function
  | Some {task_decl = d; task_prev = p} ->
      let new_acc = Mid.set_union acc (translate_tdecl d) in
      translate_task_acc new_acc p
  | None -> acc

let translate_task =
  translate_task_acc Mid.empty


(** Using ctasks and certificates *)

(* check_certif replays the certificate on a ctask *)
exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)

let find_ident i cta =
  match Mid.find_opt i cta with
  | Some x -> x
  | None -> verif_failed "Can't find ident in the task"

(* Ensures the goal has exactly one cterm *)
let split_cta cta =
  let open Mid in
  fold (fun i (cte, pos) (mh, mg) ->
      if pos then mh, add i (cte, pos) mg
      else add i (cte, pos) mh, mg)
    cta (empty, empty)

let set_goal (cta : ctask) =
  let mh, mg = split_cta cta in
  let idg, _ = Mid.choose mg in
  fun ct -> Mid.add idg (ct, true) mh

let rec check_rewrite_term tl tr t p =
  (* returns t where the instance at p of tl is replaced by tr *)
  match p, t with
  | [], t when cterm_equal t tl -> tr
  | Left::prest, CTbinop (op, t1, t2) ->
      let nt1 = check_rewrite_term tl tr t1 prest in
      CTbinop (op, nt1, t2)
  | Right::prest, CTbinop (op, t1, t2) ->
      let nt2 = check_rewrite_term tl tr t2 prest in
      CTbinop (op, t1, nt2)
  | _ -> verif_failed "Can't follow the rewrite path"

let check_rewrite cta rev rh where p : ctask list =
  let rec introduce acc = function
    | CTbinop (CTimplies, t1, t2) -> introduce (t1::acc) t2
    | t -> acc, t in
  let lp, tl, tr =
    let ct, pos = find_ident rh cta in
    if pos then verif_failed "Can't use goal as an hypothesis to rewrite" else
      match introduce [] ct with
      | lp, CTbinop (CTiff, t1, t2) -> if rev then lp, t1, t2 else lp, t2, t1
      | _ -> verif_failed "Can't find the hypothesis used to rewrite" in
  let rewrite_decl id (te, b) =
    if id_equal id where
    then check_rewrite_term tl tr te p, b
    else te, b in
  Mid.mapi rewrite_decl cta :: List.map (set_goal cta) lp

let rec check_certif cta (cert : certif) : ctask list =
  match cert with
    | Skip -> [cta]
    | Axiom (h, where) ->
        let th, posh = find_ident h cta in
        let tw, posw = find_ident where cta in
        if not posh && posw
        then if cterm_equal th tw
             then []
             else verif_failed "The hypothesis and goal given do not match"
        else verif_failed "Terms have wrong positivities in the task"
    | Split (c1, c2, where) ->
        let t, pos = find_ident where cta in
        begin match t, pos with
        | CTbinop (CTand, t1, t2), true | CTbinop (CTor, t1, t2), false ->
            let cta1 = Mid.add where (t1, pos) cta in
            let cta2 = Mid.add where (t2, pos) cta in
            check_certif cta1 c1 @ check_certif cta2 c2
        | _ -> verif_failed "Not splittable" end
    | Unfold (c, where) ->
        let t, pos = find_ident where cta in
        begin match t with
        | CTbinop (CTiff, t1, t2) ->
            let imp_pos = CTbinop (CTimplies, t1, t2) in
            let imp_neg = CTbinop (CTimplies, t2, t1) in
            let destruct_iff = CTbinop (CTand, imp_pos, imp_neg), pos in
            let cta = Mid.add where destruct_iff cta in
            check_certif cta c
        | _ -> verif_failed "Not decodable" end
    | Destruct (c, i1, i2, where) ->
        let t, pos = find_ident where cta in
        begin match t, pos with
        | CTbinop (CTand, t1, t2), false | CTbinop (CTor, t1, t2), true ->
            let cta = Mid.remove where cta
                      |> Mid.add i1 (t1, pos)
                      |> Mid.add i2 (t2, pos) in
            check_certif cta c
        | _ -> verif_failed "Not destructible"  end
    | Dir (d, c, where) ->
        let t, pos = find_ident where cta in
        begin match t, d, pos with
        | CTbinop (CTor, t, _), Left, true | CTbinop (CTor, _, t), Right, true
        | CTbinop (CTand, t, _), Left, false | CTbinop (CTand, _, t), Right, false ->
          let cta = Mid.add where (t, pos) cta in
          check_certif cta c
        | _ -> verif_failed "Can't follow a direction" end
    | Intro (name, c, where) ->
        let t, pos = find_ident where cta in
        begin match t, pos with
        | CTbinop (CTimplies, f1, f2), true ->
            let cta = Mid.add name (f1, false) cta
                      |> Mid.add where (f2, true) in
            check_certif cta c
        | _ -> verif_failed "Nothing to introduce" end
    | Weakening (c, where) ->
        let cta = Mid.remove where cta in
        check_certif cta c
    | Rewrite (rev, h, p, lc, where) ->
        let lcta = check_rewrite cta rev h where p in
        List.map2 check_certif lcta lc |> List.concat


(* Creates a certified transformation from a transformation with certificate *)
let checker_ctrans ctr task =
  try let ltask, cert = ctr task in
      let ctask = translate_task task in
      print_certif "/tmp/certif.log" cert;
      print_ctasks "/tmp/init_ctask.log" [ctask];
      let lctask = check_certif ctask cert in
      if Lists.equal ctask_equal lctask (List.map translate_task ltask)
      then ltask
      else begin
          print_ctasks "/tmp/from_trans.log" (List.map translate_task ltask);
          print_ctasks "/tmp/from_cert.log" lctask;
          verif_failed "Replaying certif gives different result" end
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_ctrans", e))

(* Generalize ctrans on (task list * certif), the invariant is that the number of
  Skip in the certif is equal to the list length. *)
let ctrans_gen (ctr : ctrans) (ts, c) =
  let rec fill acc c ts = match c with
    | Skip -> begin match ts with
              | [] -> assert false
              | t::ts -> let lt, ct = ctr t in
                         lt :: acc, ct, ts end
    | Axiom _ -> acc, c, ts
    | Split (c1, c2, where) -> let acc, c1, ts = fill acc c1 ts in
                               let acc, c2, ts = fill acc c2 ts in
                               acc, Split (c1, c2, where), ts
    | Unfold (c, where) -> let acc, c, ts = fill acc c ts in
                             acc, Unfold (c, where), ts
    | Destruct (c, i1, i2, where) -> let acc, c, ts = fill acc c ts in
                                     acc, Destruct (c, i1, i2, where), ts
    | Dir (d, c, where) -> let acc, c, ts = fill acc c ts in
                           acc, Dir (d, c, where), ts
    | Intro (name, c, where) -> let acc, c, ts = fill acc c ts in
                                acc, Intro (name, c, where), ts
    | Weakening (c, where) -> let acc, c, ts = fill acc c ts in
                              acc, Weakening (c, where), ts
    | Rewrite (rev, h, p, lc, where) ->
        let acc, lc, ts = List.fold_left (fun (acc, lc, ts) nc ->
                              let acc, c, ts = fill acc nc ts in
                              (acc, c::lc, ts)) (acc, [], ts) lc in
        acc, Rewrite (rev, h, p, List.rev lc, where), ts
  in
  let acc, c, ts = fill [] c ts in
  assert (ts = []);
  let rev_concat l1 l2 = List.fold_left (fun acc l -> l @ acc) l2 l1 in
  rev_concat acc [], c

let rec nocuts = function
  | Skip -> false
  | Axiom _ -> true
  | Split (c1, c2, _) -> nocuts c1 && nocuts c2
  | Unfold (c, _)
  | Destruct (c, _, _, _)
  | Dir (_, c, _)
  | Weakening (c, _)
  | Intro (_, c, _) -> nocuts c
  | Rewrite (_, _, _, lc, _) -> List.for_all nocuts lc

(** Primitive transformations with certificate *)

let pr_arg_opt task = function
  | Some pr -> pr
  | None -> task_goal task

(* Identity transformation with certificate *)
let id task = [task], Skip

(* Assumption with certificate *)
let assumption_decl g (d : decl) =
  match d.d_node with
  | Dprop (_, pr, f) -> if t_equal_nt_na g f
                        then Some pr.pr_name
                        else None
  | _ -> None

let assumption_tdecl g (td : tdecl) =
  match td.td_node with
  | Decl d -> assumption_decl g d
  | _ -> None

let rec assumption_ctxt g = function
  | Some {task_decl = d; task_prev = p} ->
      begin match assumption_tdecl g d with
      | Some h -> h
      | None -> assumption_ctxt g p end
  | None -> raise Not_found

let assumption t  =
  let pr, g = try task_goal t, task_goal_fmla t
          with GoalNotFound -> invalid_arg "Cert_syntax.assumption" in
  let _, t' = task_separate_goal t in
  try let h = assumption_ctxt g t' in
      [], Axiom (h, pr.pr_name)
  with Not_found -> [t], Skip


(* Split with certificate *)
let destruct where task =
  let iw = (pr_arg_opt task where).pr_name in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal iw pr.pr_name ->
        begin match k, t.t_node with
        | k, Tbinop (Tand, f1, f2) when k <> Pgoal ->
            let pr1 = create_prsymbol (id_clone iw) in
            let pr2 = create_prsymbol (id_clone iw) in
            clues := Some (pr1, pr2);
            [create_prop_decl k pr1 f1; create_prop_decl k pr2 f2]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some (pr1, pr2) -> [nt], Destruct (Skip, pr1.pr_name, pr2.pr_name, iw)
  | None -> [task], Skip


let unfold where task =
  let iw = (pr_arg_opt task where).pr_name in
  let clues = ref false in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal iw pr.pr_name ->
        begin match t.t_node with
        | Tbinop (Tiff, f1, f2) ->
            clues := true;
            let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
            [create_prop_decl k pr destr_iff]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  if !clues then [nt], Unfold (Skip, iw)
  else [task], Skip

let split_or_and where task =
  let iw = (pr_arg_opt task where).pr_name in
  let clues = ref false in (* TODO Andrei *)
  let trans_t = Trans.decl_l (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal iw pr.pr_name ->
        begin match k, t.t_node with
        | Pgoal as k, Tbinop (Tand, f1, f2)
        | (Paxiom | Plemma as k), Tbinop (Tor, f1, f2) ->
            clues := true;
            [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]]
        | _ -> [[d]] end
    | _ -> [[d]]) None in
  let nt = Trans.apply trans_t task in
  if !clues then nt, Split (Skip, Skip, iw)
  else [task], Skip

(* Intro with certificate *)
let intro task = (* introduce hypothesis A when the goal is of the form A -> B *)
  let npr = create_prsymbol (id_fresh "H") in
  let pr, g = try task_goal task, task_goal_fmla task
              with GoalNotFound -> invalid_arg "Cert_syntax.intro" in
  let _, c = task_separate_goal task in
  match g.t_node with
  | Tbinop (Timplies, f1, f2) ->
      let decl1 = create_prop_decl Paxiom npr f1 in
      let tf1 = add_decl c decl1 in
      let tf2 = add_decl tf1 (create_prop_decl Pgoal pr f2) in
      [tf2], Intro (npr.pr_name, Skip, pr.pr_name)
  | _ -> [task], Skip

(* Direction with certificate *)
let dir d task = (* choose Left (A) or Right (B) when the goal is of the form A \/ B *)
  let pr, g = try task_goal task, task_goal_fmla task
              with GoalNotFound -> invalid_arg "Cert_syntax.dir" in
  let _, c = task_separate_goal task in
  match g.t_node, d with
  | Tbinop (Tor, f, _), Left | Tbinop (Tor, _, f), Right ->
      let tf = add_decl c (create_prop_decl Pgoal pr f) in
      [tf], Dir (d, Skip, pr.pr_name)
  | _ -> [task], Skip

(* Rewrite with certificate *)
let rec rewrite_in_term tl tr t : (term * path) option =
  (* tries all paths in [t] to replace [tl] with [tr] *)
  if t_equal tl t
  then Some (tr, [])
  else match t.t_node with
       | Tbinop (op, t1, t2) ->
           begin match rewrite_in_term tl tr t1 with
           | Some (nt1, p) -> Some (t_binary op nt1 t2, Left::p)
           | None -> match rewrite_in_term tl tr t2 with
                     | Some (nt2, p) -> Some (t_binary op t1 nt2, Right::p)
                     | None -> None end
       | _ -> None

let rec intro_premises acc t = match t.t_node with
  | Tbinop (Timplies, f1, f2) -> intro_premises (f1::acc) f2
  | _ -> acc, t

let rewrite_in rev h h1 task =
  let h = h.pr_name and h1 = h1.pr_name in
  let clues = ref None in
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h ->
          let lp, f = intro_premises [] t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, t1, t2)
      | _ -> acc)
      None
  in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Args_wrapper.Arg_error "rewrite") (* Should not happen *)
    | Some (lp, t1, t2) ->
      Trans.fold_decl (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t)
              when id_equal pr.pr_name h1 && (p = Pgoal || p = Paxiom) ->
            begin match rewrite_in_term t1 t2 t with
              | Some (new_term, path) ->
                  clues := Some (path, Skip :: List.map (fun _ -> Skip) lp);
                  Some (lp, create_prop_decl p pr new_term)
              | None -> None end
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)

  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_decl) ->
      let trans_rewriting =
        Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _) when id_equal pr.pr_name h1 && (p = Paxiom || p = Pgoal) ->
            [new_decl]
        | _ -> [d]) None in
      let list_par =
        List.map (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (Pgoal, pr, _) ->
                [create_goal ~expl:"rewrite premises" pr e]
             (* [create_goal ~expl:"rewrite premises" (create_prsymbol (gen_ident "G")) e] *)
            | _ -> [d])
          None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  let gen_task = Trans.apply (Trans.bind (Trans.bind found_eq lp_new) recreate_tasks) task in
  match !clues with
  | None -> [task], Skip
  | Some (path, lc) ->
      gen_task, Rewrite (rev, h, path, lc, h1)

let rewrite rev h h1 task =
  let h1 = pr_arg_opt task h1 in
  rewrite_in (not rev) h h1 task

let clear_one i task =
  let trans = Trans.decl (fun d -> match d.d_node with
    | Dprop (_, pr, _) when id_equal i pr.pr_name -> []
    | _ -> [d]) None in
  [Trans.apply trans task], Weakening (Skip, i)


(** Transformials *)

(* Compose transformations with certificate *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

let compose_list l = List.fold_left compose id l

(* If Then Else on transformations with certificate *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  (* applies [tri], if the task changed then apply [trt] else apply [tre] *)
  let ((lt, cert) as tri_task) = tri task in
  if not (Lists.equal task_equal lt [task] && cert = Skip)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task

(* Try on transformations with certificate *)
let rec try_close (lctr : ctrans list) : ctrans = fun task ->
  (* try each transformation in [lctr] and keep the one that closes the task *)
  match lctr with
  | [] -> id task
  | h::t -> let lctask_h, cert_h = h task in
            if lctask_h = []
            then [], cert_h
            else try_close t task

(* Repeat on transformations with certificate *)
let repeat (ctr : ctrans) : ctrans = fun task ->
  (* keep applying [ctr] as long as the task changes *)
  let gen_task = id task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task

(** Derived transformations with certificate *)

let intros = repeat intro

let split_logic where = compose (unfold where)
                          (compose (split_or_and where)
                             (destruct where))

let rec intuition task =
  repeat (compose assumption
            (compose intro
               (compose (split_logic None)
                  (try_close [ite (dir Left) intuition id;
                              ite (dir Right) intuition id])))) task

let clear l = compose_list (List.map (fun pr -> clear_one pr.pr_name) l)


(** Certified transformations *)

let assumption_trans = checker_ctrans assumption
let split_trans where = checker_ctrans (split_logic where)
let intro_trans = checker_ctrans intro
let left_trans = checker_ctrans (dir Left)
let right_trans = checker_ctrans (dir Right)
let rewrite_trans rev rh where = checker_ctrans (rewrite rev rh where)
let clear_trans l = checker_ctrans (clear l)

let intros_trans = checker_ctrans intros
let intuition_trans = checker_ctrans intuition

let () =
  let open Args_wrapper in
  Trans.register_transform_l "assumption_cert" (Trans.store assumption_trans)
    ~desc:"A certified version of coq tactic [assumption]";
  Trans.register_transform_l "intro_cert" (Trans.store intro_trans)
    ~desc:"A certified version of (simplified) coq tactic [intro]";
  Trans.register_transform_l "left_cert" (Trans.store left_trans)
    ~desc:"A certified version of coq tactic [left]";
  Trans.register_transform_l "right_cert" (Trans.store right_trans)
    ~desc:"A certified version of coq tactic [right]";
  wrap_and_register ~desc:"A certified version of (simplified) coq tactic [clear]"
    "clear_cert" (Tprlist Ttrans_l)
    (fun l -> Trans.store (clear_trans l));
  wrap_and_register ~desc:"A certified version of (simplified) coq tactic [split]"
    "split_cert" (Topt ("in", Tprsymbol (Ttrans_l)))
    (fun h -> Trans.store (split_trans h));
  wrap_and_register ~desc:"A certified version of transformation rewrite"
    "rewrite_cert" (Toptbool ("<-", (Tprsymbol (Topt ("in", Tprsymbol (Ttrans_l))))))
    (fun rev rh where -> Trans.store (rewrite_trans rev rh where))


let () =
  Trans.register_transform_l "intros_cert" (Trans.store intros_trans)
    ~desc:"A certified version of coq tactic [intros]";
  Trans.register_transform_l "intuition_cert" (Trans.store intuition_trans)
    ~desc:"A certified version of (simplified) coq tactic [intuition]"
