open Why3

open Task
open Decl
open Term
open Ident
open Generic_arg_trans_utils


open Cert_certificates


let decl_cert f = Trans.decl_acc (hole ()) (|>>) (fun d _ -> f d)
let decl_l_cert f = Trans.decl_l_acc (hole ()) (|>>) (fun d _ -> f d)

let map_ty = function
    | None -> Ty.ty_bool
    | Some ty -> ty

(* Identity transformation with a certificate *)
let id_ctrans = Trans.store (fun task -> [task], hole ())

(** Combinators on transformations with a certificate *)

(* Generalize ctrans on <task list * certif>, with the invariant that each <Hole> in the
   certif corresponds to one task in the list *)
let ctrans_gen (ctr : ctrans) (ts, c : task list * visible_cert) =
  let llt, lc = List.split (List.map (Trans.apply ctr) ts) in
  List.flatten llt, c |>>> lc

(* Apply a <ctrans> and then apply another <ctrans> on every <task> generated by the first one *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = Trans.store (fun t ->
  Trans.apply tr1 t |> ctrans_gen tr2)

let compose_list l = List.fold_left compose id_ctrans l

let is_hole (v, c) =
  match v, c with
  | [i], Hole j when id_equal i j -> true
  | _ -> false

(* If Then Else on transformations with a certificate :  *)
(*   applies [tri], if the task changed then apply [trt] else apply [tre] *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = Trans.store (fun task ->
  let (lt, c) as tri_task = Trans.apply tri task in
  if not (Lists.equal task_equal lt [task] && is_hole c)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task)

(* Try on transformations with a certificate : *)
(*   try each transformation in <lctr> and keep the one that closes the <task> *)
let rec try_close (lctr : ctrans list) : ctrans = Trans.store (fun task ->
  match lctr with
  | [] -> Trans.apply id_ctrans task
  | h::t -> let lctask_h, cert_h = Trans.apply h task in
            if lctask_h = []
            then [], cert_h
            else Trans.apply (try_close t) task)

(* Repeat on a transformation with a certificate : *)
(*   keep applying <ctr> as long as the task changes *)
let repeat (ctr : ctrans) : ctrans = Trans.store (fun task ->
  let gen_task = Trans.apply id_ctrans task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task)


(** Primitive transformations with a certificate *)

(* First, some utility functions *)
let default_goal task = function
  | Some pr -> pr
  | None -> task_goal task

type target =
  | Pr of prsymbol
  | Everywhere
  | Anywhere
  | Nowhere

let find_target any every where task =
  if any then Anywhere
  else if every then Everywhere
  else Pr (default_goal task where)

let match_tg tg pr = match tg with
  | Pr pr' -> pr_equal pr' pr
  | Everywhere | Anywhere -> true
  | Nowhere -> false

let update_tg_c (tg, c1) co =
  match tg, co with
  | Everywhere, Some c2 -> Everywhere, c1 |>> c2
  | Everywhere, None -> Everywhere, c1
  | _, Some c2 -> assert (is_hole c1); Nowhere, c2
  | _, None -> tg, c1

let update_opt o1 o2 = match o1 with
  | Some _ -> o1
  | None -> o2

(* To debug *)
open Format
let rec print_ast fmt t = match t.t_node with
  | Tvar _ -> fprintf fmt "Tvar"
  | Tconst _ -> fprintf fmt "Tconst"
  | Tapp (l, ts) ->
      fprintf fmt "(%a %a)"
        Cert_abstract.prid (l.ls_name)
        (pp_print_list print_ast) ts
  | Tif _ -> fprintf fmt "Tif"
  | Tlet _ -> fprintf fmt "Tlet"
  | Tcase _ -> fprintf fmt "Tcase"
  | Teps _ -> fprintf fmt "Teps"
  | Tquant (_, t) -> let _, _, t = t_open_quant t in
                     fprintf fmt "Tquant (Q, %a)"
                       print_ast t
  | Tbinop (_, t1, t2) ->
      fprintf fmt "%a BOP %a"
        print_ast t1
        print_ast t2
  | Tnot t -> fprintf fmt "Tnot (%a)" print_ast t
  | Ttrue -> fprintf fmt "Ttrue"
  | Tfalse -> fprintf fmt "Tfalse"

let tprint_tg target =
  Trans.decl_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
      | Dprop (_, pr, t) when match_tg tg pr ->
          Format.eprintf "%a : %a@." Cert_abstract.prhyp (pr.pr_name) print_ast t;
          [d], None
      | _ -> [d], None)

let tprint any every where : ctrans = Trans.store (fun task ->
   let tg = find_target any every where task in
   let ta, (_, c) = tprint_tg tg task in
   [ta], c)


(* Assumption with a certificate : *)
let assumption_pr_t prg tg = decl_l_cert (fun d -> match d.d_node with
  | Dprop (Paxiom, pr, t) when t_equal t tg -> [], ([], Axiom (pr, prg))
  | _ -> [[d]], hole ())

let assumption : ctrans = Trans.store (fun task ->
  let prg, tg = task_goal task, task_goal_fmla task in
  assumption_pr_t prg tg task)

let find_contradict = Trans.fold_decl (fun d (m, (cert : visible_cert)) -> match d.d_node with
  | Dprop (Paxiom, pr, t) ->
      let un_not_t = match t.t_node with Tnot t -> t | _ -> t_not t in
      let new_cert = match Mterm.(find_opt (t_not t) m, find_opt un_not_t m) with
        | Some g, _ | _, Some g -> [], Swap (g, Axiom (pr, g))
        | _ -> cert in
      Mterm.add t pr m, new_cert
  | _ -> m, cert) (Mterm.empty, hole ())

let contradict : ctrans = Trans.store (fun task ->
  let _, c = Trans.apply find_contradict task in
  let res_task = if is_hole c then [task] else [] in
  res_task, c)

let ren pr1 =
  decl_cert  (fun d -> match d.d_node with
   | Dprop (k, pr, t) when pr_equal pr pr1 ->
       let pr2 = pr_clone pr1 in
       [create_prop_decl k pr2 t],
       lambda one (fun i -> rename pr1 pr2 (Hole i))
   | _ -> [d], hole ())

let crename pr1 : ctrans = Trans.store (fun task ->
  let ta, c = ren pr1 task in
  [ta], c)


(* Closes task if hypotheses contain false or if the goal is true or reflexivity of equality *)
let close : ctrans = Trans.store (fun task ->
  let trans = Trans.fold_decl (fun d acc -> match d.d_node, acc with
    | _, Some _ -> acc
    | Dprop (k, pr, t), _ ->
        begin match k, t.t_node with
        | Pgoal, Ttrue | Paxiom, Tfalse -> Some pr
        | Pgoal, Tapp (e, [e1; e2])
            when ls_equal e ps_equ &&
                 t_equal e1 e2 -> Some pr
        | _ -> acc
        end
    | _ -> acc) None in
  match Trans.apply trans task with
  | Some pr -> [], ([], Trivial pr)
  | None -> [task], hole ())


(* Split with a certificate : *)
(* destructs a logical constructor at the top of the formula *)
(* destructs /\ in the hypotheses *)

(* let destruct omni where : ctrans = Trans.store (fun task ->
 *   let target = tg omni where task in
 *   let clues = ref None in
 *   let trans_t = Trans.decl (fun d -> match d.d_node with
 *     | Dprop (k, pr, t) ->
 *         begin match k, t.t_node with
 *         | k, Tbinop (Tand, f1, f2) when k <> Pgoal ->
 *             if is_target pr target then begin
 *                 let pr1 = pr_clone pr in
 *                 let pr2 = pr_clone pr in
 *                 clues := Some (Destruct (pr, pr1, pr2, Hole));
 *                 [create_prop_decl k pr1 f1; create_prop_decl k pr2 f2] end
 *             else [d]
 *         | _ -> [d] end
 *     | _ -> [d]) None in
 *   let nt = Trans.apply trans_t task in
 *   match !clues with
 *   | Some c -> [nt], c
 *   | None -> [task], Hole) *)

(* let destruct omni where : ctrans = Trans.store (fun task ->
 *   let target = tg omni where task in
 *   let trans_t = Trans.decl_acc None update_opt (fun d o -> match d.d_node, o with
 *     | Dprop (Paxiom, pr, {t_node = Tbinop (Tand, f1, f2)}), None ->
 *         if is_target pr target then begin
 *             let pr1 = pr_clone pr in
 *             let pr2 = pr_clone pr in
 *             [create_prop_decl Paxiom pr1 f1; create_prop_decl Paxiom pr2 f2],
 *             Some (Destruct (pr, pr1, pr2, Hole))
 *           end
 *         else [d], None
 *     | _ -> [d], None) in
 *   let nt, o = trans_t task in
 *   match o with
 *   | Some c -> [nt], c
 *   | None -> [task], Hole) *)

(* let destruct_tg target =
 *   Trans.decl_acc (target, Hole) (fun _ acc -> acc) (fun d (tg, c) -> match d.d_node with
 *       | Dprop (Paxiom, pr, {t_node = Tbinop (Tand, f1, f2)}) when match_tg tg pr ->
 *           let pr1 = pr_clone pr in
 *           let pr2 = pr_clone pr in
 *           [create_prop_decl Paxiom pr1 f1; create_prop_decl Paxiom pr2 f2],
 *           (Nowhere, Destruct (pr, pr1, pr2, Hole))
 *       | _ -> [d], (tg, c)) *)


let destruct_tg target =
  Trans.decl_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
      | Dprop (Paxiom, pr, {t_node = Tbinop (Tand, f1, f2)}) when match_tg tg pr ->
          let pr1 = pr_clone pr in
          let pr2 = pr_clone pr in
          [create_prop_decl Paxiom pr1 f1; create_prop_decl Paxiom pr2 f2],
          Some (lambda one (fun i -> Destruct (pr, pr1, pr2, Hole i)))
      | _ -> [d], None)

let destruct any every where : ctrans = Trans.store (fun task ->
   let tg = find_target any every where task in
   let ta, (_, c) = destruct_tg tg task in
   [ta], c)

(* destructs /\ in the goal or \/ in the hypotheses *)
let split_or_and_tg target =
  Trans.decl_l_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match k, t.t_node with
        | (Pgoal as k), Tbinop (Tand, f1, f2)
        | (Paxiom as k), Tbinop (Tor, f1, f2) ->
            [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]],
            Some (lambda two (fun i j -> Split (pr, Hole i, Hole j)))
        | _ -> [[d]], None end
    | _ -> [[d]], None)

let split_or_and any every where : ctrans = Trans.store (fun task ->
   let tg = find_target any every where task in
   let lta, (_, c) = split_or_and_tg tg task in
   lta, c)

let destruct_all_tg target =
  Trans.decl_l_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match k, t.t_node with
        | (Paxiom as k), Tbinop (Tand, f1, f2) ->
            let pr1 = pr_clone pr in
            let pr2 = pr_clone pr in
            [[create_prop_decl k pr1 f1; create_prop_decl k pr2 f2]],
            Some (lambda one (fun i -> Destruct (pr, pr1, pr2, Hole i)))
        | (Pgoal as k), Tbinop (Tand, f1, f2)
        | (Paxiom as k), Tbinop (Tor, f1, f2) ->
            [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]],
            Some (lambda two (fun i j -> Split (pr, Hole i, Hole j)))
        | Pgoal, Tbinop (Tor, f1, f2) ->
            let prh = pr_clone pr in
            [[create_prop_decl Paxiom prh (t_not_simp f1); create_prop_decl Pgoal pr f2]],
            Some (lambda one (fun i -> Destruct (pr, prh, pr, Swap (prh, Hole i))))
        | _ -> [[d]], None end
    | _ -> [[d]], None)

let destruct_all any every where : ctrans = Trans.store (fun task ->
   let tg = find_target any every where task in
   let lta, (_, c) = destruct_all_tg tg task in
   lta, c)

let neg_decompose_tg target =
  Trans.decl_l_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match t.t_node with
        | Tnot nt ->
            begin match k, nt.t_node with
            | k, Tnot nnt -> (* double negation *)
                [[create_prop_decl k pr nnt]],
                Some (lambda one (fun i ->
                  Swap (pr, Swap (pr, Hole i))))
            | Paxiom, Tbinop (Tor, f1, f2) -> (* destruct *)
                let pr1 = pr_clone pr in
                let pr2 = pr_clone pr in
                [[create_prop_decl Paxiom pr1 (t_not_simp f1);
                  create_prop_decl Paxiom pr2 (t_not_simp f2)]],
                Some (lambda one (fun i ->
                  Swap (pr,
                  Destruct (pr, pr1, pr2,
                  Swap (pr1, Swap (pr2, Hole i))))))
            | Pgoal, Tbinop (Tand, f1, f2) ->
                let pr1 = pr_clone pr in
                let pr2 = pr_clone pr in
                [[create_prop_decl Paxiom pr1 f1;
                  create_prop_decl Pgoal pr2 (t_not_simp f2)]],
                Some (lambda one (fun i ->
                  Swap (pr,
                  Destruct (pr, pr1, pr2,
                  Swap (pr2, Hole i)))))
            | Paxiom, Tbinop (Tand, f1, f2) -> (* split *)
                [[create_prop_decl Paxiom pr (t_not_simp f1)];
                 [create_prop_decl Paxiom pr (t_not_simp f2)]],
                Some (lambda two (fun i j ->
                  Swap (pr,
                  Split (pr,
                         Swap (pr, Hole i),
                         Swap (pr, Hole j)))))
            | Pgoal, Tbinop (Tor, f1, f2) ->
                [[create_prop_decl Pgoal pr (t_not_simp f1)];
                 [create_prop_decl Pgoal pr (t_not_simp f2)]],
                Some (lambda two (fun i j ->
                Swap (pr,
                Split (pr,
                       Swap (pr, Hole i),
                       Swap (pr, Hole j)))))
            | Pgoal, Ttrue -> (* ⊥ and ⊤ *)
                [[create_prop_decl Pgoal pr t_false]],
                Some (lambda one (fun i ->
                Clear (pr,
                Assert (pr, t_false,
                        Hole i,
                        Trivial pr))))
            | Pgoal, Tfalse ->
                [], Some (lambda Z (Swap (pr, Trivial pr)))
            | Paxiom, Tfalse ->
                [[]], Some (lambda one (fun i -> Clear (pr, Hole i)))
            | Paxiom, Ttrue ->
                [], Some (lambda Z (Swap (pr, Trivial pr)))
            | k, Tbinop (Tiff, f1, f2) -> (* unfold *)
                let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
                [[create_prop_decl k pr destr_iff]],
                Some (lambda one (fun i -> Swap (pr, Unfold (pr, Swap (pr, Hole i)))))
            | k, Tbinop (Timplies, f1, f2) ->
                let destr_imp = t_or (t_not f1) f2 in
                [[create_prop_decl k pr destr_imp]],
                Some (lambda one (fun i -> Swap (pr, Unfold (pr, Swap (pr, Hole i)))))
            | _ -> [[d]], None
            end
        | _ -> [[d]], None end
    | _ -> [[d]], None)

let neg_decompose any every where : ctrans = Trans.store (fun task ->
   let tg = find_target any every where task in
   let lta, (_, c) = neg_decompose_tg tg task in
   lta, c)

(* replaces A <-> B with (A -> B) /\ (B -> A) *)
(* and A -> B with ¬A ∨ B *)
let unfold_tg target =
  Trans.decl_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match t.t_node with
        | Tbinop (Tiff, f1, f2)  ->
            let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
            [create_prop_decl k pr destr_iff],
            Some (lambda one (fun i -> Unfold (pr, Hole i)))
        | Tbinop (Timplies, f1, f2) ->
            let destr_imp = t_or (t_not f1) f2 in
            [create_prop_decl k pr destr_imp],
            Some (lambda one (fun i -> Unfold (pr, Hole i)))
        | _ -> [d], None end
    | _ -> [d], None)

let unfold any every where : ctrans = Trans.store (fun task ->
  let tg = find_target any every where task in
  let ta, (_, c) = unfold_tg tg task in
  [ta], c)

(* the next 2 functions are copied from introduction.ml *)
let intro_attrs = Sattr.singleton Inlining.intro_attr

let ls_of_vs vs =
  let id = id_clone ~attrs:intro_attrs vs.vs_name in
  create_fsymbol id [] vs.vs_ty

let intro_tg target =
  Trans.decl_acc (target, hole ()) update_tg_c (fun d (tg, _) -> match d.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match t.t_node, k with
        | Tbinop (Timplies, f1, f2), Pgoal ->
            let hpr = create_prsymbol (id_fresh "H") in
            [create_prop_decl Paxiom hpr f1; create_prop_decl Pgoal pr f2],
            Some (lambda one (fun i ->
              Unfold (pr,
              Destruct (pr, hpr, pr,
              Swap (hpr, Hole i)))))
        | Tquant ((Tforall as q), f), (Pgoal as k)
        | Tquant ((Texists as q), f), (Paxiom as k) ->
            let vsl, tg, f_t = t_open_quant f in
            begin match vsl with
            | vs::vsl ->
                let ls = ls_of_vs vs in
                let subst = Mvs.singleton vs (fs_app ls [] vs.vs_ty) in
                let f = t_subst subst f_t
                        |> t_close_quant vsl tg
                        |> t_quant q in
                [create_param_decl ls; create_prop_decl k pr f],
                Some (lambda one (fun i -> IntroQuant (pr, ls.ls_name, Hole i)))
            | [] -> assert false
            end
        | _ -> [d], None end
    | _ -> [d], None)


(* introduces hypothesis H : A when the goal is of the form A → B or
     introduces variable x when the goal is of the form ∀ x. P x
     introduces variable x when a hypothesis is of the form ∃ x. P x *)
let intro any every where : ctrans = Trans.store (fun task ->
  let tg = find_target any every where task in
  let ta, (_, c) = intro_tg tg task in
  [ta], c)


(* Direction with a certificate *)
(* choose Left (A) or Right (B) when
    • the goal is of the form A ∨ B
    • the hypothesis is of the form A ∧ B *)
let cdir_pr d prg =
  Trans.decl_acc false (||) (fun decl found -> match decl.d_node with
    | Dprop (k, pr, t) when pr_equal pr prg && not found ->
        begin match k, t.t_node, d with
        | (Pgoal as k),           Tbinop (Tor, f, _),  false
        | (Pgoal as k),           Tbinop (Tor, _, f),  true
        | (Paxiom as k), Tbinop (Tand, f, _), false
        | (Paxiom as k), Tbinop (Tand, _, f), true ->
            [create_prop_decl k pr f], true
        | _ -> [decl], false end
    | _ -> [decl], false)

let cdir d where : ctrans =  Trans.store (fun task ->
  let pr = default_goal task where in
  let nt, b = cdir_pr d pr task in
  if b then [nt], lambda one (fun i -> dir d pr (Hole i))
  else [task], hole ())

(* Assert with certificate *)
let assert_h_t h t = Trans.decl_l (fun decl -> match decl.d_node with
  | Dprop (Pgoal, _, _) ->
      [ [create_prop_decl Pgoal h t]; [create_prop_decl Paxiom h t; decl] ]
  | _ -> [[decl]]) None

let cassert t : ctrans = Trans.store (fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let prg = task_goal task in
  Trans.apply (assert_h_t h t) task,
  lambda two (fun i j -> Assert (h, t, Clear (prg, Hole i), Hole j)))

(* Instantiate with certificate *)

let inst_tg t_inst target = Trans.decl_acc (target, hole ()) update_tg_c
   (fun decl (tg, _) -> match decl.d_node with
    | Dprop (k, pr, t) when match_tg tg pr ->
        begin match t.t_node, k with
        | Tquant (Tforall, _), Paxiom ->
            let hpr = create_prsymbol (gen_ident "H") in
            let t_subst = subst_forall t t_inst in
            [decl; create_prop_decl k hpr t_subst],
            Some (lambda one (fun i -> InstQuant (pr, hpr, t_inst, Hole i)))
        | Tquant (Texists, _), Pgoal ->
            let hpr = create_prsymbol (gen_ident "H") in
            let t_subst = subst_exist t t_inst in
            [create_prop_decl k hpr t_subst],
            Some (lambda one (fun i -> InstQuant (pr, hpr, t_inst, Clear (pr, Hole i))))
        | _ -> [decl], None end
    | _ -> [decl], None)

let inst t_inst where : ctrans = Trans.store (fun task ->
  let target = find_target false false where task in
  let ta, (_, c) = inst_tg t_inst target task in
  [ta], c)

(* Rewrite with a certificate *)

let rec intro_premises acc t = match t.t_node with
  | Tbinop (Timplies, f1, f2) -> intro_premises (f1::acc) f2
  | _ -> acc, t

let rewrite_in rev prh pri task = (* rewrites <h> in <i> with direction <rev> *)
  let nprh = pr_clone prh in
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when pr_equal pr prh ->
          let lp, f = intro_premises [] t in
          let revert, t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev
              then (fun c -> c), t1, t2
              else (fun c -> EqSym (nprh, c)), t2, t1
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev
              then (fun c -> c), t1, t2
              else iffsym_hyp nprh, t2, t1
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, revert, t1, t2)
      | _ -> acc)
      None
  in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Args_wrapper.Arg_error "Did not find rewrite hypothesis")
    | Some (lp, revert, t1, t2) ->
      Trans.fold_decl (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t) when pr_equal pr pri ->
            let new_term = t_replace t1 t2 t in
            Some (lp, revert, create_prop_decl p pr new_term)
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, revert, new_decl) ->
        let trans_rewriting =
          Trans.decl (fun decl -> match decl.d_node with
          | Dprop (_, pr, _) when pr_equal pr pri -> [new_decl]
          | _ -> [decl]) None in
        let list_par =
          List.map (fun t ->
              Trans.decl (fun decl -> match decl.d_node with
              | Dprop (Pgoal, pr, _) ->
                  [create_goal ~expl:"rewrite premises" pr t]
              | _ -> [decl])
            None) lp in
        let pr = task_goal task in
        let n = List.length lp + 1 in
        let cert =
          lambda (List n) (fun l ->
              let s = Stream.of_list l in
              let hole () = Hole (Stream.next s) in
              let apply _ c =
                Unfold (nprh, Split (nprh,
                Clear (pr, Swap (nprh, rename nprh pr (hole ()))),
                c)) in
              let rew_cert = Rewrite (nprh, pri, Clear (nprh, hole ())) in
              Duplicate (prh, nprh,
              List.fold_right apply lp (revert rew_cert))) in

        Trans.store (fun task ->
            Trans.apply (Trans.par (trans_rewriting :: list_par)) task,
            cert)
  in


  (* Composing previous functions *)
  Trans.apply (Trans.bind (Trans.bind found_eq lp_new) recreate_tasks) task

let rewrite g rev where : ctrans = Trans.store (fun task ->
  let h1 = default_goal task where in
  rewrite_in (not rev) g h1 task)

let exfalso : ctrans = Trans.store (fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
         [create_prop_decl Pgoal h t_false]
     | _ -> [decl]) None in
  let g = task_goal task in
  [Trans.apply trans task],
  lambda one (fun i -> Assert (h, t_false, Clear (g, Hole i), Trivial h)))

let case t : ctrans = Trans.store (fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl_l (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
         [ [create_prop_decl Paxiom h t; decl];
           [create_prop_decl Paxiom h (t_not t); decl] ]
     | _ -> [[decl]]) None in
  Trans.apply trans task,
  lambda two (fun i j->  Assert (h, t_not t, Swap (h, Hole i), Hole j)))

(* if formula <f> designed by <where> is a premise, dismiss the old
 goal and put <not f> in its place *)

let swap_pr gpr = Trans.fold_decl (fun d (opt_t, acc_task) -> match d.d_node with
  | Dprop (Paxiom, pr, t) when pr_equal gpr pr ->
      Some t, acc_task
  | _ -> opt_t, add_decl acc_task d) (None, None)

let swap where : ctrans = Trans.store (fun task ->
  let gpr = default_goal task where in
  let t, pr_goal = task_goal_fmla task, task_goal task in
  let _, hyp = task_separate_goal task in
  if pr_equal gpr pr_goal
  then let underlying_t = match t.t_node with Tnot t' -> t' | _ -> t in
       Trans.apply (compose (case underlying_t) (compose assumption exfalso)) task
  else
  let clues, nt = Trans.apply (swap_pr gpr) hyp in
  match clues with
  | Some t ->
      let not_t = match t.t_node with Tnot t' -> t' | _ -> t_not t in
      let decl = create_prop_decl Pgoal gpr not_t in
      [add_decl nt decl],
      lambda one (fun i -> Swap (gpr, Clear (pr_goal, Hole i)))
  | None -> [task], hole ())

let revert ls : ctrans = Trans.store (fun task ->
  let x = t_app_infer ls [] in
  let gpr = create_prsymbol (gen_ident "G") in
  let t, idg = task_goal_fmla task, task_goal task in
  let _, hyp = task_separate_goal task in
  let new_ident = id_fresh ls.ls_name.id_string in
  let new_var = create_vsymbol new_ident (Opt.get ls.ls_value) in
  let t = t_replace (t_app_infer ls []) (t_var new_var) t in
  let close_t = t_forall_close [new_var] [] t in
  let task = add_decl hyp (create_prop_decl Pgoal gpr close_t) in
  let prinst = create_prsymbol (gen_ident "Hinst") in
  [task],
  lambda one (fun i ->
      Assert (gpr, close_t,
        Clear (idg, Hole i),
        InstQuant (gpr, prinst, x, Axiom (prinst, idg)))))


(* Clear transformation with a certificate : *)
(*   removes hypothesis <g> from the task *)
let clear_one_d g = decl_cert (fun decl -> match decl.d_node with
  | Dprop (_, pr, _) when pr_equal g pr -> [], lambda one (fun i -> Clear (pr, Hole i))
  | _ -> [decl], hole ())

let clear_one g : ctrans = Trans.store (fun task ->
  let ta, c = clear_one_d g task in
  [ta], c)

(* UNSOUND : uses ∃ x. x = P, where P is a formula. Not first order logic. *)
(* let pose (name: string) (t: term) task =
 *   let ls = Term.create_lsymbol (gen_ident name) [] None in
 *   let ls_term = Term.t_app ls [] None in
 *   let new_constant = Decl.create_param_decl ls in
 *   let pr = create_prsymbol (gen_ident "H") in
 *   let eq = t_iff ls_term t in
 *   (\* hyp = [pr : vs = t] *\)
 *   let hyp =
 *     Decl.create_prop_decl Paxiom pr eq
 *   in
 *   let trans_new_task =
 *       Trans.add_decls [new_constant; hyp]
 *   in
 *   let h1 = id_register (gen_ident "Hpose") in
 *   let h2 = id_register (gen_ident "Hpose") in
 *   let id_cert = Unfold (h1,
 *                 Destruct (h1, h1, h2,
 *                 Swap_neg (h1, Axiom (h1, h2)))) in
 *   let eq_cert = Unfold (h1, Split (h1, id_cert, id_cert)) in
 *   [Trans.apply trans_new_task task],
 *   Assert (pr.pr_name,
 *        t_exists (t_close_quant [vs] [] eq),
 *        Inst_quant (pr.pr_name, h1, t, eq_cert),
 *        Intro_quant (pr.pr_name, vs.vs_name, Hole)) *)


(** Derived transformations with a certificate *)

let trivial = try_close [assumption; close; contradict]

let intros = repeat (intro false false None)

let split_logic any every where =
  compose (unfold any every where)
    (compose (split_or_and any every where)
       (destruct any every where))

let rec blast task =
    Trans.apply (
        repeat (ite (compose (compose (compose
                    trivial
                    (neg_decompose true false None))
                    (unfold true false None))
                    (destruct_all true false None))
                (Trans.store blast)
                id_ctrans))
      task

let blast : ctrans = Trans.store blast

let clear l = compose_list (List.map (fun pr -> clear_one pr) l)
