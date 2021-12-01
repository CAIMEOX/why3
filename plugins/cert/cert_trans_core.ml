open Why3
open Task
open Decl
open Term
open Ident
open Ty
open Generic_arg_trans_utils

open Cert_certificates
open Cert_trans_utils

(* To debug *)
let tprint_tg target =
  Trans.decl_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (_, pr, t) when match_tg tg pr ->
          Format.eprintf "%a : %a@." Pretty.print_pr pr Pretty.print_term t;
          [d], None
      | _ -> [d], None)

let tprint any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let ta, (_, c) = tprint_tg tg task in
      [ta], c)


(* Assumption with a certificate : *)
let assumption_pr_t prg tg =
  decl_l_cert (fun d ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when t_equal t tg -> [], axiom pr prg
      | _ -> [[d]], idc)

let assumption : ctrans = Trans.store (fun task ->
  let prg, tg = task_goal task, task_goal_fmla task in
  assumption_pr_t prg tg task)

let find_contradict =
  Trans.fold_decl (fun d (m, found, (cert : scert)) ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when not found ->
          let un_not_t = match t.t_node with Tnot t -> t | _ -> t_not t in
          let found, new_cert =
            match Mterm.(find_opt (t_not t) m, find_opt un_not_t m) with
            | Some g, _ | _, Some g -> true, swap g ++ axiom pr g
            | _ -> false, cert in
          Mterm.add t pr m, found, new_cert
      | _ -> m, found, cert) (Mterm.empty, false, idc)

let contradict : ctrans =
  Trans.store (fun task ->
      let _, found, c = Trans.apply find_contradict task in
      let res_task = if found then [] else [task] in
      res_task, c)

let ren pr1 =
  decl_cert  (fun d ->
      match d.d_node with
      | Dprop (k, pr, t) when pr_equal pr pr1 ->
          let pr2 = pr_clone pr1 in
          [create_prop_decl k pr2 t],
          rename pr1 pr2
      | _ -> [d], idc)

let crename pr1 : ctrans =
  Trans.store (fun task ->
      let ta, c = ren pr1 task in
      [ta], c)


(* Closes task if hypotheses contain false or if the goal is true or reflexivity
   of equality *)
let close : ctrans =
  Trans.store (fun task ->
      let trans =
        Trans.fold_decl (fun d acc ->
            match d.d_node, acc with
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
      | Some pr -> [], trivial pr
      | None -> [task], idc)


(* Split with a certificate : destructs a logical constructor at the top of the
   formula or destructs /\ in the hypotheses *)

let destruct_tg target =
  Trans.decl_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (Paxiom, pr, {t_node = Tbinop (Tand, f1, f2)})
          when match_tg tg pr ->
          let pr1 = pr_clone pr in
          let pr2 = pr_clone pr in
          [create_prop_decl Paxiom pr1 f1; create_prop_decl Paxiom pr2 f2],
          Some (destruct pr pr1 pr2)
      | _ -> [d], None)

let destruct_and any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let ta, (_, c) = destruct_tg tg task in
      [ta], c)

(* destructs /\ in the goal or \/ in the hypotheses *)
let split_or_and_tg target =
  Trans.decl_l_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (k, pr, t) when match_tg tg pr ->
          begin match k, t.t_node with
          | (Pgoal as k), Tbinop (Tand, f1, f2)
          | (Paxiom as k), Tbinop (Tor, f1, f2) ->
              [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]],
              Some (split pr)
          | _ -> [[d]], None end
      | _ -> [[d]], None)

let split_or_and any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let lta, (_, c) = split_or_and_tg tg task in
      lta, c)

let destruct_all_tg target =
  Trans.decl_l_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (k, pr, t) when match_tg tg pr ->
          begin match k, t.t_node with
          | (Paxiom as k), Tbinop (Tand, f1, f2) ->
              let pr1 = pr_clone pr in
              let pr2 = pr_clone pr in
              [[create_prop_decl k pr1 f1; create_prop_decl k pr2 f2]],
              Some (destruct pr pr1 pr2)
          | (Pgoal as k), Tbinop (Tand, f1, f2)
          | (Paxiom as k), Tbinop (Tor, f1, f2) ->
              [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]],
              Some (split pr)
          | Pgoal, Tbinop (Tor, f1, f2) ->
              let prh = pr_clone pr in
              [[create_prop_decl Paxiom prh (t_not_simp f1);
                create_prop_decl Pgoal pr f2]],
              Some (destruct pr prh pr ++ swap prh)
          | _ -> [[d]], None end
      | _ -> [[d]], None)

let destruct_all any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let lta, (_, c) = destruct_all_tg tg task in
      lta, c)

let neg_decompose_tg target =
  Trans.decl_l_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (k, pr, t) when match_tg tg pr ->
          begin match t.t_node with
          | Tnot nt ->
              begin match k, nt.t_node with
              | k, Tnot nnt -> (* double negation *)
                  [[create_prop_decl k pr nnt]],
                  Some (swap pr ++ swap pr)
              | Paxiom, Tbinop (Tor, f1, f2) -> (* destruct *)
                  let pr1 = pr_clone pr in
                  let pr2 = pr_clone pr in
                  [[create_prop_decl Paxiom pr1 (t_not_simp f1);
                    create_prop_decl Paxiom pr2 (t_not_simp f2)]],
                  Some (swap pr ++ destruct pr pr1 pr2 ++ swap pr1 ++ swap pr2)
              | Pgoal, Tbinop (Tand, f1, f2) ->
                  let pr1 = pr_clone pr in
                  let pr2 = pr_clone pr in
                  [[create_prop_decl Paxiom pr1 f1;
                    create_prop_decl Pgoal pr2 (t_not_simp f2)]],
                  Some (swap pr ++ destruct pr pr1 pr2 ++ swap pr2)
              | Paxiom, Tbinop (Tand, f1, f2) -> (* split *)
                  [[create_prop_decl Paxiom pr (t_not_simp f1)];
                   [create_prop_decl Paxiom pr (t_not_simp f2)]],
                  Some (swap pr ++ split pr ++ swap pr)
              | Pgoal, Tbinop (Tor, f1, f2) ->
                  [[create_prop_decl Pgoal pr (t_not_simp f1)];
                   [create_prop_decl Pgoal pr (t_not_simp f2)]],
                  Some (swap pr ++ split pr ++ swap pr)
              | Pgoal, Ttrue -> (* ⊥ and ⊤ *)
                  [[create_prop_decl Pgoal pr t_false]],
                  Some (clear pr ++ assertion pr t_false +++
                          [idc; trivial pr])
              | Pgoal, Tfalse ->
                  [], Some (swap pr ++ trivial pr)
              | Paxiom, Tfalse ->
                  [[]], Some (clear pr)
              | Paxiom, Ttrue ->
                  [], Some (swap pr ++ trivial pr)
              | k, Tbinop (Tiff, f1, f2) -> (* unfold *)
                  let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
                  [[create_prop_decl k pr destr_iff]],
                  Some (swap pr ++ unfold pr ++ swap pr)
              | k, Tbinop (Timplies, f1, f2) ->
                  let destr_imp = t_or (t_not f1) f2 in
                  [[create_prop_decl k pr destr_imp]],
                  Some (swap pr ++ unfold pr ++ swap pr)
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
  Trans.decl_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (k, pr, t) when match_tg tg pr ->
          begin match t.t_node with
          | Tbinop (Tiff, f1, f2)  ->
              let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
              [create_prop_decl k pr destr_iff],
              Some (unfold pr)
          | Tbinop (Timplies, f1, f2) ->
              let destr_imp = t_or (t_not f1) f2 in
              [create_prop_decl k pr destr_imp],
              Some (unfold pr)
          | _ -> [d], None end
      | _ -> [d], None)

let unfold_hyp_arr any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let ta, (_, c) = unfold_tg tg task in
      [ta], c)

(* the next 2 functions are copied from introduction.ml *)
let intro_attrs = Sattr.singleton Inlining.intro_attr

let ls_of_vs vs =
  let id = id_clone ~attrs:intro_attrs vs.vs_name in
  create_fsymbol id [] vs.vs_ty

let intro_tg target =
  Trans.decl_acc (target, idc) update_tg_c (fun d (tg, _) ->
      match d.d_node with
      | Dprop (k, pr, t) when match_tg tg pr ->
          let alphas = Stv.elements (t_ty_freevars Stv.empty t) in
          let t, ldecla, cty_intro = match alphas with
            | [] -> t, [], idc
            | _ -> let lts = List.map (fun _ -> create_tysymbol (id_fresh "a") [] NoDef) alphas in
                   let ldecla = List.map create_ty_decl lts in
                   let lty = List.map (fun ts -> ty_app ts []) lts in
                   let subst = Mtv.of_list (List.combine alphas lty) in
                   let _, t = t_subst_types subst Mvs.empty t in
                   t, ldecla, introtype pr lts in
          begin match t.t_node, k with
          | Tbinop (Timplies, f1, f2), Pgoal ->
              let hpr = create_prsymbol (id_fresh "H") in
              ldecla @ [create_prop_decl Paxiom hpr f1; create_prop_decl Pgoal pr f2],
              Some (cty_intro ++ unfold pr ++ destruct pr hpr pr ++ swap hpr)
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
                  ldecla @ [create_param_decl ls; create_prop_decl k pr f],
                  Some (cty_intro ++ introquant pr ls)
              | [] -> assert false
              end
          | _ -> [d], None end
      | _ -> [d], None)

(* introduces hypothesis H : A when the goal is of the form A → B or introduces
   variable x when the goal is of the form ∀ x. P x introduces variable x when a
   hypothesis is of the form ∃ x. P x *)
let intro any every where : ctrans =
  Trans.store (fun task ->
      let tg = find_target any every where task in
      let ta, (_, c) = intro_tg tg task in
      [ta], c)

(* Direction with a certificate *)
(* choose Left (A) or Right (B) when
    • the goal is of the form A ∨ B
    • the hypothesis is of the form A ∧ B *)
let cdir_pr d prg =
  Trans.decl_acc false (||) (fun decl found ->
      match decl.d_node with
      | Dprop (k, pr, t) when pr_equal pr prg && not found ->
          begin match k, t.t_node, d with
          | (Pgoal as k),           Tbinop (Tor, f, _),  false
          | (Pgoal as k),           Tbinop (Tor, _, f),  true
          | (Paxiom as k), Tbinop (Tand, f, _), false
          | (Paxiom as k), Tbinop (Tand, _, f), true ->
              [create_prop_decl k pr f], true
          | _ -> [decl], false end
      | _ -> [decl], false)

let cdir d where : ctrans =
  Trans.store (fun task ->
      let pr = default_goal task where in
      let nt, found = cdir_pr d pr task in
      if found then [nt], dir d pr
      else [task], idc)

(* Assert with certificate *)
let assert_h_t h t =
  Trans.decl_l (fun decl ->
      match decl.d_node with
      | Dprop (Pgoal, _, _) ->
          [[create_prop_decl Pgoal h t];
           [create_prop_decl Paxiom h t; decl]]
      | _ -> [[decl]]) None

let cassert t : ctrans =
  Trans.store (fun task ->
      let h = create_prsymbol (gen_ident "H") in
      let prg = task_goal task in
      Trans.apply (assert_h_t h t) task,
      assertion h t +++ [clear prg; idc])

(* Instantiate with certificate *)

let inst_tg t_inst target = Trans.decl_acc (target, idc) update_tg_c
   (fun decl (tg, _) ->
     match decl.d_node with
     | Dprop (k, pr, t) when match_tg tg pr ->
         begin match t.t_node, k with
         | Tquant (Tforall, _), Paxiom ->
             let hpr = create_prsymbol (gen_ident "H") in
             let t_subst = subst_forall t t_inst in
             [decl; create_prop_decl k hpr t_subst],
             Some (instquant pr hpr t_inst)
         | Tquant (Texists, _), Pgoal ->
             let hpr = create_prsymbol (gen_ident "H") in
             let t_subst = subst_exist t t_inst in
             [create_prop_decl k hpr t_subst],
             Some (instquant pr hpr t_inst ++ clear pr)
         | _ -> [decl], None end
     | _ -> [decl], None)

let inst t_inst where : ctrans =
  Trans.store (fun task ->
      let target = find_target false false where task in
      let ta, (_, c) = inst_tg t_inst target task in
      [ta], c)


let exfalso : ctrans =
  Trans.store (fun task ->
      let h = create_prsymbol (gen_ident "H") in
      let trans =
        Trans.decl (fun decl ->
            match decl.d_node with
            | Dprop (Pgoal, _, _) ->
                [create_prop_decl Pgoal h t_false]
            | _ -> [decl]) None in
      let g = task_goal task in
      [Trans.apply trans task],
      assertion h t_false +++ [clear g; trivial h])

let case t : ctrans = Trans.store (fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let trans =
    Trans.decl_l (fun decl ->
        match decl.d_node with
        | Dprop (Pgoal, _, _) ->
            [ [create_prop_decl Paxiom h t; decl];
              [create_prop_decl Paxiom h (t_not t); decl] ]
        | _ -> [[decl]]) None in
  Trans.apply trans task,
  assertion h (t_not t) +++ [swap h; idc])

(* if formula <f> designed by <where> is a premise, dismiss the old
 goal and put <not f> in its place *)
let swap_pr gpr =
  Trans.fold_decl (fun d (opt_t, acc_task) ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when pr_equal gpr pr ->
          Some t, acc_task
      | _ -> opt_t, add_decl acc_task d) (None, None)

let swap where : ctrans =
  Trans.store (fun task ->
      let gpr = default_goal task where in
      let t, pr_goal = task_goal_fmla task, task_goal task in
      let _, hyp = task_separate_goal task in
      if pr_equal gpr pr_goal
      then let underlying_t = match t.t_node with Tnot t' -> t' | _ -> t in
           Trans.apply (compose (case underlying_t)
                          (compose assumption exfalso)) task
      else
        let clues, nt = Trans.apply (swap_pr gpr) hyp in
        match clues with
        | Some t ->
            let not_t = match t.t_node with Tnot t' -> t' | _ -> t_not t in
            let decl = create_prop_decl Pgoal gpr not_t in
            [add_decl nt decl],
            swap gpr ++ clear pr_goal
        | None -> [task], idc)

let revert ls : ctrans =
  Trans.store (fun task ->
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
      let cert = assertion gpr close_t +++
                   [clear idg;
                    instquant gpr prinst x ++ axiom prinst idg] in
      [task], cert)


(* clear transformation with a certificate, removes formula <g> from the task *)
let clear_one_d g =
  decl_cert (fun decl ->
      match decl.d_node with
      | Dprop (_, pr, _) when pr_equal g pr ->
          [], clear pr
      | _ -> [decl], idc)

let clear_one g : ctrans =
  Trans.store (fun task ->
      let ta, c = clear_one_d g task in
      [ta], c)

(** Derived transformations with a certificate *)

let trivial = try_close [assumption; close; contradict]

let intros = repeat (intro false false None)

let split_logic any every where =
  compose (unfold_hyp_arr any every where)
    (compose (split_or_and any every where)
       (destruct_and any every where))

let rec blast task =
    Trans.apply (
        repeat (ite (compose (compose (compose
                    trivial
                    (neg_decompose true false None))
                    (unfold_hyp_arr true false None))
                    (destruct_all true false None))
                (Trans.store blast)
                id_ctrans))
      task

let blast : ctrans = Trans.store blast

let clear l = compose_list (List.map (fun pr -> clear_one pr) l)
