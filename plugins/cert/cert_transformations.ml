open Why3

open Theory
open Task
open Decl
open Term
open Ident
open Generic_arg_trans_utils
open Cert_syntax



(* Identity transformation with a certificate *)
let id task = [task], hole


(** Combinators on transformations with a certificate *)

(* Generalize ctrans on <task list * certif>, with the invariant that each <Hole> in the
   certif corresponds to one task in the list *)
let ctrans_gen (ctr : ctrans) ((ts, (r, g)) : task list * certif) =
  let rec fill acc (r, g) ts = match r with
    | Hole -> begin match ts with
              | [] -> assert false
              | t::ts -> let lt, ct = ctr t in
                         lt :: acc, ct, ts end
    | Axiom _ | Trivial -> acc, (r, g), ts
    | Cut (a, c1, c2) -> let acc, c1, ts = fill acc c1 ts in
                         let acc, c2, ts = fill acc c2 ts in
                         acc, (Cut (a, c1, c2), g), ts
    | Split (c1, c2) -> let acc, c1, ts = fill acc c1 ts in
                        let acc, c2, ts = fill acc c2 ts in
                        acc, (Split (c1, c2), g), ts
    | Unfold c -> let acc, c, ts = fill acc c ts in
                  acc, (Unfold c, g), ts
    | Swap_neg c -> let acc, c, ts = fill acc c ts in
                    acc, (Swap_neg c, g), ts
    | Destruct (h1, h2, c) -> let acc, c, ts = fill acc c ts in
                              acc, (Destruct (h1, h2, c), g), ts
    | Weakening c -> let acc, c, ts = fill acc c ts in
                     acc, (Weakening c, g), ts
    | Intro_quant (h, c) -> let acc, c, ts = fill acc c ts in
                            acc, (Intro_quant (h, c), g), ts
    | Inst_quant (i, h, c) -> let acc, c, ts = fill acc c ts in
                              acc, (Inst_quant (i, h, c), g), ts
    | Rewrite (h, path, rev, lc) ->
        let acc, lc, ts = List.fold_left (fun (acc, lc, ts) nc ->
                              let acc, c, ts = fill acc nc ts in
                              (acc, c::lc, ts)) (acc, [], ts) lc in
        acc, (Rewrite (h, path, rev, List.rev lc), g), ts
  in
  let acc, c, ts = fill [] (r, g) ts in
  assert (ts = []);
  Lists.rev_flatten acc, c

(* Apply a <ctrans> and then apply another <ctrans> on every <task> generated by the first one *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

let compose_list l = List.fold_left compose id l

(* If Then Else on transformations with a certificate :  *)
(*   applies [tri], if the task changed then apply [trt] else apply [tre] *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  let ((lt, (r, _)) as tri_task) = tri task in
  if not (Lists.equal task_equal lt [task] && r = Hole)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task

(* Try on transformations with a certificate : *)
(*   try each transformation in <lctr> and keep the one that closes the <task> *)
let rec try_close (lctr : ctrans list) : ctrans = fun task ->
  match lctr with
  | [] -> id task
  | h::t -> let lctask_h, cert_h = h task in
            if lctask_h = []
            then [], cert_h
            else try_close t task

(* Repeat on a transformation with a certificate : *)
(*   keep applying <ctr> as long as the task changes *)
let repeat (ctr : ctrans) : ctrans = fun task ->
  let gen_task = id task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task


(** Primitive transformations with a certificate *)

let default_goal task = function
  | Some pr -> pr
  | None -> task_goal task

(* Assumption with a certificate : *)
(*   closes the current task if the goal is an hypothesis *)
let assumption_decl tg decl = match decl.d_node with
  | Dprop (_, pr, t) when t_equal t tg ->
      Some pr.pr_name
  | _ -> None

let assumption_tdecl tg td = match td.td_node with
  | Decl decl -> assumption_decl tg decl
  | _ -> None

let rec assumption_ctxt tg = function
  | Some {task_decl = td; task_prev = task} ->
      begin match assumption_tdecl tg td with
      | Some h -> h
      | None -> assumption_ctxt tg task end
  | None -> raise Not_found

let assumption : ctrans = fun task ->
  let g, tg = try (task_goal task).pr_name, task_goal_fmla task
          with GoalNotFound -> invalid_arg "Cert_transformations.assumption" in
  let _, hyp = task_separate_goal task in
  try let h = assumption_ctxt tg hyp in
      [], (Axiom h, g)
  with Not_found -> [task], hole

(* Closes task when if hypotheses contain false or if the goal is true *)
let close : ctrans = fun task ->
  let trans = Trans.fold_decl (fun d acc -> match d.d_node, acc with
      | _, Some _ -> acc
      | Dprop (k, pr, t), _ ->
          begin match k, t.t_node with
          | Pgoal, Ttrue | (Plemma | Paxiom), Tfalse -> Some pr
          | _ -> acc
          end
      | _ -> acc) None in
  match Trans.apply trans task with
  | Some pr -> [], (Trivial, pr.pr_name)
  | None -> [task], hole

(* Split with a certificate : *)
(* destructs a logical constructor at the top of the formula *)
let destruct where task = (* destructs /\ in the hypotheses *)
  let g = (default_goal task where).pr_name in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match k, t.t_node with
        | k, Tbinop (Tand, f1, f2) when k <> Pgoal ->
            let pr1 = create_prsymbol (id_clone g) in
            let pr2 = create_prsymbol (id_clone g) in
            clues := Some (pr1.pr_name, pr2.pr_name);
            [create_prop_decl k pr1 f1; create_prop_decl k pr2 f2]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some (h1, h2) -> [nt], (Destruct (h1, h2, hole), g)
  | None -> [task], hole

let unfold where task = (* replaces A <-> B with (A -> B) /\ (B -> A) *)
                        (* and A -> B with ¬A ∨ B *)
  let g = (default_goal task where).pr_name in
  let clues = ref false in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match t.t_node with
        | Tbinop (Tiff, f1, f2) ->
            clues := true;
            let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
            [create_prop_decl k pr destr_iff]
        | Tbinop (Timplies, f1, f2) ->
            clues := true;
            let destr_imp = t_or (t_not f1) f2 in
            [create_prop_decl k pr destr_imp]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  if !clues then [nt], (Unfold hole, g)
  else [task], hole

let split_or_and where task = (* destructs /\ in the goal or \/ in the hypothses *)
  let g = (default_goal task where).pr_name in
  let clues = ref false in
  let trans_t = Trans.decl_l (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match k, t.t_node with
        | Pgoal as k, Tbinop (Tand, f1, f2)
        | (Paxiom | Plemma as k), Tbinop (Tor, f1, f2) ->
            clues := true;
            [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]]
        | _ -> [[d]] end
    | _ -> [[d]]) None in
  let nt = Trans.apply trans_t task in
  if !clues then nt, (Split (hole, hole), g)
  else [task], hole


(* the next 2 functions are copied from introduction.ml *)
let intro_attrs = Sattr.singleton Inlining.intro_attr

let ls_of_vs vs =
  let id = id_clone ~attrs:intro_attrs vs.vs_name in
  create_fsymbol id [] vs.vs_ty

let intro where task =
  (* introduces hypothesis H : A when the goal is of the form A → B or
     introduces variable x when the goal is of the form ∀ x. P x
     introduces variable x when a hypothesis is of the form ∃ x. P x *)
  let gpr = default_goal task where in
  let hpr = create_prsymbol (id_fresh "H") in
  let h = hpr.pr_name and g = gpr.pr_name in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match t.t_node, k with
        | Tbinop (Timplies, f1, f2), Pgoal ->
            clues := Some (Unfold (Destruct (h, g, (Swap_neg hole, h)), g), g);
            [create_prop_decl Paxiom hpr f1;
             create_prop_decl Pgoal gpr f2]
        | Tquant (Tforall, f), (Pgoal as k) | Tquant (Texists, f), (Paxiom | Plemma as k) ->
            let vsl, _, f_t = t_open_quant f in
            begin match vsl with
            | [vs] ->
                let ls = ls_of_vs vs in
                let subst = Mvs.singleton vs (fs_app ls [] vs.vs_ty) in
                let f = t_subst subst f_t in
                clues := Some (Intro_quant (ls.ls_name, hole), gpr.pr_name);
                [create_param_decl ls; create_prop_decl k gpr f]
            | _ -> assert false
            end
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | None -> [task], hole
  | Some c -> [nt], c


let dir_smart d c g =
  let h = id_register (id_fresh "Weaken") in
  let left, right = match d with Left -> g, h | Right -> h, g in
  Destruct (left, right, (Weakening c, h)), g

(* Direction with a certificate *)
(* choose Left (A) or Right (B) when
    • the goal is of the form A ∨ B
    • the hypothesis is of the form A ∧ B *)
let dir d where task =
  let g = (default_goal task where).pr_name in
  let clues = ref false in
  let trans_t = Trans.decl (fun decl -> match decl.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match k, t.t_node, d with
        | (Pgoal as k),           Tbinop (Tor, f, _),  Left
        | (Pgoal as k),           Tbinop (Tor, _, f),  Right
        | (Paxiom | Plemma as k), Tbinop (Tand, f, _), Left
        | (Paxiom | Plemma as k), Tbinop (Tand, _, f), Right ->
            clues := true;
            [create_prop_decl k pr f]
        | _ -> [decl] end
    | _ -> [decl]) None in
  let nt = Trans.apply trans_t task in
  if !clues then [nt], dir_smart d hole g
  else [task], hole

let left = dir Left None
let right = dir Right None

(* Assert with certificate *)
let cut t task =
  let h = create_prsymbol (gen_ident "H") in
  let trans_t = Trans.decl_l (fun decl -> match decl.d_node with
    | Dprop (Pgoal, _, _) ->
        [ [create_prop_decl Pgoal h t]; [create_prop_decl Paxiom h t; decl] ]
    | _ -> [[decl]]) None in
  let idg = (task_goal task).pr_name in
  let ct = translate_term t in
  Trans.apply trans_t task, (Cut (ct, (Weakening hole, idg), hole), h.pr_name)

(* Instantiate with certificate *)
let inst t_inst where task =
  let g = (default_goal task where).pr_name in
  let ct_inst = translate_term t_inst in
  let hpr = create_prsymbol (gen_ident "H") in
  let clues = ref None in
  let trans_t = Trans.decl (fun decl -> match decl.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match t.t_node, k with
        | Tquant (Tforall, _), (Plemma | Paxiom) ->
            let t_subst = subst_forall t t_inst in
            clues := Some (Inst_quant (hpr.pr_name, ct_inst, hole), g);
            [decl; create_prop_decl k hpr t_subst]
        | Tquant (Texists, _), Pgoal ->
            let t_subst = subst_exist t t_inst in
            clues := Some (Inst_quant (hpr.pr_name, ct_inst, (Weakening hole, g)), g);
            [create_prop_decl k hpr t_subst]
        | _ -> [decl] end
    | _ -> [decl]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> [nt], c
  | None -> [task], hole

(* Rewrite with a certificate *)
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

let rewrite_in rev h h1 task = (* rewrites <h> in <h1> with direction <rev> *)
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
                  clues := Some (path, hole :: List.map (fun _ -> hole) lp);
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
        Trans.decl (fun decl -> match decl.d_node with
        | Dprop (p, pr, _) when id_equal pr.pr_name h1 && (p = Paxiom || p = Pgoal) ->
            [new_decl]
        | _ -> [decl]) None in
      let list_par =
        List.map (fun t ->
            Trans.decl (fun decl -> match decl.d_node with
            | Dprop (Pgoal, pr, _) ->
                [create_goal ~expl:"rewrite premises" pr t]
            | _ -> [decl])
          None) lp in
      Trans.par (trans_rewriting :: list_par) in


  (* Composing previous functions *)
  let gen_task = Trans.apply (Trans.bind (Trans.bind found_eq lp_new) recreate_tasks) task in
  match !clues with
  | None -> [task], hole
  | Some (path, lc) ->
      gen_task, (Rewrite (h, path, rev, lc), h1)

let rewrite g rev where task =
  let h1 = default_goal task where in
  rewrite_in (not rev) g h1 task

let exfalso : ctrans = fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
         [create_prop_decl Pgoal h t_false]
     | _ -> [decl]) None in
  let g = task_goal task in
  [Trans.apply trans task],
  (Cut (CTfalse, (Weakening hole, g.pr_name), (Trivial, h.pr_name)), h.pr_name)

let case t = fun task ->
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl_l (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
            [ [create_prop_decl Paxiom h t; decl];
              [create_prop_decl Paxiom h (t_not t); decl] ]
     | _ -> [[decl]]) None in
  let not_ct = CTnot (translate_term t) in
  Trans.apply trans task,
  (Cut (not_ct, (Swap_neg hole, h.pr_name), hole),
   h.pr_name)

let swap where task = (* if formula <f> designed by <where> is in the context, dismiss the old
 goal and put <not f> in its place *)
  let gpr = default_goal task where in
  let term_goal, id_goal = task_goal_fmla task, (task_goal task).pr_name in
  if id_equal gpr.pr_name id_goal
  then compose (case term_goal) (compose assumption exfalso) task
  else
  let _, hyp = task_separate_goal task in
  let trans_t = Trans.fold_decl (fun d (opt_t, acc_task) -> match d.d_node with
    | Dprop ((Paxiom | Plemma), pr, t) when id_equal gpr.pr_name pr.pr_name ->
        Some t, acc_task
    | _ -> opt_t, add_decl acc_task d) (None, None) in
  let clues, nt = Trans.apply trans_t hyp in
  match clues with
  | Some t ->
      let not_t = match t.t_node with Tnot t' -> t' | _ -> t_not t in
      let decl = create_prop_decl Pgoal gpr not_t in
      [add_decl nt decl], (Swap_neg (Weakening hole, id_goal), gpr.pr_name)
  | None -> [task], hole

let revert ls task =
  let gpr = create_prsymbol (gen_ident "G") in
  let t, idg = task_goal_fmla task, task_goal task in
  let _, hyp = task_separate_goal task in
  let new_ident = id_fresh ls.ls_name.id_string in
  let new_var = create_vsymbol new_ident (Opt.get ls.ls_value) in
  let t = t_replace (t_app_infer ls []) (t_var new_var) t in
  let close_t = t_forall_close [new_var] [] t in
  let task = add_decl hyp (create_prop_decl Pgoal gpr close_t) in
  let hinst = id_register (gen_ident "Hinst") in
  [task],
  (Cut (translate_term close_t,
        (Weakening hole, idg.pr_name),
        (Inst_quant (hinst, CTfvar ls.ls_name, (Axiom hinst, idg.pr_name)), gpr.pr_name)),
   gpr.pr_name)


(* Clear transformation with a certificate : *)
(*   removes hypothesis <g> from the task *)
let clear_one g task =
  let trans = Trans.decl (fun decl -> match decl.d_node with
    | Dprop (_, pr, _) when id_equal g pr.pr_name -> []
    | _ -> [decl]) None in
  [Trans.apply trans task], (Weakening hole, g)



let pose (name: string) (t: term) : ctrans = fun task ->
  let ls_ident = gen_ident name in
  let ls = Term.create_lsymbol ls_ident [] None in
  let ls_term = Term.t_app ls [] None in
  let new_constant = Decl.create_param_decl ls in
  let pr = create_prsymbol (gen_ident "H") in
  let eq = t_iff ls_term t in
  (* hyp = [pr : ls = t] *)
  let hyp =
    Decl.create_prop_decl Paxiom pr eq
  in
  let trans_new_task =
      Trans.add_decls [new_constant; hyp]
  in
  let hpose = id_register (gen_ident "Hpose") in
  let hposet = id_register (gen_ident "Hpose") in
  let id_cert = Unfold (Destruct (hpose, hposet, (Swap_neg (Axiom hpose, hposet), hpose)),
                hpose), hpose in
  let eq_cert = Unfold (Split (id_cert, id_cert), hpose), hpose in
  let ct = translate_term t in
  [Trans.apply trans_new_task task],
  (Cut (CTquant (CTexists, CTbinop (Tiff, CTbvar 0, ct)),
        (Inst_quant (hpose, ct, eq_cert),
         pr.pr_name),
        (Intro_quant (ls.ls_name, hole), pr.pr_name)
     ),
   pr.pr_name)


(** Derived transformations with a certificate *)

let trivial = try_close [assumption; close]

let intros = repeat (intro None)

let split_logic where = compose (unfold where)
                          (compose (split_or_and where)
                             (destruct where))

let rec intuition task =
  repeat (compose assumption
            (compose (intro None)
               (compose (split_logic None)
                  (try_close [ite left intuition id;
                              ite right intuition id])))) task

let clear l = compose_list (List.map (fun pr -> clear_one pr.pr_name) l)
