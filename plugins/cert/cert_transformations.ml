open Why3

open Theory
open Task
open Decl
open Term
open Ident
open Generic_arg_trans_utils

open Cert_certificates

(* Identity transformation with a certificate *)
let id_ctrans task = [task], Hole


(** Combinators on transformations with a certificate *)

(* Generalize ctrans on <task list * certif>, with the invariant that each <Hole> in the
   certif corresponds to one task in the list *)
let ctrans_gen (ctr : ctrans) (ts, c : task list * certif) =
  let llt, lc = List.split (List.map ctr ts) in
  List.flatten llt, c |>>> lc

  (* let rec fill acc c' ts = match c' with
   *   | Nc -> raise Not_certified
   *   | Hole -> begin match ts with
   *             | [] -> assert false
   *             | t::ts -> let lt, ct = ctr t in
   *                        lt :: acc, ct, ts end
   *   | Axiom _ | Trivial _ -> acc, c', ts
   *   | Cut (i, a, c1, c2) -> let acc, c1, ts = fill acc c1 ts in
   *                           let acc, c2, ts = fill acc c2 ts in
   *                           acc, Cut (i, a, c1, c2), ts
   *   | Split (i, c1, c2) -> let acc, c1, ts = fill acc c1 ts in
   *                          let acc, c2, ts = fill acc c2 ts in
   *                          acc, Split (i, c1, c2), ts
   *   | Unfold (i, c) -> let acc, c, ts = fill acc c ts in
   *                      acc, Unfold (i, c), ts
   *   | Swap_neg (i, c) -> let acc, c, ts = fill acc c ts in
   *                        acc, Swap_neg (i, c), ts
   *   | Destruct (i, j1, j2, c) -> let acc, c, ts = fill acc c ts in
   *                                acc, Destruct (i, j1, j2, c), ts
   *   | Construct (i1, i2, j, c) -> let acc, c, ts = fill acc c ts in
   *                                 acc, Construct (i1, i2, j, c), ts
   *   | Weakening (i, c) -> let acc, c, ts = fill acc c ts in
   *                         acc, Weakening (i, c), ts
   *   | Intro_quant (i, y, c) -> let acc, c, ts = fill acc c ts in
   *                              acc, Intro_quant (i, y, c), ts
   *   | Inst_quant (i, j, t, c) -> let acc, c, ts = fill acc c ts in
   *                                acc, Inst_quant (i, j, t, c), ts
   *   | Rewrite (i, j, path, rev, lc) ->
   *       let acc, lc, ts = List.fold_left (fun (acc, lc, ts) nc ->
   *                             let acc, c, ts = fill acc nc ts in
   *                             (acc, c::lc, ts)) (acc, [], ts) lc in
   *       acc, Rewrite (i, j, path, rev, List.rev lc), ts
   * in
   * let acc, c, ts = fill [] c ts in
   * assert (ts = []);
   * Lists.rev_flatten acc, c *)

(* Apply a <ctrans> and then apply another <ctrans> on every <task> generated by the first one *)
let compose (tr1 : ctrans) (tr2 : ctrans) : ctrans = fun task ->
  tr1 task |> ctrans_gen tr2

let compose_list l = List.fold_left compose id_ctrans l

(* If Then Else on transformations with a certificate :  *)
(*   applies [tri], if the task changed then apply [trt] else apply [tre] *)
let ite (tri : ctrans) (trt : ctrans) (tre : ctrans) : ctrans = fun task ->
  let (lt, c) as tri_task = tri task in
  if not (Lists.equal task_equal lt [task] && c = Hole)
  then ctrans_gen trt tri_task
  else ctrans_gen tre tri_task

(* Try on transformations with a certificate : *)
(*   try each transformation in <lctr> and keep the one that closes the <task> *)
let rec try_close (lctr : ctrans list) : ctrans = fun task ->
  match lctr with
  | [] -> id_ctrans task
  | h::t -> let lctask_h, cert_h = h task in
            if lctask_h = []
            then [], cert_h
            else try_close t task

(* Repeat on a transformation with a certificate : *)
(*   keep applying <ctr> as long as the task changes *)
let repeat (ctr : ctrans) : ctrans = fun task ->
  let gen_task = id_ctrans task in
  let gen_tr = ctrans_gen ctr in
  let rec loop gt =
    let new_gt = gen_tr gt in
    if Lists.equal task_equal (fst new_gt) (fst gt)
    then gt
    else loop new_gt in
  loop gen_task


(** Primitive transformations with a certificate *)

(* First, some utility functions *)
let default_goal task = function
  | Some pr -> pr
  | None -> task_goal task

type target =
  | Pr of prsymbol
  | Everywhere
  | Nowhere

let tg omni where task =
  let v = if omni then Everywhere else Pr (default_goal task where) in
  ref v

let is_target pr tg = match !tg with
  | Nowhere -> false
  | Everywhere -> tg := Nowhere; true
  | Pr tg_pr -> id_equal pr.pr_name tg_pr.pr_name

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

let assumption task =
  let g, tg = try (task_goal task).pr_name, task_goal_fmla task
          with GoalNotFound -> invalid_arg "Cert_transformations.assumption" in
  let _, hyp = task_separate_goal task in
  try let h = assumption_ctxt tg hyp in
      [], Axiom (h, g)
  with Not_found -> [task], Hole

let add k v tbl = tbl := (k, v) :: !tbl

let rec assoc term = function
  | [] -> raise Not_found
  | (k, v)::tail -> if t_equal k term then v else assoc term tail

let find_opt t tbl = try Some (assoc t !tbl)
                     with Not_found -> None

let contradict task =
  let tbl = ref [] in
  let prem_trans = Trans.fold_decl (fun d () -> match d.d_node with
    | Dprop (k, pr, t) when k <> Pgoal ->
        add t pr.pr_name tbl
    | _ -> ()) () in
  let _ = Trans.apply prem_trans task in
  let trans = Trans.fold_decl (fun d acc -> match d.d_node, acc with
    | Dprop (k, pr, t), None when k <> Pgoal ->
        begin match find_opt (t_not t) tbl with
        | Some g -> Some (pr.pr_name, g)
        | None -> acc end
    | _ -> acc) None in
  match Trans.apply trans task with
  | Some (h, g) -> [], Swap_neg (g, Axiom (h, g))
  | _ ->
      (* let open Format in
       * let out = open_out "/tmp/hyp_tbl.log" in
       * let fmt = formatter_of_out_channel out in
       * List.iter (fun (t, pr) ->
       *     fprintf fmt "%a : %a\n@."
       *       pri pr
       *       pcte (translate_term t)) !tbl;
       * close_out out; *)
      [task], Hole


(* Closes task when if hypotheses contain false or if the goal is true *)
let close task =
  let trans = Trans.fold_decl (fun d acc -> match d.d_node, acc with
      | _, Some _ -> acc
      | Dprop (k, pr, t), _ ->
          begin match k, t.t_node with
          | Pgoal, Ttrue | Paxiom, Tfalse -> Some pr
          | _ -> acc
          end
      | _ -> acc) None in
  match Trans.apply trans task with
  | Some pr -> [], Trivial pr.pr_name
  | None -> [task], Hole

(* Split with a certificate : *)
(* destructs a logical constructor at the top of the formula *)
let destruct omni where task = (* destructs /\ in the hypotheses *)
  let target = tg omni where task in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        begin match k, t.t_node with
        | k, Tbinop (Tand, f1, f2) when k <> Pgoal ->
            if is_target pr target then begin
                let g = pr.pr_name in
                let pr1 = create_prsymbol (id_clone g) in
                let pr2 = create_prsymbol (id_clone g) in
                clues := Some (Destruct (g, pr1.pr_name, pr2.pr_name, Hole));
                [create_prop_decl k pr1 f1; create_prop_decl k pr2 f2] end
            else [d]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> [nt], c
  | None -> [task], Hole

let split_or_and omni where task = (* destructs /\ in the goal or \/ in the hypothses *)
  let target = tg omni where task in
  let clues = ref None in
  let trans_t = Trans.decl_l (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        begin match k, t.t_node with
        | (Pgoal as k), Tbinop (Tand, f1, f2)
        | (Paxiom as k), Tbinop (Tor, f1, f2) ->
            if is_target pr target then begin
                clues := Some pr;
                [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]] end
            else [[d]]
        | _ -> [[d]] end
    | _ -> [[d]]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some gpr -> nt, Split (gpr.pr_name, Hole, Hole)
  | None -> [task], Hole

let destruct_all omni where task =
  let target = tg omni where task in
  let clues = ref None in
  let trans_t = Trans.decl_l (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        begin match k, t.t_node with
        | (Paxiom as k), Tbinop (Tand, f1, f2) ->
            if is_target pr target then
            let pr1 = create_prsymbol (id_clone pr.pr_name) in
            let pr2 = create_prsymbol (id_clone pr.pr_name) in
            clues := Some (Destruct (pr.pr_name, pr1.pr_name, pr2.pr_name, Hole));
            [[create_prop_decl k pr1 f1; create_prop_decl k pr2 f2]]
            else [[d]]
        | (Pgoal as k), Tbinop (Tand, f1, f2)
        | (Paxiom as k), Tbinop (Tor, f1, f2) ->
            if is_target pr target then begin
            clues := Some (Split (pr.pr_name, Hole, Hole));
            [[create_prop_decl k pr f1]; [create_prop_decl k pr f2]] end
            else [[d]]
        | Pgoal, Tbinop (Tor, f1, f2) ->
            if is_target pr target then
            let prh = create_prsymbol (id_clone pr.pr_name) in
            let g = pr.pr_name and h1 = prh.pr_name in
            let htemp = id_register (gen_ident "htemp") in
            clues := Some (Destruct (g, htemp, g,
                           Cut (h1, f1,
                                Swap_neg (h1, Weakening (htemp, Hole)),
                                Axiom (h1, htemp))));
            [[create_prop_decl Paxiom prh (t_not f1); create_prop_decl Pgoal pr f2]]
            else [[d]]
        | _ -> [[d]] end
    | _ -> [[d]]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> nt, c
  | None -> [task], Hole

let neg_decompose omni where task =
  let target = tg omni where task in
  let clues : certif option ref = ref None in
  let trans_t = Trans.decl_l (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        let g = pr.pr_name in
        begin match t.t_node with
        | Tnot nt ->
            begin match k, nt.t_node with
            | k, Tnot nnt when is_target pr target -> (* double negation *)
                clues := Some (Swap_neg (g, Swap_neg (g, Hole)));
                [[create_prop_decl k pr nnt]]
            | Paxiom, Tbinop (Tor, f1, f2) when is_target pr target -> (* destruct *)
                let pr1 = create_prsymbol (id_clone g) in
                let pr2 = create_prsymbol (id_clone g) in
                clues := Some (Swap_neg (g,
                               Destruct (g, pr1.pr_name, pr2.pr_name,
                               Swap_neg (pr1.pr_name,
                               Swap_neg (pr2.pr_name, Hole)))));
                [[create_prop_decl Paxiom pr1 (t_not f1);
                  create_prop_decl Paxiom pr2 (t_not f2)]]
            | Pgoal, Tbinop (Tand, f1, f2) when is_target pr target ->
                let pr1 = create_prsymbol (id_clone g) in
                let pr2 = create_prsymbol (id_clone g) in
                clues := Some (Swap_neg (g,
                               Destruct (g, pr1.pr_name, pr2.pr_name,
                               Swap_neg (pr2.pr_name, Hole))));
                [[create_prop_decl Paxiom pr1 f1;
                  create_prop_decl Pgoal  pr2 (t_not f2)]]
            | Paxiom, Tbinop (Tand, f1, f2) when is_target pr target -> (* split *)
                clues := Some (Swap_neg (g,
                               Split (g,
                                      Swap_neg (g, Hole),
                                      Swap_neg (g, Hole))));
                [[create_prop_decl Paxiom pr (t_not f1)];
                 [create_prop_decl Paxiom pr (t_not f2)]]
            | Pgoal, Tbinop (Tor, f1, f2) when is_target pr target ->
                clues := Some (Swap_neg (g,
                               Split (g,
                                      Swap_neg (g, Hole),
                                      Swap_neg (g, Hole))));
                [[create_prop_decl Pgoal pr (t_not f1)];
                 [create_prop_decl Pgoal pr (t_not f2)]]
            | Pgoal, Ttrue when is_target pr target -> (* ⊥ and ⊤ *)
                clues := Some (Weakening (g,
                               Cut (g, t_false,
                                    Hole,
                                    Trivial g)));
                [[create_prop_decl Pgoal pr t_false]]
            | Pgoal, Tfalse when is_target pr target ->
                clues := Some (Swap_neg (g, Trivial g));
                []
            | Paxiom, Tfalse when is_target pr target ->
                clues := Some (Weakening (g, Hole));
                [[]]
            | Paxiom, Ttrue when is_target pr target ->
                clues := Some (Swap_neg (g, Trivial g));
                []
            | k, Tbinop (Tiff, f1, f2) when is_target pr target -> (* unfold *)
                clues := Some (Swap_neg (g, Unfold (g, Swap_neg (g, Hole))));
                let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
                [[create_prop_decl k pr destr_iff]]
            | k, Tbinop (Timplies, f1, f2) when is_target pr target ->
                clues := Some (Swap_neg (g, Unfold (g, Swap_neg (g, Hole))));
                let destr_imp = t_or (t_not f1) f2 in
                [[create_prop_decl k pr destr_imp]]
            | _ -> [[d]]
            end
        | _ -> [[d]] end
    | _ -> [[d]]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> nt, c
  | None -> [task], Hole

let unfold omni where task = (* replaces A <-> B with (A -> B) /\ (B -> A) *)
                             (* and A -> B with ¬A ∨ B *)
  let target = tg omni where task in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        begin match t.t_node with
        | Tbinop (Tiff, f1, f2) when is_target pr target ->
            clues := Some (Unfold (pr.pr_name, Hole));
            let destr_iff = t_and (t_implies f1 f2) (t_implies f2 f1) in
            [create_prop_decl k pr destr_iff]
        | Tbinop (Timplies, f1, f2) when is_target pr target ->
            clues := Some (Unfold (pr.pr_name, Hole));
            let destr_imp = t_or (t_not f1) f2 in
            [create_prop_decl k pr destr_imp]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> [nt], c
  | None -> [task], Hole


(* the next 2 functions are copied from introduction.ml *)
let intro_attrs = Sattr.singleton Inlining.intro_attr

let ls_of_vs vs =
  let id = id_clone ~attrs:intro_attrs vs.vs_name in
  create_fsymbol id [] vs.vs_ty

let intro omni where task =
  (* introduces hypothesis H : A when the goal is of the form A → B or
     introduces variable x when the goal is of the form ∀ x. P x
     introduces variable x when a hypothesis is of the form ∃ x. P x *)
  let target = tg omni where task in
  let hpr = create_prsymbol (id_fresh "H") in
  let h = hpr.pr_name in
  let clues = ref None in
  let trans_t = Trans.decl (fun d -> match d.d_node with
    | Dprop (k, pr, t) ->
        begin match t.t_node, k with
        | Tbinop (Timplies, f1, f2), Pgoal ->
            if is_target pr target
            then begin
                let g = pr.pr_name in
                clues := Some (Unfold (g, Destruct (g, h, g, (Swap_neg (h, Hole)))));
                [create_prop_decl Paxiom hpr f1;
                 create_prop_decl Pgoal pr f2] end
            else [d]
        | Tquant (Tforall, f), (Pgoal as k) | Tquant (Texists, f), (Paxiom as k) ->
            if is_target pr target
            then
              let vsl, _, f_t = t_open_quant f in
              begin match vsl with
              | [vs] ->
                  let ls = ls_of_vs vs in
                  let subst = Mvs.singleton vs (fs_app ls [] vs.vs_ty) in
                  let f = t_subst subst f_t in
                  clues := Some (Intro_quant (pr.pr_name, ls.ls_name, Hole));
                  [create_param_decl ls; create_prop_decl k pr f]
              | _ -> assert false
              end
            else [d]
        | _ -> [d] end
    | _ -> [d]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | None -> [task], Hole
  | Some c -> [nt], c

let dir_smart d c g =
  let h = id_register (id_fresh "Weaken") in
  let left, right = match d with Left -> g, h | Right -> h, g in
  Destruct (g, left, right, Weakening (h, c))

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
        | (Paxiom as k), Tbinop (Tand, f, _), Left
        | (Paxiom as k), Tbinop (Tand, _, f), Right ->
            clues := true;
            [create_prop_decl k pr f]
        | _ -> [decl] end
    | _ -> [decl]) None in
  let nt = Trans.apply trans_t task in
  if !clues then [nt], dir_smart d Hole g
  else [task], Hole

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
  Trans.apply trans_t task, Cut (h.pr_name, t, Weakening (idg, Hole), Hole)

(* Instantiate with certificate *)
let inst t_inst where task =
  let g = (default_goal task where).pr_name in
  let hpr = create_prsymbol (gen_ident "H") in
  let clues = ref None in
  let trans_t = Trans.decl (fun decl -> match decl.d_node with
    | Dprop (k, pr, t) when id_equal g pr.pr_name ->
        begin match t.t_node, k with
        | Tquant (Tforall, _), Paxiom ->
            let t_subst = subst_forall t t_inst in
            clues := Some (Inst_quant (g, hpr.pr_name, t_inst, Hole));
            [decl; create_prop_decl k hpr t_subst]
        | Tquant (Texists, _), Pgoal ->
            let t_subst = subst_exist t t_inst in
            clues := Some (Inst_quant (g, hpr.pr_name, t_inst, Weakening (g, Hole)));
            [create_prop_decl k hpr t_subst]
        | _ -> [decl] end
    | _ -> [decl]) None in
  let nt = Trans.apply trans_t task in
  match !clues with
  | Some c -> [nt], c
  | None -> [task], Hole

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
                  clues := Some (path, Hole :: List.map (fun _ -> Hole) lp);
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
  | None -> [task], Hole
  | Some (path, lc) ->
      gen_task, Rewrite (h1, h, path, rev, lc)

let rewrite g rev where task =
  let h1 = default_goal task where in
  rewrite_in (not rev) g h1 task

let exfalso task =
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
         [create_prop_decl Pgoal h t_false]
     | _ -> [decl]) None in
  let g = task_goal task in
  [Trans.apply trans task],
  Cut (h.pr_name, t_false, Weakening (g.pr_name, Hole), Trivial h.pr_name)

let case t task =
  let h = create_prsymbol (gen_ident "H") in
  let trans = Trans.decl_l (fun decl -> match decl.d_node with
     | Dprop (Pgoal, _, _) ->
            [ [create_prop_decl Paxiom h t; decl];
              [create_prop_decl Paxiom h (t_not t); decl] ]
     | _ -> [[decl]]) None in
  Trans.apply trans task,
  Cut (h.pr_name, t_not t, Swap_neg (h.pr_name, Hole), Hole)


let swap where task = (* if formula <f> designed by <where> is a premise, dismiss the old
 goal and put <not f> in its place *)
  let gpr = default_goal task where in
  let t, pr_goal = task_goal_fmla task, task_goal task in
  let _, hyp = task_separate_goal task in
  if id_equal gpr.pr_name pr_goal.pr_name
  then let underlying_t = match t.t_node with Tnot t' -> t' | _ -> t in
       compose (case underlying_t) (compose assumption exfalso) task
  else
  let trans_t = Trans.fold_decl (fun d (opt_t, acc_task) -> match d.d_node with
    | Dprop (Paxiom, pr, t) when id_equal gpr.pr_name pr.pr_name ->
        Some t, acc_task
    | _ -> opt_t, add_decl acc_task d) (None, None) in
  let clues, nt = Trans.apply trans_t hyp in
  match clues with
  | Some t ->
      let not_t = match t.t_node with Tnot t' -> t' | _ -> t_not t in
      let decl = create_prop_decl Pgoal gpr not_t in
      [add_decl nt decl], Swap_neg (gpr.pr_name, Weakening (pr_goal.pr_name, Hole))
  | None -> [task], Hole

let revert ls task =
  let x = t_app_infer ls [] in
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
  Cut (gpr.pr_name, close_t,
       Weakening (idg.pr_name, Hole),
       Inst_quant (gpr.pr_name, hinst, x, Axiom (hinst, idg.pr_name)))


(* Clear transformation with a certificate : *)
(*   removes hypothesis <g> from the task *)
let clear_one g task =
  let trans = Trans.decl (fun decl -> match decl.d_node with
    | Dprop (_, pr, _) when id_equal g pr.pr_name -> []
    | _ -> [decl]) None in
  [Trans.apply trans task], Weakening (g, Hole)

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
 *   Cut (pr.pr_name,
 *        t_exists (t_close_quant [vs] [] eq),
 *        Inst_quant (pr.pr_name, h1, t, eq_cert),
 *        Intro_quant (pr.pr_name, vs.vs_name, Hole)) *)


(** Derived transformations with a certificate *)

let trivial = try_close [assumption; close; contradict]

let intros = repeat (intro false None)

let split_logic omni where = compose (unfold omni where)
                               (compose (split_or_and omni where)
                                  (destruct omni where))

let rec blast task =
  repeat (ite (compose (compose (compose
                 trivial
                 (neg_decompose true None))
                 (unfold true None))
                 (destruct_all true None))
            blast
            id_ctrans)
    task

let clear l = compose_list (List.map (fun pr -> clear_one pr.pr_name) l)
