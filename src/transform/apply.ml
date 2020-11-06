(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper
open Reduction_engine
open Generic_arg_trans_utils

(** This file contains transformations with arguments that acts on specific
    declarations to refine them (rewrite, replace, apply, unfold...) *)


let debug_matching = Debug.register_info_flag "print_match"
  ~desc:"Print@ terms@ that@ were@ not@ successfully@ matched@ by@ ITP@ tactic@ apply."

(* One only need to change the following parameter values to change the
   explanation given to *new* goals introduced by transformation of this file.
*)

(* Subgoals generated by using [apply] *)
let apply_subgoals = "apply premises"

(* Subgoals generated by using [rewrite] *)
let rewrite_subgoals = "rewrite premises"

(* Equality hypothesis generated by using [replace] *)
let replace_hypothesis = "equality hypothesis"

(* Printing substitution *)
let print_subst fmt (mvs: Term.term Mvs.t) =
  Format.fprintf fmt "Print subst@.";
  Mvs.iter (fun k e -> Format.fprintf fmt "key = %a, term = %a@."
               Pretty.print_vs k Pretty.print_term e) mvs

(* Do as intros: introduce all premises of hypothesis pr and return a triple
   (goal, list_premises, binded variables) *)
let intros f =
  let rec intros_aux lp lv llet f =
    match f.t_node with
    | Tbinop (Timplies, f1, f2) ->
        intros_aux (f1 :: lp) lv llet f2
    | Tquant (Tforall, fq) ->
        let vsl, _, fs = t_open_quant fq in
        intros_aux lp (lv @ vsl) llet fs
    | Tlet (t, tb) ->
        let vs, t2 = t_open_bound tb in
        intros_aux lp lv ((vs, t) :: llet) t2
    | _ -> (lp, lv, llet, f) in
  intros_aux [] [] [] f

let term_decl d =
  match d.td_node with
  | Decl ({d_node = Dprop (_pk, _pr, t)}) -> t
  | _ -> raise (Arg_trans "term_decl")

(* [with_terms subst_ty subst lv wt]: Takes the list of variables in lv that are
   not part of the substitution and try to match them with the list of values
   from wt (ordered). *)
(* TODO we could use something simpler than first_order_matching here. *)
let with_terms ~trans_name subst_ty subst lv withed_terms =
  Debug.dprintf debug_matching "Calling with_terms@.";
  (* Get the list of variables of lv that are not in subst. *)
  let lv, slv =
    List.fold_left
      (fun (acc, accs) v ->
         match (Mvs.find v subst) with
         | _ -> acc, accs
         | exception Not_found -> t_var v :: acc, Svs.add v accs)
      ([], Svs.empty)
      lv
  in
  let lv = List.rev lv in

  (* Length checking for nice errors *)
  let diff = Svs.cardinal slv - List.length withed_terms in
  match diff with
  | _ when diff < 0 ->
      Debug.dprintf debug_matching "Too many withed terms@.";
      let msg = ": Not the right number of missing arguments. Expected arguments for:" in
      raise (Arg_trans_missing (trans_name ^ msg, slv))
  | _ when diff > 0 ->
      Debug.dprintf debug_matching "Not enough withed terms@.";
      let msg =
        if withed_terms = [] then
          ": Unable to infer arguments (try using \"with\") for:"
        else
          ": Not the right number of missing arguments. Expected arguments for:" in
      raise (Arg_trans_missing (trans_name ^ msg, slv))
  | _ (* when diff = 0 *) ->
      let new_subst_ty, new_subst =
        (* TODO Here we match on a list of variable against a list of terms. It
           is probably possible to use a simplified version. But don't forget
           to unify type variables. (Same comment as at top of this function) *)
        try first_order_matching slv lv withed_terms with
        | Reduction_engine.NoMatch (Some (t1, t2, None)) ->
            Debug.dprintf debug_matching
              "Term %a and %a can not be matched. Failure in matching@."
                Pretty.print_term t1 Pretty.print_term t2;
            raise (Arg_trans_term2 (trans_name^":matching", t1, t2))
        | Reduction_engine.NoMatch (Some (t1, t2, Some t3)) ->
            Debug.dprintf debug_matching
              "Term %a and %a can not be matched. %a already matched with %a@."
                Pretty.print_term t1 Pretty.print_term t2 Pretty.print_term t1
                Pretty.print_term t3;
            raise (Arg_trans_term3 (trans_name^":matching", t1, t2, t3))
        | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
            Debug.dprintf debug_matching
              "Term %a and %a can not be matched. Failure in matching@."
              Pretty.print_pat p1 Pretty.print_pat p2;
            raise (Arg_trans_pattern (trans_name, p1, p2))
        | Reduction_engine.NoMatch None ->
            Debug.dprintf debug_matching "with_terms: No match@.";
            raise (Arg_trans trans_name)
      in
      let subst_ty = Ty.Mtv.union
          (fun _x y z ->
            if Ty.ty_equal y z then
              Some y
            else
              raise (Arg_trans_type (trans_name ^ ": ", y, z)))
          subst_ty new_subst_ty
      in
      let subst =
        Mvs.union (fun _x y z ->
          if Term.t_equal y z then
            Some y
          else
            raise (Arg_trans_term2 (trans_name ^ ": ", y, z)))
          subst new_subst
      in
      subst_ty, subst

(* This function first try to match left_term and right_term with a substitution
   on lv/slv. It then tries to fill the holes with the list of withed_terms.
   trans_name is used for nice error messages. Errors are returned when the size
   of withed_terms is incorrect.
*)
let matching_with_terms ~trans_name lv llet_vs left_term right_term withed_terms =
  let slv = List.fold_left (fun acc v -> Svs.add v acc) llet_vs lv in
  let (subst_ty, subst) =
    try first_order_matching slv [left_term] [right_term] with
    | Reduction_engine.NoMatch (Some (t1, t2, None)) ->
      Debug.dprintf debug_matching
        "Term %a and %a can not be matched. Failure in matching@."
        Pretty.print_term t1 Pretty.print_term t2;
      raise (Arg_trans_term2 (trans_name^":no_match", t1, t2))
    | Reduction_engine.NoMatch (Some (t1, t2, Some t3)) ->
      Debug.dprintf debug_matching
        "Term %a and %a can not be matched. %a already matched with %a@."
        Pretty.print_term t1 Pretty.print_term t2 Pretty.print_term t1
        Pretty.print_term t3;
      raise (Arg_trans_term3 (trans_name^":no_match", t1, t2, t3))
    | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
      Debug.dprintf debug_matching
        "Term %a and %a can not be matched. Failure in matching@."
        Pretty.print_pat p1 Pretty.print_pat p2;
      raise (Arg_trans_pattern (trans_name, p1, p2))
    | Reduction_engine.NoMatch None -> raise (Arg_trans trans_name)
  in
  Debug.dprintf debug_matching
    "subst after first first_order_matching:\n%a@." print_subst subst;
  let subst_ty, subst =
    let withed_terms = Opt.get_def [] withed_terms in
    with_terms ~trans_name subst_ty subst lv withed_terms
  in
  subst_ty, subst

let generate_new_subgoals ~subst_ty ~subst llet lp =
  (* Here the substitution is updated in order for the let values to not contain
     any let-introduced-variables. *)
  let subst_ty, subst, new_lets, new_goals =
    List.fold_left (fun (subst_ty, subst, new_lets, new_goals) (v,t) ->
        match Mvs.find v subst with
        | t' ->
            (* [v -> t'] appears in subst. So we want to create two new goals:
               G1: t = t'
               G2: h
            *)
            let t' = t_ty_subst subst_ty subst t' in
            let t = t_ty_subst subst_ty subst t in
            (subst_ty, subst, new_lets, (t_equ t' t) :: new_goals)
        | exception Not_found ->
            let t = t_ty_subst subst_ty subst t in
            (subst_ty, Mvs.add v t subst, (v,t) :: new_lets, new_goals)
      )
      (subst_ty, subst, [], []) llet
  in
  let add_lets_subst new_goals h =
    let h = t_ty_subst subst_ty subst h in
    let freevars = t_freevars Mvs.empty h in
    let h =
      (* All the remaining freevars are originally let-binded. We rebind them
         with a correct let. *)
      List.fold_left (fun h (v, t) ->
          if Mvs.mem v freevars then
            let t = t_ty_subst subst_ty subst t in
            (* Small optimization with t_let_simp instead of t_let *)
            t_let_simp t (t_close_bound v h)
          else
            h)
        h (List.rev new_lets)
    in
    h :: new_goals
  in
  List.fold_left add_lets_subst [] (new_goals @ lp)

(* Apply:
   1) takes the hypothesis and introduce parts of it to keep only the last
      element of the implication. It gathers the premises and variables in a
      list.
   2) try to find a good substitution for the list of variables so that last
      element of implication is equal to the goal.
   3) generate new goals corresponding to premises with variables instantiated
      with values found in 2).
 *)
let apply pr withed_terms : Task.task Trans.tlist = Trans.store (fun task ->
  let kn = task_known task in
  let g, task = Task.task_separate_goal task in
  let g = term_decl g in
  let t =
    match find_prop_decl kn pr with
    | (_, t) -> t
    | exception Not_found -> raise (Arg_pr_not_found pr)
  in
  let (lp, lv, llet, nt) = intros t in
  let llet_vs = List.fold_left (fun acc (vs, _) -> Svs.add vs acc) Svs.empty llet in
  match matching_with_terms ~trans_name:"apply" lv llet_vs nt g withed_terms with
  | exception e -> raise e
  | subst_ty, subst ->
      Debug.dprintf debug_matching "subst after matching with terms:\n%a@."
        print_subst subst;
      let inst_nt = t_ty_subst subst_ty subst nt in
      (* Safety guard: we check that the goal was indeed the instantiated
         hypothesis *)
      if (Term.t_equal inst_nt g) then
        let new_goals = generate_new_subgoals ~subst ~subst_ty llet lp in
        Debug.dprintf debug_matching "Printing new_goals to introduce:\n%a@."
          (Pp.print_list Pp.newline Pretty.print_term) new_goals;
        let create_goal h =
          let pr = create_prsymbol (gen_ident ?loc:g.t_loc "G") in
          Task.add_decl task (create_goal ~expl:apply_subgoals pr h)
        in
        List.map create_goal new_goals
      else
        (* This should never happen *)
        assert false
  )

let replace rev f1 f2 t =
  match rev with
  | true -> t_replace f1 f2 t
  | false -> t_replace f2 f1 t

(* - If f1 is unifiable to t with substitution s then return s.f2 and replace every
     occurrences of s.f1 with s.f2 in the rest of the term
   - Else call recursively on subterms of t *)
(* If a substitution s is found then new premises are computed as e -> s.e *)
let replace_subst lp lv llet f1 f2 withed_terms t =
  (* is_replaced is common to the whole execution of replace_subst. Once an
     occurence is found, it changes to Some (s) so that only one instanciation
     is rewritten during execution *)
  let rec replace is_replaced f1 f2 t : _ * Term.term =
    match is_replaced with
    | Some(subst_ty,subst) ->
        is_replaced, t_replace (t_ty_subst subst_ty subst f1) (t_ty_subst subst_ty subst f2) t
    | None ->
      begin
        (* Generate the list of variables that are here from let bindings *)
        let llet_svs =
          List.fold_left (fun acc (v, _) -> Svs.add v acc)
            Svs.empty llet
        in
        (* Catch any error from first_order_matching or with_terms. *)
        match matching_with_terms ~trans_name:"rewrite" lv llet_svs f1 t (Some withed_terms) with
        | exception _e ->
            Term.t_map_fold
                (fun is_replaced t -> replace is_replaced f1 f2 t)
                is_replaced t
        | subst_ty, subst ->
              let sf1 = t_ty_subst subst_ty subst f1 in
              if (Term.t_equal sf1 t) then
                Some (subst_ty, subst), t_ty_subst subst_ty subst f2
              else
                t_map_fold (fun is_replaced t -> replace is_replaced f1 f2 t)
                  is_replaced t
      end
  in
  let is_replaced, t =
    replace None f1 f2 t
  in
  match is_replaced with
  | None -> raise (Arg_trans "rewrite: no term matching the given pattern")
  | Some(subst_ty,subst) ->
      let new_goals = generate_new_subgoals ~subst ~subst_ty llet lp in
      (new_goals, t)

let rewrite_in rev with_terms h h1 =
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
          let lp, lv, llet, f = intros t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, lv, llet, t1, t2)
      | _ -> acc)
      None
  in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Arg_error "rewrite") (* Should not happen *)
    | Some (lp, lv, llet, t1, t2) ->
      Trans.fold_decl (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          let lp, new_term = replace_subst lp lv llet t1 t2 with_terms t in
            Some (lp, create_prop_decl p pr new_term)
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_term) ->
      let trans_rewriting =
        Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          [new_term]
        | _ -> [d]) None in
      let list_par =
        List.map
          (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (p, pr, _t)
              when (Ident.id_equal pr.pr_name h1.pr_name &&
                    p = Paxiom) ->
                [d]
            | Dprop (Pgoal, _, _) ->
                [create_goal ~expl:rewrite_subgoals (Decl.create_prsymbol (gen_ident "G")) e]
            | _ -> [d] )
          None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  Trans.bind (Trans.bind found_eq lp_new) recreate_tasks

let rewrite_list opt rev hl h1 =
  let found_decl =
    fold_decl (fun d (ok,acc) ->
        if ok then (ok,acc)
        else
          match d.d_node with
          | Dprop (p, pr, t)
               when (Ident.id_equal pr.pr_name h1.pr_name &&
                     (p = Paxiom || p = Pgoal)) ->
             (true,Some (p,pr,t))
          | _ -> (ok, acc)) (false, None) in
  let found_term = Trans.bind found_decl
                     (fun (_, od) -> Trans.store (fun _ ->
                        match od with
                        | Some (_,_,t) -> ([],t)
                        | None -> raise (Arg_error "rewrite"))) in
  let do_h h (lp, term) =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    fold_decl (fun d ((acclp,accterm) as acc) ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
          let lp, lv, llet, f = intros t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          let new_lp, new_term =
            if opt
            then try replace_subst lp lv llet t1 t2 [] accterm
                 with Arg_trans _ -> acc
            else
              replace_subst lp lv llet t1 t2 [] accterm in
       new_lp@acclp, new_term
      | _ -> acc) (lp, term) in
  let do_all = List.fold_left (fun acc h -> Trans.bind acc (do_h h)) found_term hl in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks (lp, term) =
    let trans_rewriting =
      Trans.decl (fun d -> match d.d_node with
      | Dprop (p, pr, _t)
         when (Ident.id_equal pr.pr_name h1.pr_name &&
               (p = Paxiom || p = Pgoal)) ->
         [create_prop_decl p pr term]
      | _ -> [d]) None in
    let list_par =
      List.map
        (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (p, pr, _t)
              when (Ident.id_equal pr.pr_name h1.pr_name &&
                    p = Paxiom) ->
                [d]
            | Dprop (Pgoal, _, _) ->
                [create_goal ~expl:rewrite_subgoals (Decl.create_prsymbol (gen_ident "G")) e]
            | _ -> [d] )
          None) lp in
    Trans.par (trans_rewriting :: list_par) in
  Trans.bind do_all recreate_tasks

let find_target_prop h : prsymbol trans =
  Trans.store (fun task ->
               match h with
                 | Some pr -> pr
                 | None -> Task.task_goal task)

let rewrite with_terms rev h h1 =
  let with_terms =
    match with_terms with
    | None -> []
    | Some l -> l
  in
  Trans.bind (find_target_prop h1) (rewrite_in (not rev) with_terms h)

let rewrite_list rev opt hl h1 =
  Trans.bind (find_target_prop h1) (rewrite_list opt (not rev) hl)

let detect_prop_list pr k hl =
  match hl with
  | None -> k = Pgoal
  | Some [] -> (* Should not be able to parse the empty list *)
      raise (Arg_trans "replace")
  | Some hl ->
      ((List.exists (fun h -> Ident.id_equal pr.pr_name h.pr_name) hl)
         && (k = Paxiom || k = Pgoal))

(* Replace occurences of t1 with t2 in h. When h is None, the default is to
   replace in the goal.
*)
let replace t1 t2 hl =
  if not (Ty.ty_equal (t_type t1) (t_type t2)) then
    raise (Arg_trans_term2 ("replace", t1, t2))
  else
    (* Create a new goal for equality of the two terms *)
    let pr_goal = create_prsymbol (gen_ident "G") in
    let eq_goal_term = t_app_infer ps_equ [t1; t2] in
    let ng = create_goal ~expl:replace_hypothesis pr_goal eq_goal_term in
    let ng = Trans.goal (fun _ _ -> [ng]) in
    let g = Trans.decl (fun d ->
      match d.d_node with
      | Dprop (p, pr, t) when detect_prop_list pr p hl ->
          [create_prop_decl p pr (replace true t1 t2 t)]
      | _ -> [d]) None in
    Trans.par [g; ng]

let replace tl hl =
  match tl with
  | t1 :: t2 :: [] -> replace t1 t2 hl
  | _ ->
      (* Should not happen, an error should be raised in args_wrapper *)
      assert false

let t_replace_app unf ls_defn t =
  let (vl, tls) = ls_defn in
  match t.t_node with
  | Tapp (ls, tl) when ls_equal unf ls ->
     let add (mt,mv) x y =
       Ty.ty_match mt x.vs_ty (t_type y), Mvs.add x y mv
     in
     let mtv,mvs =
       List.fold_left2 add (Ty.Mtv.empty,Mvs.empty) vl tl
     in
     let mtv = Ty.oty_match mtv tls.t_ty t.t_ty in
     t_ty_subst mtv mvs tls
  | _ -> t

let rec t_ls_replace ls ls_defn t =
  t_replace_app ls ls_defn (t_map (t_ls_replace ls ls_defn) t)

let unfold unf hl =
  let r = ref None in
  Trans.decl
    (fun d ->
      match d.d_node with
        (* Do not work on mutually recursive functions *)
      | Dlogic [(ls, ls_defn)] when ls_equal ls unf ->
          r := Some (open_ls_defn ls_defn);
          [d]
      | Dprop (k, pr, t) when detect_prop_list pr k hl ->
        begin
          match !r with
          | None -> [d]
          | Some ls_defn ->
              let t = t_ls_replace unf ls_defn t in
              let new_decl = create_prop_decl k pr t in
              [new_decl]
        end
      | _ -> [d]) None


let () = wrap_and_register ~desc:"Sort@ declarations." "sort" Ttrans sort

let () = wrap_and_register
          ~desc:"unfold <ls> [in] <name list>@ \
            unfolds@ logical@ symbol@ <ls> in@ the@ given@ \
            list@ of@ premises.@ If@ no@ list@ is@ given,@ \
            unfold@ in@ the@ goal."
          "unfold"
          (Tlsymbol (Topt ("in", Tprlist Ttrans)))
          unfold

let () = wrap_and_register
          ~desc:"replace <term1> <term2> [in] <name list>@ \
            replaces@ occcurences@ of@ <term1>@ by@ <term2>@ in@ \
            the@ given@ list@ of@ premises.@ If@ no@ list@ is@ given,@ \
            replace@ in@ the@ goal."
          "replace"
          (Ttermlist_same (2, (Topt ("in", Tprlist Ttrans_l))))
          replace

let _ = wrap_and_register
          ~desc:"rewrite [<-] <name> [in] <name2> [with] <term list>@ \
            rewrites@ equality@ defined@ in@ <name>@ into@ <name2>@ \
            using@ exactly@ all@ terms@ in@ the@ list@ as@ instances@ \
            for@ what@ cannot@ be@ deduced@ directly."
          "rewrite"
          (Toptbool ("<-",(Tprsymbol (Topt ("in",
            Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))))))
          (fun rev h h1opt term_list -> rewrite term_list rev h h1opt)

let _ = wrap_and_register
          ~desc:"rewrite_list [<-] <name list> [?] [in] <name2>@ \
            rewrites@ equalities@ defined@ in@ the@ given@ list@ \
            of@ premises@ into@ <name2>.@ If@ [?]@ is@ set,@ each@ \
            of@ the@ rewrites@ is@ optional."
          "rewrite_list"
          (Toptbool ("<-", (Tprlist (Toptbool ("?",
            Topt ("in", Tprsymbol Ttrans_l))))))
          (fun rev hl opt h1opt -> rewrite_list rev opt hl h1opt)

let () = wrap_and_register
           ~desc:"apply <prop> [with] <term list>@ \
            applies@ premise@ <prop>@ to@ the@ goal@ and@ uses@ the@ \
            list@ of@ terms@ to@ instantiate@ the@ variables@ that@ \
            are@ not@ found."
          "apply"
          (Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))
          apply
