open Why3

open Term
open Decl
open Generic_arg_trans_utils

open Cert_certificates
open Cert_trans_utils

(* Rewrite with a certificate: if f1 is unifiable to t with substitution s then
   return s.f2 and replace every occurrences of s.f1 with s.f2 in the rest of
   the term else call recursively on subterms of t. If a substitution s is found
   then new premises are computed as e -> s.e *)
let replace_subst lp lv llet f1 f2 withed_terms t =
  (* is_replaced is common to the whole execution of replace_subst. Once an
     occurence is found, it changes to Some (s) so that only one instanciation
     is rewritten during execution *)
  let rec replace is_replaced f1 f2 t : _ * Term.term =
    match is_replaced with
    | Some(subst_ty,subst) ->
        is_replaced, t_replace (t_ty_subst subst_ty subst f1)
                       (t_ty_subst subst_ty subst f2) t
    | None ->
        begin
          (* Generate the list of variables that are here from let bindings *)
          let llet_svs =
            List.fold_left (fun acc (v, _) -> Svs.add v acc)
              Svs.empty llet
          in
          (* Catch any error from first_order_matching or with_terms. *)
          match Apply.matching_with_terms ~trans_name:"rewrite"
                  lv llet_svs f1 t (Some withed_terms) with
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
      let new_goals = Apply.generate_new_subgoals ~subst ~subst_ty llet lp in
      subst, new_goals, t

(* rewrites <h> in <i> with direction <rev> *)
let rewrite_in rev with_terms prh pri task =
  let nprh = pr_clone prh in
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    Trans.fold_decl (fun d acc ->
        match d.d_node with
        | Dprop (Paxiom, pr, trew) when pr_equal pr prh ->
            let lp, lv, llet, f = Apply.intros trew in
            let revert, t1, t2 =
              match f.t_node with
              | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
                  (* Support to rewrite from the right *)
                  if rev
                  then idc, t1, t2
                  else eqsym nprh, t2, t1
              | Tbinop (Tiff, t1, t2) ->
                  (* Support to rewrite from the right *)
                  if rev
                  then idc, t1, t2
                  else iffsym_hyp nprh, t2, t1
              | _ -> raise (Arg_bad_hypothesis ("rewrite", f)) in
            Some (lp, lv, llet, revert, t1, t2, trew)
        | _ -> acc)
      None
  in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Args_wrapper.Arg_error "Did not find rewrite hypothesis")
    | Some (lp, lv, llet, revert, t1, t2, trew) ->
        Trans.fold_decl (fun d acc ->
            match d.d_node with
            | Dprop (p, pr, t) when pr_equal pr pri ->
                let subst, lp, new_term =
                  replace_subst lp lv llet t1 t2 with_terms t in
                let new_prop = create_prop_decl p pr new_term in
                Some (subst, trew, revert, lp, lv, new_prop)
            | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten hypothesis
     to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (subst, trew, revert, lp, lv, new_decl) ->
        let trans_rewriting =
          Trans.decl (fun decl ->
              match decl.d_node with
              | Dprop (_, pr, _) when pr_equal pr pri -> [new_decl]
              | _ -> [decl]) None in
        let list_par =
          List.map (fun t ->
              Trans.decl (fun decl ->
                  match decl.d_node with
                  | Dprop (Pgoal, pr, _) ->
                      [create_goal ~expl:"rewrite premises" pr t]
                  | _ -> [decl])
                None) lp in
        let pr = Task.task_goal task in
        let n = List.length lp + 1 in
        let cert =
          lambdan n (fun l ->
              let rec app_inst trew lid lv = match trew.t_node, lid with
                | Tbinop (Timplies, _, trew), id::lid ->
                    unfold nprh ++ split nprh +++
                      [clear pr ++ swap nprh ++ rename nprh pr ++ return id;
                       app_inst trew lid lv]
                | Tquant (Tforall, fq), _ ->
                    let vsl, _, trew = t_open_quant fq in
                    let rec inst lv vsl = match lv, vsl with
                      | _, [] -> app_inst trew lid lv
                      | v::lv, _::vsl ->
                          let c = inst lv vsl in
                          let tv = Mvs.find v subst in
                          instquant nprh nprh tv ++ c
                      | _ -> assert false in
                    inst lv vsl
                | _ -> idc in
              let id, lid = match l with
                | [] -> assert false
                | h::t -> h, t in
              let rew_cert = rewrite nprh pri ++ clear nprh ++ return id in
              let rcert = duplicate prh nprh ++
                            app_inst trew lid lv ++ revert ++ rew_cert in
              apply rcert) in

        Trans.store (fun task ->
            Trans.apply (Trans.par (trans_rewriting :: list_par)) task,
            cert)
  in
  (* Composing previous functions *)
  Trans.apply (Trans.bind (Trans.bind found_eq lp_new) recreate_tasks) task

let rewrite g rev with_terms where : ctrans =
  Trans.store (fun task ->
      let h1 = default_goal task where in
      let wt = match with_terms with Some wt -> wt | None -> [] in
      rewrite_in (not rev) wt g h1 task)
