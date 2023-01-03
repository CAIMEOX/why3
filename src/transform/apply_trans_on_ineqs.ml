(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Ty
open Theory
open Ident
open Task

(* Filter all the formulas that are not inequalities or equalities about
   int/reals *)
(* Also performs some simplifications *)
(* let rec add_fmlas symbols map f = *)
(*   let rec add = add_fmlas symbols in *)
(*   match f.t_node with *)
(*   | Tbinop (Tand, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported *)
(*     | Tautology -> *)
(*       get f2 *)
(*     | Contradiction -> Contradiction *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported *)
(*       | Tautology -> *)
(*         Formula f1 *)
(*       | Contradiction -> Contradiction *)
(*       | Formula f2 -> Formula (t_and f1 f2))) *)
(*   | Tbinop (Tor, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported -> Unsupported *)
(*     | Tautology -> Tautology *)
(*     | Contradiction -> get f2 *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported -> Unsupported *)
(*       | Tautology -> Tautology *)
(*       | Contradiction -> Formula f1 *)
(*       | Formula f2 -> Formula (t_or f1 f2))) *)
(*   | Tbinop (Timplies, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported *)
(*     | Contradiction -> *)
(*       Unsupported *)
(*     | Tautology -> get f2 *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported -> Unsupported *)
(*       | Tautology -> Tautology *)
(*       | Contradiction -> Formula (t_implies f1 t_false) *)
(*       | Formula f2 -> Formula (t_implies f1 f2))) *)
(*   | Ttrue -> Tautology *)
(*   | Tfalse -> Contradiction *)
(*   | Tnot f1 -> ( *)
(*     match get f1 with *)
(*     | Unsupported -> Unsupported *)
(*     | Tautology -> Contradiction *)
(*     | Contradiction -> Tautology *)
(*     | Formula f -> Formula (t_not f)) *)
(*   | Tapp (ls, [ t1; t2 ]) -> *)
(*     if ls_equal ls ps_equ then *)
(*       match t1.t_ty with *)
(*       | Some ty -> *)
(*         if ty_equal ty ty_int || ty_equal ty ty_real then *)
(*           Formula f *)
(*         else *)
(*           Unsupported *)
(*       | None -> Formula f *)
(*     else if List.exists (fun _ls -> ls_equal ls _ls) symbols then *)
(*       Formula f *)
(*     else *)
(*       Unsupported *)
(*   | _ -> Unsupported *)

let add_ineq ineqs t ineq =
  let t_ineqs = Mterm.find t ineqs in
  match t_ineqs with
  | [] -> Mterm.add t [ ineq ] ineqs
  | _ -> Mterm.add t (ineq :: t_ineqs) ineqs

(* Deduce new inequalities from "add_ieee_post t1 t2 t" *)
let apply_add mls ineqs t t1 t2 =
  let le_ls = assert false (* TODO : Find real symbol *) in
  let add_ls = assert false (* TODO : Find real symbol *) in
  let sub_ls = assert false (* TODO : Find real symbol *) in
  let mult_ls = assert false (* TODO : Find real symbol *) in
  let abs_ls = assert false (* TODO : Find real symbol *) in
  let eps = assert false (* TODO : Create term from constant *) in
  let add = t_app add_ls [ t1; t2 ] (Some ty_real) in
  let sub = t_app sub_ls [ t; add ] (Some ty_real) in
  let abs = t_app abs_ls [ sub ] (Some ty_real) in
  let err = t_app mult_ls [ add; eps ] (Some ty_real) in
  let ineq = t_app le_ls [ abs; err ] (Some ty_bool) in
  let ineqs = add_ineq ineqs t ineq in
  let abs x = t_app abs_ls [ x ] (Some ty_real) in
  let add x y = t_app add_ls [ x; y ] (Some ty_real) in
  let sub x y = t_app sub_ls [ x; y ] (Some ty_real) in
  let mult x y = t_app mult_ls [ x; y ] (Some ty_real) in
  let le x y = t_app le_ls [ x; y ] (Some ty_bool) in
  let t1_ineqs = Mterm.find t1 ineqs in
  let t2_ineqs = Mterm.find t2 ineqs in
  let combine_ineqs (t1, t2) (t1', t2') =
    match t1.t_node with
    | Tapp (abs_ls, [ x ]) -> (
      match x.t_node with
      | Tapp (sub_ls, [ a; b ]) -> assert false
      | _ -> (
        match t2.t_node with
        | Tapp (abs_ls, [ x ]) -> (
          match x.t_node with
          | Tapp (sub_ls, [ a; b ]) -> assert false
          | _ -> le (abs t) (add (add t2 t2') (mult (add t2 t2') eps)))
        | _ -> assert false))
    | _ -> assert false
  in
  List.fold_left
    (fun ineqs t1_ineq ->
      match t1_ineq.t_node with
      | Tapp (ls, [ _t1; _t2 ]) when ls = le_ls ->
        let combine_ineqs = combine_ineqs (_t1, _t2) in
        List.fold_left
          (fun ineqs t2_ineq ->
            match t2_ineq.t_node with
            | Tapp (ls, [ _t1; _t2 ]) when ls = le_ls ->
              let new_ineq = combine_ineqs (_t1, _t2) in
              add_ineq ineqs t new_ineq
            | _ -> ineqs)
            (* For now we don't deduce anything here, maybe we should ? *)
          ineqs t2_ineqs
      | _ -> ineqs)
    ineqs t1_ineqs

(* let rec combine_ineqs ineq ineq_list = *)
(*   match ineqs with *)
(*   | [] ->  *)
(* match Mterm.find t1 ineqs with *)
(* | [] -> ( *)
(*   match Mterm.find t2 ineqs with *)
(*   | [] -> ineqs *)
(*   | ineq :: tl -> assert false) *)
(* | ineq :: tl -> ( *)
(*   match ineq.t_node with *)
(*   | Tapp (ls, [ _t1; _t2 ]) -> ( *)
(*     match Mls.find ls mls with *)
(*     | "le" -> assert false *)
(*     | _ -> *)
(*       assert false *)
(* (* TODO: Match ls with le, then match _t1 with Tapp(absls, [ Tapp *) (*
   (minusls, [_, t3]) ]) and we take t3. Do the same for t2, then we use *) (*
   the addition lemma with (t - (t3 + t4) <= ...) *)) *)
(* | _ -> assert false) *)

(* TODO: Avoid traversing the same term twice *)
(* ineqs is a map from real terms to inequalities that hold for these terms *)
(* ieee_posts is a map from float terms to an ieee_post condition *)
let rec apply mls t ieee_posts ineqs =
  let apply = apply mls in
  match Mterm.find t ieee_posts with
  | [] -> ineqs
  | [ ieee_post ] -> (
    match ieee_post with
    | Tapp (ls, [ t1; t2 ]) -> (
      let ineqs = apply t1 ieee_posts ineqs in
      let ineqs = apply t2 ieee_posts ineqs in
      match Mls.find ls mls with
      | "add_ieee_post" -> apply_add mls ineqs t t1 t2
      | _ -> failwith "Unsupported yet")
    | _ -> assert false)
  (* Only 0 or 1 ieee_post possible *)
  | _ -> assert false

let add_new_impl _ _ _ = assert false

let get_truths_and_impls d (truths, impls) =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma -> (
    let truths = Mterm.add f (pr, kind) truths in
    match f.t_node with
    | Tbinop (Timplies, f1, _) -> (truths, add_new_impl impls f1 f)
    | _ -> (truths, impls))
  | _ -> (truths, impls)

let filter_non_arith truths acc t = assert false

let rec task_fold_left fn = function
  | Some task ->
    let prev = task_fold_left fn task.task_prev in
    fn prev task.task_decl
  | None -> None

let remove_unused_decls truths task =
  let filter_non_arith = filter_non_arith truths in
  task_fold_left filter_non_arith task

let check_truth = assert false

let remove_unused_decls (truths, impls) =
  let truths, _ =
    Mterm.fold_left (fun arg t _ -> check_truth arg t) (truths, impls) truths
  in
  Trans.store (remove_unused_decls truths)

let apply_trans_on_ineqs env =
  let symbol_names =
    [
      Ident.op_infix "<";
      Ident.op_infix "<=";
      Ident.op_infix ">";
      Ident.op_infix ">=";
      Ident.op_infix "+";
      Ident.op_infix "-";
      Ident.op_infix "*";
      Ident.op_infix "/";
    ]
  in
  let real = Env.read_theory env [ "real" ] "Real" in
  let symbols =
    List.map (fun name -> ns_find_ls real.th_export [ name ]) symbol_names
  in
  (* let add_fmlas = add_fmlas symbols in *)
  let arith_symbols = [] in

  Trans.bind
    (Trans.fold_decl get_truths_and_impls (Mterm.empty, Mterm.empty))
    remove_unused_decls
(* Trans.bind Trans.identity *)
(*   (fun task -> *)
(*     let goal = Task.task_goal_fmla task in *)
(*     match goal.t_node with *)
(*     | Tapp (ls, [ t1; t2 ]) -> *)
(*       if List.exists (fun _ls -> ls_equal ls _ls) symbols then *)
(*         let terms_ineqs = *)
(*           Trans.fold_decl *)
(*             (fun d acc -> *)
(*               match d.d_node with *)
(*               | Dparam { ls_args = []; ls_value = Some ty } *)
(*                 when ty_equal ty ty_int || ty_equal ty ty_real -> *)
(*                 assert false (* Mterm.add ? *) *)
(*               | Dprop (Paxiom, pr, f) -> add_fmlas acc f *)
(*               | _ -> acc) *)
(*             Mterm.empty *)
(*         in *)
(*         let rec get_terms t = *)
(*           match t.t_node with *)
(*           | Tvar v -> [ t ] *)
(*           | Tconst c -> [] *)
(*           | Tapp (ls, [ t1; t2 ]) -> *)
(*             if List.exists (fun _ls -> ls_equal ls _ls) arith_symbols then *)
(*               get_terms t1 @ get_terms t2 *)
(*             else *)
(*               [ t ] *)
(*           | _ -> assert false *)
(*         in *)
(*         let goal_terms = get_terms t1 @ get_terms t2 in *)
(*         assert false *)
(*       else *)
(*         failwith "Unsupported goal" *)
(*     | _ -> failwith "Unsupported goal") *)
(*   Trans.compose *)
(*   (Trans.lookup_transform "abstract_unknown_lsymbols" env) *)
(*   (Trans.decl (filter_non_arith (int_symbols @ real_symbols)) None) *)

let () =
  Trans.register_env_transform "apply_trans_on_ineqs" apply_trans_on_ineqs
    ~desc:
      "Try to apply transitivity of inequalities without losing information."
