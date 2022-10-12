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

(* Filter all the formulas that are not inequalities or equalities about
   int/reals *)
(* Also performs some simplifications *)
let rec add_fmlas symbols map f =
  let rec add = add_fmlas symbols in
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> (
    match get f1 with
    | Unsupported
    | Tautology ->
      get f2
    | Contradiction -> Contradiction
    | Formula f1 -> (
      match get f2 with
      | Unsupported
      | Tautology ->
        Formula f1
      | Contradiction -> Contradiction
      | Formula f2 -> Formula (t_and f1 f2)))
  | Tbinop (Tor, f1, f2) -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Tautology
    | Contradiction -> get f2
    | Formula f1 -> (
      match get f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula f1
      | Formula f2 -> Formula (t_or f1 f2)))
  | Tbinop (Timplies, f1, f2) -> (
    match get f1 with
    | Unsupported
    | Contradiction ->
      Unsupported
    | Tautology -> get f2
    | Formula f1 -> (
      match get f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula (t_implies f1 t_false)
      | Formula f2 -> Formula (t_implies f1 f2)))
  | Ttrue -> Tautology
  | Tfalse -> Contradiction
  | Tnot f1 -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Contradiction
    | Contradiction -> Tautology
    | Formula f -> Formula (t_not f))
  | Tapp (ls, [ t1; t2 ]) ->
    if ls_equal ls ps_equ then
      match t1.t_ty with
      | Some ty ->
        if ty_equal ty ty_int || ty_equal ty ty_real then
          Formula f
        else
          Unsupported
      | None -> Formula f
    else if List.exists (fun _ls -> ls_equal ls _ls) symbols then
      Formula f
    else
      Unsupported
  | _ -> Unsupported


let apply_trans_on_ineqs env =
  let symbol_names =
    [
      Ident.op_infix "<";
      Ident.op_infix "<=";
      Ident.op_infix ">";
      Ident.op_infix ">=";
    ]
  in
  let int = Env.read_theory env [ "int" ] "Int" in
  let int_symbols =
    List.map (fun name -> ns_find_ls int.th_export [ name ]) symbol_names
  in
  let real = Env.read_theory env [ "real" ] "Real" in
  let real_symbols =
    List.map (fun name -> ns_find_ls real.th_export [ name ]) symbol_names
  in
  let symbols = int_symbols @ real_symbols in
  let add_fmlas = add_fmlas symbols in
  let arith_symbols = [] in
  Trans.bind Trans.identity (fun task ->
    let goal = Task.task_goal_fmla task in
    match goal.t_node with
      | Tapp (ls, [ t1; t2 ]) ->
        if List.exists (fun _ls -> ls_equal ls _ls) symbols then
          let terms_ineqs = Trans.fold_decl (fun d acc ->
            match d.d_node with
            | Dparam { ls_args = []; ls_value = Some ty }
              when ty_equal ty ty_int || ty_equal ty ty_real -> assert false (* Mterm.add ? *)
            | Dprop (Paxiom, pr, f) ->
              add_fmlas acc f
            | _ -> acc
            ) Mterm.empty in
          let rec get_terms t = (match t.t_node with
          | Tvar v -> [ t ]
          | Tconst c -> [ ]
          | Tapp (ls, [ t1; t2 ]) ->
              if List.exists (fun _ls -> ls_equal ls _ls) arith_symbols then get_terms t1 @ get_terms t2 else [ t ]
          | _ -> assert false
          ) in
          let goal_terms = get_terms t1 @ get_terms t2 in
          assert false
        else
          failwith "Unsupported goal"
      | _ -> failwith "Unsupported goal"
    )

  (* Trans.compose (Trans.lookup_transform "abstract_unknown_lsymbols" env) (Trans.decl (filter_non_arith (int_symbols @ real_symbols)) None) *)

let () =
  Trans.register_env_transform "apply_trans_on_ineqs" apply_trans_on_ineqs
    ~desc:
      "Try to apply transitivity of inequalities without losing information."
