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

type ineq_symbol =
  | Lt
  | Gt
  | Le
  | Ge

type real_op =
  | Add
  | Sub
  | Mul
  | Div

type ieee_symbol =
  | AddPostSingle
  | SubPostSingle
  | MulPostSingle
  | DivPostSingle
  | AddPostDouble
  | SubPostDouble
  | MulPostDouble
  | DivPostDouble

type symbols = {
  real_ineqs : ineq_symbol Mls.t;
  real_ops : real_op Mls.t;
  abs : lsymbol;
  to_real : lsymbol;
  ieee : ieee_symbol Mls.t;
}

type ineq =
  | Abs of ineq_symbol * term * term
  | Absminus of ineq_symbol * term * term * term
  | Unsupported

type ieee_post = Post of ieee_symbol * term * term * term

let parse_ineq symbols ineq =
  match ineq.t_node with
  | Tapp (ls, [ t1; t2 ]) when Mls.mem ls symbols.real_ineqs -> (
    match t1.t_node with
    | Tapp (_ls, [ t ]) when ls_equal _ls symbols.abs -> (
      let ineq_symbol = Mls.find ls symbols.real_ineqs in
      match t.t_node with
      | Tvar v -> Abs (ineq_symbol, t1, t2)
      | Tapp (ls, [ _t1; _t2 ])
        when Mls.mem ls symbols.real_ops && Mls.find ls symbols.real_ops == Sub
        ->
        Absminus (ineq_symbol, _t1, _t2, t2)
      | _ -> Unsupported)
    | _ -> Unsupported)
  | _ -> assert false

let rec get_subterms symbols t =
  match t.t_node with
  | Tvar v -> [ t ]
  | Tapp (ls, [ t ]) when ls_equal ls symbols.abs -> get_subterms symbols t
  | Tapp (ls, terms) when Mls.mem ls symbols.real_ops ->
    List.fold_left (fun ts t -> ts @ get_subterms symbols t) [] terms
  | Tapp (ls, _) -> [ t ]
  | _ -> []

let add_ineq symbols ineqs ineq =
  let add ineqs ineq t =
    let t_ineqs =
      try Mterm.find t ineqs with
      | Not_found -> []
    in
    match t_ineqs with
    | [] -> Mterm.add t [ ineq ] ineqs
    | _ -> Mterm.add t (ineq :: t_ineqs) ineqs
  in
  let ineq = parse_ineq symbols ineq in
  let get_subterms = get_subterms symbols in
  let terms =
    match ineq with
    | Abs (_, t1, t2) -> get_subterms t1 @ get_subterms t2
    | Absminus (_, t1, t2, t3) ->
      get_subterms t1 @ get_subterms t2 @ get_subterms t3
    | Unsupported -> []
  in
  List.fold_left (fun ineqs t -> add ineqs ineq t) ineqs terms

let rec add_fmlas symbols f (ieee_posts, ineqs) =
  let rec add = add_fmlas symbols in
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let ieee_posts, ineqs = add f1 (ieee_posts, ineqs) in
    add f2 (ieee_posts, ineqs)
  | Tapp (ls, [ t1; t2 ]) when Mls.mem ls symbols.real_ineqs ->
    (ieee_posts, add_ineq symbols ineqs f)
  | Tapp (ls, [ t1; t2; t3 ]) when Mls.mem ls symbols.ieee ->
    ( Mterm.add t3 (Post (Mls.find ls symbols.ieee, t1, t2, t3)) ieee_posts,
      ineqs )
  | _ -> (ieee_posts, ineqs)

let get_ieee_posts_and_ineqs symbols d (ieee_posts, ineqs) =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma ->
    add_fmlas symbols f (ieee_posts, ineqs)
  | _ -> (ieee_posts, ineqs)

let use_ieee_thms symbols ineqs ieee_symbol t1 t2 t3 = assert false

(* TODO: Avoid traversing the same term twice *)
let rec apply_theorems symbols ieee_posts ineqs t =
  let apply = apply_theorems symbols in
  try
    match Mterm.find t ieee_posts with
    | Post (ieee_symbol, t1, t2, t3) ->
      let new_truths = apply ieee_posts ineqs t1 in
      let new_truths = new_truths @ apply ieee_posts ineqs t2 in
      new_truths @ use_ieee_thms symbols ineqs ieee_symbol t1 t2 t3
  with
  | Not_found -> []

let apply symbols (ieee_posts, ineqs) task =
  let goal = Task.task_goal_fmla task in
  match goal.t_node with
  (* TODO: Also destruct conjunctions ? *)
  | Tapp (ls, [ t1; t2 ]) when Mls.mem ls symbols.real_ineqs -> (
    match parse_ineq symbols goal with
    | Abs (ineq_symbol, t1, t2) ->
      let new_truths = apply_theorems symbols ieee_posts ineqs t1 in
      assert false
    | Absminus _ -> failwith "Unsupported yet"
    | Unsupported -> failwith "Unsupported inequality form")
  | _ -> failwith "Unsupported goal, it should be a real inequality"

let apply_transitivity symbols (ieee_posts, ineqs) =
  (* let new_truths = [] in *)
  (* let truths, _ = *)
  (*   Mterm.fold_left (fun arg t _ -> check_truth arg t) (truths, impls) truths *)
  (* in *)
  Trans.store (apply symbols (ieee_posts, ineqs))

let apply_trans_on_ineqs env =
  let real = Env.read_theory env [ "real" ] "Real" in
  let ineqs_symbol_names =
    [
      (Ident.op_infix "<", Lt);
      (Ident.op_infix "<=", Le);
      (Ident.op_infix ">", Gt);
      (Ident.op_infix ">=", Ge);
    ]
  in
  let ops_symbol_names =
    [
      (Ident.op_infix "+", Add);
      (Ident.op_infix "-", Sub);
      (Ident.op_infix "*", Mul);
      (Ident.op_infix "/", Div);
    ]
  in
  let real_ineqs =
    List.fold_left
      (fun mls (name, indicator) ->
        let ls = ns_find_ls real.th_export [ name ] in
        Mls.add ls indicator mls)
      Mls.empty ineqs_symbol_names
  in
  let real_ops =
    List.fold_left
      (fun mls (name, indicator) ->
        let ls = ns_find_ls real.th_export [ name ] in
        Mls.add ls indicator mls)
      Mls.empty ops_symbol_names
  in
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  let ieee_generic = Env.read_theory env [ "ieee_float" ] "GenericFloat" in
  let to_real = ns_find_ls ieee_generic.th_export [ "to_real" ] in
  (* TODO: Support minus, sqrt ? *)
  let ieee_symbol_names =
    [
      ("add_post_ieee", AddPostSingle);
      ("sub_post_ieee", SubPostSingle);
      ("mul_post_ieee", MulPostSingle);
      ("div_post_ieee", DivPostSingle);
    ]
  in
  let ieee_single = Env.read_theory env [ "mach.float" ] "Single" in
  let ieee_single =
    List.fold_left
      (fun mls (name, indicator) ->
        let ls = ns_find_ls ieee_single.th_export [ name ] in
        Mls.add ls indicator mls)
      Mls.empty ieee_symbol_names
  in
  let ieee_symbol_names =
    [
      ("add_post_ieee", AddPostDouble);
      ("sub_post_ieee", SubPostDouble);
      ("mul_post_ieee", MulPostDouble);
      ("div_post_ieee", DivPostDouble);
    ]
  in
  let ieee_double = Env.read_theory env [ "mach.float" ] "Double" in
  let ieee =
    List.fold_left
      (fun mls (name, indicator) ->
        let ls = ns_find_ls ieee_double.th_export [ name ] in
        Mls.add ls indicator mls)
      ieee_single ieee_symbol_names
  in
  let symbols = { real_ineqs; real_ops; abs; to_real; ieee } in

  let get_ieee_posts_and_ineqs = get_ieee_posts_and_ineqs symbols in
  Trans.bind
    (Trans.fold_decl get_ieee_posts_and_ineqs (Mterm.empty, Mterm.empty))
    (apply_transitivity symbols)

let () =
  Trans.register_env_transform "apply_trans_on_ineqs" apply_trans_on_ineqs
    ~desc:
      "Try to apply transitivity of inequalities without losing information."
