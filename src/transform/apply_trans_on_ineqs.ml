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

(* Other theorems ? - Exact substraction (see Higham 2002 p.45) theorem 2.4 and
   2.5 - also see section 4.2 of handbook of FP arithmetic - Better bounds when
   we know we won't underflow ? For methods, see Higham p. 472 (501) *)

open Term
open Decl
open Ty
open Theory
open Ident
open Task

type symbols = {
  add : lsymbol;
  sub : lsymbol;
  mul : lsymbol;
  div : lsymbol;
  lt : lsymbol;
  le : lsymbol;
  gt : lsymbol;
  ge : lsymbol;
  abs : lsymbol;
  to_real : lsymbol;
  add_post_ieee_single : lsymbol;
  sub_post_ieee_single : lsymbol;
  mul_post_ieee_single : lsymbol;
  div_post_ieee_single : lsymbol;
  add_post_ieee_double : lsymbol;
  sub_post_ieee_double : lsymbol;
  mul_post_ieee_double : lsymbol;
  div_post_ieee_double : lsymbol;
}

let is_op_ls symbols ls =
  ls_equal ls symbols.add || ls_equal ls symbols.sub || ls_equal ls symbols.mul
  || ls_equal ls symbols.div

(* TODO: Add ge and gt later *)
let is_ineq_ls symbols ls = ls_equal ls symbols.lt || ls_equal ls symbols.le
(* || ls_equal ls symbols.gt || ls_equal ls symbols.ge *)

let is_ieee_single symbols ls =
  ls_equal ls symbols.add_post_ieee_single
  || ls_equal ls symbols.sub_post_ieee_single
  || ls_equal ls symbols.sub_post_ieee_single
  || ls_equal ls symbols.sub_post_ieee_single

let is_ieee_double symbols ls =
  ls_equal ls symbols.add_post_ieee_double
  || ls_equal ls symbols.sub_post_ieee_double
  || ls_equal ls symbols.sub_post_ieee_double
  || ls_equal ls symbols.sub_post_ieee_double

type ineq =
  | Abs of lsymbol * term * term
  | Absminus of lsymbol * term * term * term
  | Unsupported

type ieee_post = Post of lsymbol * term * term * term

let parse_ineq symbols ineq =
  match ineq.t_node with
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls -> (
    match t1.t_node with
    | Tapp (_ls, [ t ]) when ls_equal _ls symbols.abs -> (
      match t.t_node with
      (* TODO: Is Tvar v possible or is it alway an application ? *)
      | Tvar _
      | Tapp (_, []) ->
        Abs (ls, t1, t2)
      | Tapp (ls, [ _t1; _t2 ]) when ls_equal ls symbols.sub ->
        Absminus (ls, _t1, _t2, t2)
      | _ -> Unsupported)
    | _ -> Unsupported)
  | _ -> assert false

let rec get_subterms symbols t =
  match t.t_node with
  | Tvar v -> [ t ]
  | Tapp (ls, [ t ]) when ls_equal ls symbols.abs -> get_subterms symbols t
  | Tapp (ls, terms) when is_op_ls symbols ls ->
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
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls ->
    (ieee_posts, add_ineq symbols ineqs f)
  | Tapp (ls, [ t1; t2; t3 ])
    when is_ieee_single symbols ls || is_ieee_double symbols ls ->
    (Mterm.add t3 (Post (ls, t1, t2, t3)) ieee_posts, ineqs)
  | _ -> (ieee_posts, ineqs)

let get_ieee_posts_and_ineqs symbols d (ieee_posts, ineqs) =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma ->
    add_fmlas symbols f (ieee_posts, ineqs)
  | _ -> (ieee_posts, ineqs)

let get_key mls elem =
  List.find (fun key -> Mls.find key mls = elem) (Mls.keys mls)

let use_ieee_thms symbols ineqs ieee_symbol t1 t2 t3 =
  let eps =
    t_const
      (Constant.ConstReal
         (Number.real_literal ~radix:16 ~neg:false ~int:"1" ~frac:"0"
            ~exp:(Some "-53")))
      ty_real
  in
  let abs t = t_app symbols.abs [ t ] (Some ty_real) in
  let add t1 t2 = t_app symbols.add [ t1; t2 ] (Some ty_real) in
  let sub t1 t2 = t_app symbols.sub [ t1; t2 ] (Some ty_real) in
  let mul t1 t2 = t_app symbols.mul [ t1; t2 ] (Some ty_real) in
  let _div t1 t2 = t_app symbols.div [ t1; t2 ] (Some ty_real) in
  let ineq ls t1 t2 = t_app ls [ t1; t2 ] (Some ty_bool) in
  let combine_ineqs ineq1 ineq2 =
    match ineq1 with
    | Abs (ineq_symbol, t1, t2) -> (
      match ineq2 with
      | Abs (ineq_symbol, _t1, _t2) ->
        if
          ls_equal ieee_symbol symbols.add_post_ieee_single
          || ls_equal ieee_symbol symbols.add_post_ieee_double
        then
          let left = abs t3 in
          let right = add (add t2 _t2) (mul eps (abs (add t2 _t2))) in
          ineq ineq_symbol left right
        else
          failwith "Symbols not Supported yet "
      | _ -> assert false)
    | _ -> assert false
  in
  let t1_ineqs = Mterm.find t1 ineqs in
  let t2_ineqs = Mterm.find t2 ineqs in
  let new_ineqs =
    List.fold_left
      (fun new_ineqs t1_ineq ->
        match t1_ineq with
        | Abs _ ->
          List.fold_left
            (fun new_ineqs t2_ineq ->
              match t2_ineq with
              | Abs _ -> combine_ineqs t1_ineq t2_ineq :: new_ineqs
              | _ -> [])
            new_ineqs t2_ineqs
        | Absminus _ ->
          new_ineqs
          (* TODO: Combine with other Absminus. Also combine with t2 *)
        | _ -> new_ineqs)
      [] t1_ineqs
  in
  (* Do a fold_left on t2_ineqs to combine Absminus ineqs with t1 *)
  if
    ls_equal ieee_symbol symbols.add_post_ieee_single
    || ls_equal ieee_symbol symbols.add_post_ieee_double
  then
    let left = abs (sub t3 (add t1 t2)) in
    let right = mul eps (abs (add t1 t2)) in
    ineq symbols.le left right :: new_ineqs
  else
    new_ineqs

(* TODO: Avoid traversing the same term twice *)
let rec apply_theorems symbols ieee_posts ineqs t =
  let apply = apply_theorems symbols in
  (* We check if t has the form "to_real x" *)
  match t.t_node with
  | Tapp (ls, [ x ]) when ls == symbols.to_real -> (
    try
      match Mterm.find x ieee_posts with
      | Post (ieee_symbol, t1, t2, t3) ->
        let to_real_t1 = t_app symbols.to_real [ t1 ] (Some ty_real) in
        let to_real_t2 = t_app symbols.to_real [ t2 ] (Some ty_real) in
        let new_truths = apply ieee_posts ineqs to_real_t1 in
        let new_truths = new_truths @ apply ieee_posts ineqs to_real_t2 in
        new_truths
        @ use_ieee_thms symbols ineqs ieee_symbol to_real_t1 to_real_t2 t
    with
    | Not_found -> [])
  | _ -> []

let apply symbols (ieee_posts, ineqs) task =
  let goal = Task.task_goal_fmla task in
  match goal.t_node with
  (* TODO: Also destruct conjunctions ? *)
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls -> (
    match parse_ineq symbols goal with
    | Abs (ineq_symbol, t1, t2) ->
      let new_truths = apply_theorems symbols ieee_posts ineqs t1 in
      List.fold_left
        (fun task truth ->
          add_prop_decl task Plemma
            (create_prsymbol (id_fresh "generated"))
            truth)
        task new_truths
    | Absminus _ -> failwith "Unsupported yet"
    | Unsupported -> failwith "Unsupported inequality form")
  | _ -> failwith "Unsupported goal, it should be a real inequality"

let apply_transitivity symbols (ieee_posts, ineqs) =
  Trans.store (apply symbols (ieee_posts, ineqs))

let apply_trans_on_ineqs env =
  let real = Env.read_theory env [ "real" ] "Real" in
  let lt = ns_find_ls real.th_export [ Ident.op_infix "<" ] in
  let le = ns_find_ls real.th_export [ Ident.op_infix "<=" ] in
  let gt = ns_find_ls real.th_export [ Ident.op_infix ">" ] in
  let ge = ns_find_ls real.th_export [ Ident.op_infix ">=" ] in
  let add = ns_find_ls real.th_export [ Ident.op_infix "+" ] in
  let sub = ns_find_ls real.th_export [ Ident.op_infix "-" ] in
  let mul = ns_find_ls real.th_export [ Ident.op_infix "*" ] in
  let div = ns_find_ls real.th_export [ Ident.op_infix "/" ] in
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  let ieee_generic = Env.read_theory env [ "ieee_float" ] "GenericFloat" in
  let to_real = ns_find_ls ieee_generic.th_export [ "to_real" ] in
  let ieee_single = Env.read_theory env [ "mach"; "float" ] "Single" in
  let add_post_ieee_single =
    ns_find_ls ieee_single.th_export [ "add_post_ieee" ]
  in
  let sub_post_ieee_single =
    ns_find_ls ieee_single.th_export [ "sub_post_ieee" ]
  in
  let mul_post_ieee_single =
    ns_find_ls ieee_single.th_export [ "mul_post_ieee" ]
  in
  let div_post_ieee_single =
    ns_find_ls ieee_single.th_export [ "div_post_ieee" ]
  in
  let ieee_double = Env.read_theory env [ "mach"; "float" ] "Double" in
  let add_post_ieee_double =
    ns_find_ls ieee_double.th_export [ "add_post_ieee" ]
  in
  let sub_post_ieee_double =
    ns_find_ls ieee_double.th_export [ "sub_post_ieee" ]
  in
  let mul_post_ieee_double =
    ns_find_ls ieee_double.th_export [ "mul_post_ieee" ]
  in
  let div_post_ieee_double =
    ns_find_ls ieee_double.th_export [ "div_post_ieee" ]
  in
  let symbols =
    {
      add;
      sub;
      mul;
      div;
      lt;
      le;
      gt;
      ge;
      abs;
      to_real;
      add_post_ieee_single;
      sub_post_ieee_single;
      mul_post_ieee_single;
      div_post_ieee_single;
      add_post_ieee_double;
      sub_post_ieee_double;
      mul_post_ieee_double;
      div_post_ieee_double;
    }
  in

  let get_ieee_posts_and_ineqs = get_ieee_posts_and_ineqs symbols in
  Trans.compose
    (Trans.lookup_transform "inline_trivial" env)
    (Trans.bind
       (Trans.fold_decl get_ieee_posts_and_ineqs (Mterm.empty, Mterm.empty))
       (apply_transitivity symbols))

let () =
  Trans.register_env_transform "apply_trans_on_ineqs" apply_trans_on_ineqs
    ~desc:
      "Try to apply transitivity of inequalities without losing information."
