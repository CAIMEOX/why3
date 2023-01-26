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

type symbols = {
  add : lsymbol;
  sub : lsymbol;
  mul : lsymbol;
  div : lsymbol;
  minus : lsymbol;
  add_infix : lsymbol;
  sub_infix : lsymbol;
  mul_infix : lsymbol;
  div_infix : lsymbol;
  minus_infix : lsymbol;
  lt : lsymbol;
  lt_infix : lsymbol;
  le : lsymbol;
  le_infix : lsymbol;
  gt : lsymbol;
  gt_infix : lsymbol;
  ge : lsymbol;
  ge_infix : lsymbol;
  abs : lsymbol;
  min : lsymbol;
  to_real_double : lsymbol;
  add_post_double : lsymbol;
  sub_post_double : lsymbol;
  mul_post_double : lsymbol;
  div_post_double : lsymbol;
  round_error : lsymbol;
  rel_round_error : lsymbol;
  type_double : tysymbol;
}

type round_error =
  (* AbsRelative (t1 a t1' c) means abs (x - t1) <= a * t1' + c *)
  | AbsRelative of term * term * term * term
  | Absolute of term * term

(* This type corresponds to what we know about a certain FP variable "x" *)
type info = {
  (* "(<=, y)" means "|to_real x| <= y" *)
  ineqs : (lsymbol * term) list;
  round_error : round_error option;
  (* If x has an ieee_post, it means it is the result of an arithmetic FP
     operation *)
  ieee_post : (lsymbol * term * term) option;
}

let t_zero =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"0" ~frac:"0" ~exp:None))
    ty_real

let t_one =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"1" ~frac:"0" ~exp:None))
    ty_real

let add symbols t1 t2 =
  if t_equal t1 t_zero then
    t2
  else if t_equal t2 t_zero then
    t1
  else
    fs_app symbols.add [ t1; t2 ] ty_real

let sub symbols t1 t2 =
  if t_equal t1 t_zero then
    fs_app symbols.minus [ t2 ] ty_real
  else if t_equal t2 t_zero then
    t1
  else
    fs_app symbols.sub [ t1; t2 ] ty_real

let mul symbols t1 t2 =
  if t_equal t1 t_zero || t_equal t2 t_zero then
    t_zero
  else if t_equal t1 t_one then
    t2
  else if t_equal t2 t_one then
    t1
  else
    fs_app symbols.mul [ t1; t2 ] ty_real

let div symbols t1 t2 =
  if t_equal t1 t_zero then
    t_zero
  else if t_equal t2 t_one then
    t1
  else
    fs_app symbols.div [ t1; t2 ] ty_real

let is_op_ls symbols ls =
  ls_equal ls symbols.add || ls_equal ls symbols.sub || ls_equal ls symbols.mul
  || ls_equal ls symbols.div
  || ls_equal ls symbols.add_infix
  || ls_equal ls symbols.sub_infix
  || ls_equal ls symbols.mul_infix
  || ls_equal ls symbols.div_infix

(* TODO: Add ge and gt later *)
let is_ineq_ls symbols ls =
  ls_equal ls symbols.lt || ls_equal ls symbols.le
  || ls_equal ls symbols.lt_infix
  || ls_equal ls symbols.le_infix
(* || ls_equal ls symbols.gt || ls_equal ls symbols.ge *)

let is_add_ls symbols ls =
  ls_equal ls symbols.add || ls_equal ls symbols.add_infix

let is_sub_ls symbols ls =
  ls_equal ls symbols.sub || ls_equal ls symbols.sub_infix

let is_mul_ls symbols ls =
  ls_equal ls symbols.mul || ls_equal ls symbols.mul_infix

let is_div_ls symbols ls =
  ls_equal ls symbols.div || ls_equal ls symbols.div_infix

let is_to_real symbols ls = ls_equal ls symbols.to_real_double

let is_ieee_double symbols ls =
  ls_equal ls symbols.add_post_double
  || ls_equal ls symbols.sub_post_double
  || ls_equal ls symbols.mul_post_double
  || ls_equal ls symbols.div_post_double

let get_eps ieee_symbol =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:16 ~neg:false ~int:"1" ~frac:"0"
          ~exp:(Some "-53")))
    ty_real

let get_to_real symbols ieee_symbol = symbols.to_real_double

let get_info info t =
  try Mterm.find t info with
  | Not_found -> { ineqs = []; round_error = None; ieee_post = None }

let add_ineq info t ls t' =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = (ls, t') :: t_info.ineqs;
      round_error = t_info.round_error;
      ieee_post = t_info.ieee_post;
    }
  in
  Mterm.add t t_info info

(* TODO: Warning when we have multiple "round_error" ? *)
let add_round_error info t round_error =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = t_info.ineqs;
      round_error = Some round_error;
      ieee_post = t_info.ieee_post;
    }
  in
  Mterm.add t t_info info

(* TODO: Warning when we have multiple "ieee_posts" ? *)
let add_ieee_post info ls t t1 t2 =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = t_info.ineqs;
      round_error = t_info.round_error;
      ieee_post = Some (ls, t1, t2);
    }
  in
  Mterm.add t t_info info

let parse_round_error symbols info t1 t1' t2 =
  let rec parse t =
    if t_equal t t1' then
      (AbsRelative (t, t_one, t1', t_zero), true)
    else
      match t.t_node with
      | Tapp (_ls, [ t' ]) when ls_equal _ls symbols.abs ->
        if t_equal t' t1' then
          (AbsRelative (t1', t_one, t, t_zero), true)
        else
          (* TODO: Look inside abs ? *)
          (Absolute (t1', t2), false)
      | Tapp (_ls, [ t3; t4 ]) when is_add_ls symbols _ls -> (
        match parse t3 with
        | AbsRelative (a, factor, a', cst), _ ->
          (AbsRelative (a, factor, a', add symbols cst t4), false)
        | _ -> (
          match parse t4 with
          | AbsRelative (a, factor, a', cst), _ ->
            (AbsRelative (a, factor, a', add symbols cst t3), false)
          | _ -> (Absolute (t1', t2), false)))
      | Tapp (_ls, [ t3; t4 ]) when is_sub_ls symbols _ls -> (
        match parse t3 with
        | AbsRelative (a, factor, a', cst), _ ->
          (AbsRelative (a, factor, a', sub symbols cst t4), false)
        | _ -> (Absolute (t1', t2), false))
      | Tapp (_ls, [ t3; t4 ]) when is_mul_ls symbols _ls -> (
        match parse t3 with
        | AbsRelative (a, factor, a', cst), is_factor ->
          if is_factor then
            (AbsRelative (a, mul symbols factor t4, a', cst), true)
          else
            (AbsRelative (a, factor, a', mul symbols cst t4), false)
        | _ -> (
          match parse t4 with
          | AbsRelative (a, factor, a', cst), is_factor ->
            if is_factor then
              (AbsRelative (a, mul symbols factor t3, a', cst), true)
            else
              (AbsRelative (a, factor, a', mul symbols cst t4), false)
          | _ -> (Absolute (t1', t2), false)))
      | _ -> (Absolute (t1', t2), false)
  in
  let round_error, _ = parse t2 in
  add_round_error info t1 round_error

(* TODO: Add support for inequalities in both directions *)
let rec add_fmlas symbols f info =
  let rec add = add_fmlas symbols in
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = add f1 info in
    add f2 info
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls -> (
    match t1.t_node with
    | Tapp (_ls, [ t ]) when ls_equal _ls symbols.abs -> (
      match t.t_node with
      (* Look for "|to_real x| <= y" *)
      | Tapp (_ls, [ t ]) when is_to_real symbols _ls -> add_ineq info t ls t2
      | _ -> info)
    (* Look for "round_error t1 t1' <=. t2" *)
    | Tapp (_ls, [ t1; t1' ]) when ls_equal _ls symbols.round_error ->
      parse_round_error symbols info t1 t1' t2
    | _ -> info (* Look for rel_round_error *))
  | Tapp (ls, [ t1; t2; t3; t4 ]) when ls_equal ls symbols.rel_round_error ->
    add_round_error info t1 (AbsRelative (t2, t4, t3, t_zero))
  (* Look for safe_64_*_post *)
  | Tapp (ls, [ t1; t2; t3 ]) when is_ieee_double symbols ls ->
    add_ieee_post info ls t3 t1 t2
  | _ -> info

(* TODO : Normalize ineqs to be of the form "|x| <= y" or "|x| <= max
   (|y|,|z|)" *)
(* If we have x <= y and z <= x, generate the ineq |x| <= max (|y|,|z|) *)
(* Furthermore, resolve "max(|y|, |z|)" when those are constants *)
let collect_info symbols d info =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma ->
    add_fmlas symbols f info
  | _ -> info

let t_by t1 t2 = t_implies (t_or_asym t2 t_true) t1

let t_by_simp t1 t2 =
  match t2.t_node with
  | Ttrue -> t1
  | _ -> t_by t1 t2

let t_so t1 t2 = t_and t1 (t_or_asym t2 t_true)

(* TODO: Check when we have a None if it is well managed because t1' will not be
   0 !!! *)
(*
 * If we have :
 *  - |t1 - exact_t1| <= t1_factor * t1' + t1_cst
 *  - |t2 - exact_t2| <= t2_factor * t2' + t2_cst
 *  Then we get the following error on addition :
 *  |fl(t1 + t2) - (exact_t1 + exact_t2)| <= (eps + t1_factor + t2_factor)(t1'+t2')
                                              + (1+eps+t2_factor)t1_cst
                                              + (1+eps+t1_factor)t2_cst
 *)
let apply_addition_thm symbols info t1 exact_t1 t1_factor t1' t1_cst t2 exact_t2
    t2_factor t2' t2_cst r =
  let eps = get_eps None in
  let to_real = get_to_real symbols None in
  let to_real t = fs_app to_real [ t ] ty_real in
  let abs t = t_app symbols.abs [ t ] (Some ty_real) in
  let add, sub, mul, div =
    (add symbols, sub symbols, mul symbols, div symbols)
  in
  let t_ineq ls t1 t2 = ps_app ls [ t1; t2 ] in
  let delta_le =
    t_ineq symbols.le (abs (sub (to_real r) (add (to_real t1) (to_real t2))))
  in
  let f1 = delta_le (abs (add (sub (to_real t1) exact_t1) exact_t1)) in
  let f1' = delta_le (abs (add (sub (to_real t2) exact_t2) exact_t2)) in
  let f1 = t_by (delta_le (add (abs (sub (to_real t1) exact_t1)) t1')) f1 in
  let f1' = t_by (delta_le (add (abs (sub (to_real t2) exact_t2)) t2')) f1' in
  let f1 = t_by (delta_le (add (add (mul t1' t1_factor) t1_cst) t1')) f1 in
  let f1' = t_by (delta_le (add (add (mul t2' t2_factor) t2_cst) t2')) f1' in
  let f1 =
    t_by
      (delta_le
         (add (add (mul t1' t1_factor) t1_cst) (sub (mul eps t2') t1_cst)))
      f1
  in
  let f1' =
    t_by
      (delta_le
         (add (add (mul t2' t2_factor) t2_cst) (sub (mul eps t1') t2_cst)))
      f1'
  in
  let f1 =
    t_by
      (delta_le
         (add
            (add (mul (mul eps (add t2' t2_cst)) t1_factor) t1_cst)
            (sub (mul eps t2') t1_cst)))
      f1
  in
  let f1' =
    t_by
      (delta_le
         (add
            (add (mul (mul eps (add t1' t1_cst)) t2_factor) t2_cst)
            (sub (mul eps t1') t2_cst)))
      f1'
  in
  let delta_ineq =
    delta_le
      (add
         (add (mul (add eps t1_factor) t2') (mul (add eps t2_factor) t1'))
         (add (mul (add t2_factor eps) t1_cst) (mul (add t1_factor eps) t2_cst)))
  in
  let f1 = t_by delta_ineq f1 in
  let f1' = t_by delta_ineq f1' in
  let f1 =
    t_implies (t_ineq symbols.le (add t1' t1_cst) (mul eps (add t2' t2_cst))) f1
  in
  let f1' =
    t_implies
      (t_ineq symbols.le (add t2' t2_cst) (mul eps (add t1' t1_cst)))
      f1'
  in
  let f1_test =
    t_ineq symbols.le
      (abs (to_real t1))
      (abs (sub (add (to_real t1) exact_t1) exact_t1))
  in
  let f2_test =
    t_ineq symbols.le
      (abs (to_real t2))
      (abs (sub (add (to_real t2) exact_t2) exact_t2))
  in
  let f2 =
    t_by
      (t_ineq symbols.le
         (abs (add (to_real t1) (to_real t2)))
         (add
            (abs (sub (add (to_real t1) exact_t1) exact_t1))
            (abs (sub (add (to_real t2) exact_t2) exact_t2))))
      (t_and f1_test f2_test)
  in
  let f1_test' =
    t_ineq symbols.le
      (abs (sub (add (to_real t1) exact_t1) exact_t1))
      (add (abs (sub (to_real t1) exact_t1)) t1')
  in
  let f2_test' =
    t_ineq symbols.le
      (abs (sub (add (to_real t2) exact_t2) exact_t2))
      (add (abs (sub (to_real t2) exact_t2)) t2')
  in
  let f2 =
    t_by
      (t_ineq symbols.le
         (abs (add (to_real t1) (to_real t2)))
         (add
            (add (abs (sub (to_real t1) exact_t1)) t1')
            (add (abs (sub (to_real t2) exact_t2)) t2')))
      (t_and f2 (t_and f1_test' f2_test'))
  in
  let f2 =
    t_and f2
      (t_and
         (t_ineq symbols.le (mul t1' t1_factor)
            (mul t1_factor (div (add t2' t2_factor) eps)))
         (t_ineq symbols.le (mul t2' t2_factor)
            (mul t2_factor (div (add t1' t1_factor) eps))))
  in
  let f2 = t_by delta_ineq f2 in
  let f2 =
    t_implies
      (t_and
         (t_ineq symbols.lt (mul eps (add t1' t1_cst)) (add t2' t2_cst))
         (t_ineq symbols.lt (mul eps (add t2' t2_cst)) (add t1' t1_cst)))
      f2
  in
  let f = t_by delta_ineq (t_and (t_and f1 f1') f2) in
  let left = abs (sub (to_real r) (add exact_t1 exact_t2)) in
  let right =
    add
      (mul (add (add t1_factor t2_factor) eps) (add t1' t2'))
      (add
         (mul (add (add t_one eps) t2_factor) t1_cst)
         (mul (add (add t_one eps) t1_factor) t2_cst))
  in
  let f =
    t_and f
      (t_ineq symbols.le
         (abs (sub (to_real r) (add exact_t1 exact_t2)))
         (add
            (abs (sub (to_real r) (add (to_real t1) (to_real t2))))
            (add
               (add (add (mul t2_factor t2') t2_cst) t1_cst)
               (mul t1_factor t1'))))
  in
  let f = t_by (t_ineq symbols.le left right) f in
  let info =
    add_round_error info r
      (AbsRelative
         ( add exact_t1 exact_t2,
           add (add t1_factor t2_factor) eps,
           add t1' t2',
           add
             (mul (add (add t_one eps) t2_factor) t1_cst)
             (mul (add (add t_one eps) t1_factor) t2_cst) ))
  in
  (info, f)

(* t3 is a result of FP arithmetic operation involving t1 and t2 *)
(* Compute new inequalities on t3 based on what we know on t1 and t2 *)
(* TODO: Support "|x| <= max(|y|,|z|)" ??? *)
let use_ieee_thms symbols info ieee_symbol t1 t2 r =
  let eps = get_eps None in
  let to_real = get_to_real symbols None in
  let to_real t = fs_app to_real [ t ] ty_real in
  let abs t = t_app symbols.abs [ t ] (Some ty_real) in
  let add t1 t2 = t_app symbols.add [ t1; t2 ] (Some ty_real) in
  let sub t1 t2 = t_app symbols.sub [ t1; t2 ] (Some ty_real) in
  let mul t1 t2 = t_app symbols.mul [ t1; t2 ] (Some ty_real) in
  let _div t1 t2 = t_app symbols.div [ t1; t2 ] (Some ty_real) in
  let t_ineq ls t1 t2 = ps_app ls [ t1; t2 ] in
  let _min t1 t2 = fs_app symbols.min [ t1; t2 ] ty_real in
  let t1_info = get_info info t1 in
  let t2_info = get_info info t2 in
  let fmla = t_true in
  (* Combine ieee_post with the inequalities of t1 and t2 *)
  let info, fmla =
    List.fold_left
      (fun (info, fmla) (ls1, t1') ->
        List.fold_left
          (fun (info, fmla) (ls2, t2') ->
            if ls_equal ieee_symbol symbols.add_post_double then
              let ls =
                if ls_equal ls1 symbols.lt || ls_equal ls2 symbols.lt then
                  symbols.lt
                else
                  symbols.le
              in
              let right = add (add t1' t2') (mul eps (abs (add t1' t2'))) in
              let info = add_ineq info r ls right in
              let fmla = t_and_simp fmla (t_ineq ls (abs (to_real r)) right) in
              (info, fmla)
            else
              failwith "TODO : Unsupported symbol")
          (info, fmla) t2_info.ineqs)
      (info, fmla) t1_info.ineqs
  in
  (* Combine ieee_post with potential round_errors *)
  match t1_info.round_error with
  (* TODO: Correct handling of Relative and Absolute error combination *)
  (* TODO: Correct handling of Absolute and Absolute error combination *)
  (* TODO: Correct handling of Absolute and None error combination *)
  | Some (Absolute (exact_t1, t1')) -> failwith " TODO absolute "
  (* ( *)
  (*   match t2_info.round_error with *)
  (*   | Some (Absolute (exact_t2, t2')) -> *)
  (*     (* TODO *) *)
  (*     apply_addition_thm symbols info t1 exact_t1 t_one t1' t2 exact_t2 t_one *)
  (*       t2' r *)
  (*   | Some (AbsRelative (exact_t2, t2_factor, t2', cst)) -> *)
  (*     failwith "TODO" (* TODO *) *)
  (*   | None -> *)
  (*     (* TODO: This gives some shit result, correct *) *)
  (*     apply_addition_thm symbols info t1 exact_t1 t_one t1' t2 (to_real t2) *)
  (*       t_zero *)
  (*       (abs (to_real t2)) *)
  (*       r) *)
  | Some (AbsRelative (exact_t1, t1_factor, t1', t1_cst)) -> (
    match t2_info.round_error with
    | Some (Absolute _) -> failwith "TODO absolute 2" (* TODO *)
    | Some (AbsRelative (exact_t2, t2_factor, t2', t2_cst)) ->
      (* OK *)
      apply_addition_thm symbols info t1 exact_t1 t1_factor t1' t1_cst t2
        exact_t2 t2_factor t2' t2_cst r
    | None ->
      (* OK *)
      apply_addition_thm symbols info t1 exact_t1 t1_factor t1' t1_cst t2
        (to_real t2) t_zero
        (abs (to_real t2))
        t_zero r)
  | None -> (
    match t2_info.round_error with
    | Some (Absolute (exact_t2, t2')) -> failwith "TODO absolute 3"
    (* TODO *)
    | Some (AbsRelative (exact_t2, t2_factor, t2', cst)) ->
      (* OK *)
      apply_addition_thm symbols info t1 (to_real t1) t_zero
        (abs (to_real t1))
        t_zero t2 exact_t2 t2_factor t2' cst r
    | None ->
      (* OK *)
      let left = abs (sub (to_real r) (add (to_real t1) (to_real t2))) in
      let right = mul eps (abs (add (to_real t1) (to_real t2))) in
      let info =
        add_round_error info r
          (AbsRelative
             ( add (to_real t1) (to_real t2),
               eps,
               abs (add (to_real t1) (to_real t2)),
               t_zero ))
      in
      let fmla = t_and fmla (t_ineq symbols.le left right) in
      (info, fmla))

let is_ty_float symbols ty =
  match ty.ty_node with
  | Tyapp (v, []) ->
    if ts_equal v symbols.type_double then
      true
    else
      false
  | _ -> false

let rec get_floats symbols t =
  match t.t_node with
  | Tvar v ->
    if is_ty_float symbols v.vs_ty then
      [ t ]
    else
      []
  | Tapp (ls, []) ->
    if is_ty_float symbols (Opt.get ls.ls_value) then
      [ t ]
    else
      []
  | Tapp (ls, tl) -> List.fold_left (fun l t -> l @ get_floats symbols t) [] tl
  | _ -> []

(* Apply theorems on FP term t depending on what we know about it *)
(* TODO: Avoid traversing the same term twice. *)
let rec apply_theorems symbols info t =
  let apply = apply_theorems symbols in
  let t_info = get_info info t in
  match t_info.ieee_post with
  | Some (ieee_post, t1, t2) ->
    let info, fmla = apply info t1 in
    let info, fmla' = apply info t2 in
    let fmla = t_and_simp fmla fmla' in
    let info, fmla' = use_ieee_thms symbols info ieee_post t1 t2 t in
    (info, t_by_simp fmla' fmla)
  | None -> (
    match t_info.round_error with
    | Some (AbsRelative (exact_t, t_factor, t', cst)) ->
      let floats = get_floats symbols exact_t in
      let info, fmla =
        List.fold_left
          (fun (info, fmla) t ->
            let info, fmla' = apply_theorems symbols info t in
            (info, t_and_simp fmla fmla'))
          (info, t_true) floats
      in
      (* TODO: Apply round_error theorem on all floats *)
      (info, fmla)
    | Some (Absolute (exact_t, t')) ->
      let floats = get_floats symbols exact_t in
      let info, fmla =
        List.fold_left
          (fun (info, fmla) t ->
            let info, fmla' = apply_theorems symbols info t in
            (info, t_and_simp fmla fmla'))
          (info, t_true) floats
      in
      (* TODO: Apply round_error theorem on all floats *)
      (info, fmla)
    | None -> (info, t_true))

let apply symbols info task =
  let goal_tdecl, task = Task.task_separate_goal task in
  let kind, pr, goal =
    match goal_tdecl.td_node with
    | Decl d -> (
      match d.d_node with
      | Dprop p -> p
      | _ -> assert false)
    | _ -> assert false
  in
  let floats = get_floats symbols goal in
  let _, fmla =
    List.fold_left
      (fun (info, fmla) t ->
        let info, fmla' = apply_theorems symbols info t in
        (info, t_and_simp fmla fmla'))
      (info, t_true) floats
  in
  let goal = t_by_simp goal fmla in
  add_prop_decl task kind pr goal

let apply_transitivity symbols info = Trans.store (apply symbols info)

let apply_trans_on_ineqs env =
  let real = Env.read_theory env [ "real" ] "Real" in
  let lt = ns_find_ls real.th_export [ Ident.op_infix "<" ] in
  let le = ns_find_ls real.th_export [ Ident.op_infix "<=" ] in
  let gt = ns_find_ls real.th_export [ Ident.op_infix ">" ] in
  let ge = ns_find_ls real.th_export [ Ident.op_infix ">=" ] in
  let real_infix = Env.read_theory env [ "real" ] "RealInfix" in
  let lt_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "<." ] in
  let le_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "<=." ] in
  let gt_infix = ns_find_ls real_infix.th_export [ Ident.op_infix ">." ] in
  let ge_infix = ns_find_ls real_infix.th_export [ Ident.op_infix ">=." ] in
  let add = ns_find_ls real.th_export [ Ident.op_infix "+" ] in
  let sub = ns_find_ls real.th_export [ Ident.op_infix "-" ] in
  let mul = ns_find_ls real.th_export [ Ident.op_infix "*" ] in
  let div = ns_find_ls real.th_export [ Ident.op_infix "/" ] in
  let minus = ns_find_ls real.th_export [ Ident.op_prefix "-" ] in
  let add_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "+." ] in
  let sub_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "-." ] in
  let mul_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "*." ] in
  let div_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "/." ] in
  let minus_infix = ns_find_ls real_infix.th_export [ Ident.op_prefix "-." ] in
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  let real_minmax = Env.read_theory env [ "real" ] "MinMax" in
  let min = ns_find_ls real_minmax.th_export [ "min" ] in
  let safe64 = Env.read_theory env [ "cfloat" ] "Safe64" in
  let to_real_double = ns_find_ls safe64.th_export [ "to_real" ] in
  let add_post_double = ns_find_ls safe64.th_export [ "safe64_add_post" ] in
  let sub_post_double = ns_find_ls safe64.th_export [ "safe64_sub_post" ] in
  let mul_post_double = ns_find_ls safe64.th_export [ "safe64_mul_post" ] in
  let div_post_double = ns_find_ls safe64.th_export [ "safe64_div_post" ] in
  let round_error = ns_find_ls safe64.th_export [ "round_error" ] in
  let rel_round_error = ns_find_ls safe64.th_export [ "rel_round_error" ] in
  let type_double = ns_find_ts safe64.th_export [ "t" ] in
  let symbols =
    {
      add;
      sub;
      mul;
      div;
      minus;
      add_infix;
      sub_infix;
      mul_infix;
      div_infix;
      minus_infix;
      lt;
      lt_infix;
      le;
      le_infix;
      gt;
      gt_infix;
      ge;
      ge_infix;
      abs;
      min;
      to_real_double;
      add_post_double;
      sub_post_double;
      mul_post_double;
      div_post_double;
      round_error;
      rel_round_error;
      type_double;
    }
  in

  let collect_info = collect_info symbols in
  Trans.bind
    (Trans.fold_decl collect_info Mterm.empty)
    (apply_transitivity symbols)

let () =
  Trans.register_env_transform "apply_trans_on_ineqs" apply_trans_on_ineqs
    ~desc:
      "Try to apply transitivity of inequalities without losing information."
