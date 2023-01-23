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

(* Other theorems ?

   - |(x oplus y) - x + y| <= min (|x|, |y|, eps |x + y| -> To be used for error
   combination

   - Exact addition for subnormal result (section 4.2 of handbook of FP
   arithmetic)

   - Better bounds when we know we won't underflow *)

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
  type_double : tysymbol;
}

type round_error =
  | Relative of term * term * term
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

let is_op_ls symbols ls =
  ls_equal ls symbols.add || ls_equal ls symbols.sub || ls_equal ls symbols.mul
  || ls_equal ls symbols.div

(* TODO: Add ge and gt later *)
let is_ineq_ls symbols ls =
  ls_equal ls symbols.lt || ls_equal ls symbols.le
  || ls_equal ls symbols.lt_infix
  || ls_equal ls symbols.le_infix
(* || ls_equal ls symbols.gt || ls_equal ls symbols.ge *)

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
let add_round_error info t t1 factor t2 =
  let t_info = get_info info t in
  let round_error =
    match factor with
    | None -> Some (Absolute (t1, t2))
    | Some f -> Some (Relative (t1, f, t2))
  in
  let t_info =
    { ineqs = t_info.ineqs; round_error; ieee_post = t_info.ieee_post }
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
    (* Look for "round_error x <=. y" *)
    | Tapp (_ls, [ t1; t2' ]) when ls_equal _ls symbols.round_error ->
      add_round_error info t1 t2' None t2
    | _ -> info)
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

(* t3 is a result of FP arithmetic operation involving t1 and t2 *)
(* Compute new inequalities on t3 based on what we know on t1 and t2 *)
(* TODO: Support "|x| <= max(|y|,|z|)" ??? *)
let use_ieee_thms symbols info ieee_symbol t1 t2 t3 =
  let eps = get_eps ieee_symbol in
  let to_real = get_to_real symbols ieee_symbol in
  let to_real t = fs_app to_real [ t ] ty_real in
  let abs t = t_app symbols.abs [ t ] (Some ty_real) in
  let add t1 t2 = t_app symbols.add [ t1; t2 ] (Some ty_real) in
  let sub t1 t2 = t_app symbols.sub [ t1; t2 ] (Some ty_real) in
  let mul t1 t2 = t_app symbols.mul [ t1; t2 ] (Some ty_real) in
  let div t1 t2 = t_app symbols.div [ t1; t2 ] (Some ty_real) in
  let t_ineq ls t1 t2 = ps_app ls [ t1; t2 ] in
  let min t1 t2 = fs_app symbols.min [ t1; t2 ] ty_real in
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
              let info = add_ineq info t3 ls right in
              let fmla = t_and_simp fmla (t_ineq ls (abs (to_real t3)) right) in
              (info, fmla)
            else
              failwith "TODO : Unsupported symbol")
          (info, fmla) t2_info.ineqs)
      (info, fmla) t1_info.ineqs
  in
  let fmla = t_true in
  (* Combine ieee_post with potential round_errors *)
  match t1_info.round_error with
  | Some (Absolute (t1', t2')) -> (
    match t2_info.round_error with
    | Some (Absolute (t1'', t2'')) -> (info, fmla (* failwith "TODO" *))
    | Some (Relative (t1'', t2'', t3'')) -> (info, fmla) (* TODO *)
    | None ->
      let left = abs (sub (to_real t3) (add t1' (to_real t2))) in
      let right =
        add t2' (mul eps (add (add (abs t1') (abs t2')) (abs (to_real t2))))
      in
      let info = add_round_error info t3 (add t1' (to_real t2)) None right in
      let fmla = t_and fmla (t_ineq symbols.le left right) in
      (info, fmla))
  | Some (Relative (t1', t2', t3')) -> (
    match t2_info.round_error with
    | Some _ -> failwith "TODO"
    | None ->
      (* Use trick to keep addition error tractable *)
      (* TODO : Wip *)
      let abs_err = abs (sub (to_real t3) (add (to_real t1) (to_real t2))) in
      let f1 =
        t_ineq symbols.le abs_err
          (min
             (abs (to_real t1))
             (min (abs (to_real t2)) (mul eps (add (to_real t1) (to_real t2)))))
      in
      let start = t_ineq symbols.le abs_err in
      let factor = div t2' eps in
      let f2 = start (abs (add (sub (to_real t1) t1') t1')) in
      let tmp = start (add (abs (sub (to_real t1) t1')) t3') in
      let f2 = t_by tmp f2 in
      let tmp = start (mul eps (add (mul t3' factor) (abs (to_real t2)))) in
      let f2 = t_by tmp f2 in
      let tmp =
        start
          (mul eps
             (add (mul (mul (abs (to_real t2)) eps) factor) (abs (to_real t2))))
      in
      let f2 = t_by tmp f2 in
      let t_one =
        t_const
          (Constant.ConstReal
             (Number.real_literal ~radix:10 ~neg:false ~int:"1" ~frac:"0"
                ~exp:None))
          ty_real
      in
      (* |delta| <= eps (|x| + (A/eps+1)|y|) *)
      let tmp =
        start (mul eps (add t1' (mul (abs (to_real t2)) (add factor t_one))))
      in
      let f2 = t_by tmp f2 in
      let f2 =
        t_implies (t_ineq symbols.le t3' (mul eps (abs (to_real t2)))) f2
      in
      let f3 = t_implies (t_ineq symbols.le (to_real t2) (mul eps t3')) tmp in
      let f4 =
        t_ineq symbols.le
          (abs (add (to_real t1) (to_real t2)))
          (add (add (abs (sub (to_real t1) t1')) (abs t3')) (abs (to_real t2)))
      in
      let tmp' =
        t_ineq symbols.le
          (mul factor (mul eps t3'))
          (mul factor (abs (to_real t2)))
      in
      let f4 = t_by tmp (t_and f4 tmp') in
      let tmp =
        t_and
          (t_ineq symbols.lt (mul eps t3') (abs (to_real t2)))
          (t_ineq symbols.lt (mul eps (abs (to_real t2))) t3')
      in
      let f4 = t_implies tmp f4 in
      let left = abs (sub (to_real t3) (add t1' (to_real t2))) in
      let right =
        mul eps (mul (add factor t_one) (add t3' (abs (to_real t2))))
      in
      (* TODO : Simplifier la fin pour avoir comme erreur relative t2' + eps *)
      let f =
        t_by (t_ineq symbols.le left right) (t_so f1 (t_and (t_and f2 f3) f4))
      in
      let info =
        add_round_error info t3
          (add t1' (to_real t2))
          (Some (add t_one factor))
          (add (abs t1') (abs (to_real t2)))
      in
      (info, t_and fmla f))
  | None -> (
    match t2_info.round_error with
    | Some (Absolute (t1', t2')) -> (info, fmla (* failwith "TODO" *))
    | Some (Relative _) -> (info, fmla) (* TODO *)
    | None ->
      let left = abs (sub (to_real t3) (add (to_real t1) (to_real t2))) in
      let right = mul eps (abs (add (to_real t1) (to_real t2))) in
      let info =
        add_round_error info t3
          (add (to_real t1) (to_real t2))
          (Some eps)
          (abs (add (to_real t1) (to_real t2)))
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
    | Some _ ->
      failwith "TODO round_error"
      (* Here we should find if there a floats in t1, do the recursive call on
         these floats then call apply_round_error_thm on these *)
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
  match goal.t_node with
  (* TODO: Also destruct conjunctions ? *)
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls ->
    let floats = get_floats symbols t1 @ get_floats symbols t2 in
    let _, fmla =
      List.fold_left
        (fun (info, fmla) t ->
          let info, fmla' = apply_theorems symbols info t in
          (info, t_and_simp fmla fmla'))
        (info, t_true) floats
    in
    let goal = t_by_simp goal fmla in
    add_prop_decl task kind pr goal
  | _ -> failwith "Unsupported goal, it should be a real inequality"

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
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  (* TODO: If not included we should add min max theory *)
  let real_minmax = Env.read_theory env [ "real" ] "MinMax" in
  let min = ns_find_ls real_minmax.th_export [ "min" ] in
  let safe64 = Env.read_theory env [ "cfloat" ] "Safe64" in
  let to_real_double = ns_find_ls safe64.th_export [ "to_real" ] in
  let add_post_double = ns_find_ls safe64.th_export [ "safe64_add_post" ] in
  let sub_post_double = ns_find_ls safe64.th_export [ "safe64_sub_post" ] in
  let mul_post_double = ns_find_ls safe64.th_export [ "safe64_mul_post" ] in
  let div_post_double = ns_find_ls safe64.th_export [ "safe64_div_post" ] in
  let round_error = ns_find_ls safe64.th_export [ "round_error" ] in
  let type_double = ns_find_ts safe64.th_export [ "t" ] in
  let symbols =
    {
      add;
      sub;
      mul;
      div;
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
