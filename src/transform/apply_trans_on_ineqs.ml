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
  le : lsymbol;
  gt : lsymbol;
  ge : lsymbol;
  abs : lsymbol;
  to_real_double : lsymbol;
  add_post_double : lsymbol;
  sub_post_double : lsymbol;
  mul_post_double : lsymbol;
  div_post_double : lsymbol;
  round_error : lsymbol;
  type_double : tysymbol;
}

(* This type corresponds to what we know about a certain FP variable "x" *)
type info = {
  (* "(<=, y)" means "|to_real x| <= y" *)
  ineqs : (lsymbol * term) list;
  (* "(y, z)" means "round_error x y <= z", eg. "|to_real x - y| <= z" *)
  round_error : (term * term) option;
  (* If x has an ieee_post, it means it is the result of an arithmetic FP
     operation *)
  ieee_post : (lsymbol * term * term) option;
}

let is_op_ls symbols ls =
  ls_equal ls symbols.add || ls_equal ls symbols.sub || ls_equal ls symbols.mul
  || ls_equal ls symbols.div

(* TODO: Add ge and gt later *)
let is_ineq_ls symbols ls = ls_equal ls symbols.lt || ls_equal ls symbols.le
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
let add_round_error info t t1 t2 =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = t_info.ineqs;
      round_error = Some (t1, t2);
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
      add_round_error info t1 t2' t2
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
  let _div t1 t2 = t_app symbols.div [ t1; t2 ] (Some ty_real) in
  let t_ineq ls t1 t2 = ps_app ls [ t1; t2 ] in
  let t1_info = Mterm.find t1 info in
  let t2_info = Mterm.find t2 info in
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
              let fmla = t_and fmla (t_ineq ls (abs (to_real t3)) right) in
              (info, fmla)
            else
              failwith "TODO : Unsupported symbol")
          (info, fmla) t2_info.ineqs)
      (info, fmla) t1_info.ineqs
  in
  (* Combine ieee_post with potential round_errors *)
  match t1_info.round_error with
  | Some (t1', t2') -> (
    match t2_info.round_error with
    | Some (t1'', t2'') -> failwith "TODO"
    | None -> failwith "TODO")
  | None -> (
    match t2_info.round_error with
    | Some (t1', t2') -> failwith "TODO"
    | None ->
      let left = abs (sub (to_real t3) (add (to_real t1) (to_real t2))) in
      let right = mul eps (abs (add (to_real t1) (to_real t2))) in
      let info =
        add_round_error info t3 (add (to_real t1) (to_real t2)) right
      in
      let fmla = t_and fmla (t_ineq symbols.le left right) in
      (info, fmla))

(* TODO: Combine with round_error *)

(* let new_ineqs = *)
(*   List.fold_left *)
(*     (fun new_ineqs t2_ineq -> *)
(*       match t2_ineq with *)
(*       | Absminus (ineq_symbol, _, t2', t3') -> *)
(*         if ls_equal ieee_symbol symbols.add_post_double then *)
(*           (* Apply FP addition theorem *) *)
(*           let left = abs (sub t3 (add t2' t1)) in *)
(*           let right = *)
(*             add *)
(*               (add (add t2' t1) t3') *)
(*               (mul eps (add (abs t1) (abs (add t2' t3')))) *)
(*           in *)
(*           ineq ineq_symbol left right :: new_ineqs *)
(*         else *)
(*           failwith "Unsupported, todo" *)
(*         (* TODO: Combine with other Absminus. *) *)
(*       | _ -> new_ineqs) *)
(*     new_ineqs t2_ineqs *)
(* in *)
(* TODO: Should we do this if we already combined Absminus inequality ? *)
(* if ls_equal ieee_symbol symbols.add_post_double then *)
(*   let left = abs (sub t3 (add t1 t2)) in *)
(*   let right = mul eps (abs (add t1 t2)) in *)
(*   ineq symbols.le left right :: new_ineqs *)
(* else *)
(*   new_ineqs *)

(* | Absminus (ineq_symbol1, _, t2', t3') -> *)
(* let new_ineqs = *)
(*     List.fold_left *)
(*       (fun new_ineqs t2_ineq -> *)
(*         match t2_ineq with *)
(*         | Absminus (ineq_symbol2, t1', t2', t3') -> *)
(*           if ls_equal ieee_symbol symbols.add_post_double then *)
(*             let left = abs t3 in *)
(*             let right = add (add t2 t2') (mul eps (abs (add t2 t2'))) in *)
(*             let ineq_symbol = *)
(*               if *)
(*                 ls_equal ineq_symbol1 symbols.lt *)
(*                 || ls_equal ineq_symbol2 symbols.lt *)
(*               then *)
(*                 symbols.lt *)
(*               else *)
(*                 symbols.le *)
(*             in *)
(*             ineq ineq_symbol left right :: new_ineqs *)
(*           else *)
(*             failwith "Unsupported symbole" *)
(*         | _ -> new_ineqs) *)
(*       new_ineqs t2_ineqs *)
(*   in *)
(*   if ls_equal ieee_symbol symbols.add_post_double then *)
(*     (* Apply FP addition theorem *) *)
(*     (* TODO: Improve the bound to limit the accumulation of micro errors *) *)
(*     let left = abs (sub t3 (add t2' t2)) in *)
(*     let right = *)
(*       add *)
(*         (add (add t2' t2) t3') *)
(*         (mul eps (add (abs t2) (abs (add t2' t3')))) *)
(*     in *)
(*     ineq ineq_symbol1 left right :: new_ineqs *)
(*   else *)
(*     failwith "Unsupported, todo" *)
(*   (* TODO: Combine with other Absminus. *) *)
(* | _ -> new_ineqs) *)
let rec get_floats symbols t =
  match t.t_node with
  | Tvar v -> (
    match v.vs_ty.ty_node with
    | Tyapp (v, []) ->
      if ts_equal v symbols.type_double then
        [ t ]
      else
        []
    | _ -> [])
  | Tapp (ls, tl) -> List.fold_left (fun l t -> l @ get_floats symbols t) [] tl
  | _ -> []

let t_by t1 t2 = t_implies (t_or_asym t2 t_true) t1
let t_so t1 t2 = t_and t1 (t_or_asym t2 t_true)

(* Apply theorems on FP term t depending on what we know about it *)
(* TODO: Avoid traversing the same term twice. *)
let rec apply_theorems symbols info t =
  let apply = apply_theorems symbols in
  let t_info = get_info info t in
  match t_info.ieee_post with
  | Some (ieee_post, t1, t2) ->
    let info, fmla = apply info t1 in
    let info, fmla' = apply info t2 in
    let fmla = t_and fmla fmla' in
    let info, fmla' = use_ieee_thms symbols info ieee_post t1 t2 t in
    (info, t_by fmla' fmla)
  | None -> (
    match t_info.round_error with
    | Some (t1, t2) ->
      failwith "TODO round_error"
      (* Here we should find if there a floats in t1, do the recursive call on
         these floats then call apply_round_error_thm on these *)
    | None -> (info, t_true))

let apply symbols info task =
  let goal = Task.task_goal_fmla task in
  let _, task = Task.task_separate_goal task in
  match goal.t_node with
  (* TODO: Also destruct conjunctions ? *)
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls symbols ls ->
    let floats = get_floats symbols t1 @ get_floats symbols t2 in
    let info, fmla =
      List.fold_left
        (fun (info, fmla) t ->
          let info, fmla' = apply_theorems symbols info t in
          (info, t_and fmla fmla'))
        (info, t_true) floats
    in
    failwith "TODO: add new generated truths about floats in task";

    (* let task = *)
    (*   List.fold_left *)
    (*     (fun task truth -> *)
    (*       add_prop_decl task Paxiom *)
    (*         (create_prsymbol (id_fresh "generated")) *)
    (*         truth) *)
    (*     task new_truths *)
    (* in *)
    add_prop_decl task Pgoal (create_prsymbol (id_fresh "generated")) goal
  | _ -> failwith "Unsupported goal, it should be a real inequality"

let apply_transitivity symbols info = Trans.store (apply symbols info)

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
      le;
      gt;
      ge;
      abs;
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
