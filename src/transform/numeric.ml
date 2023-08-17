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

type ieee_symbols = {
  ieee_type : tysymbol;
  to_real : lsymbol;
  add_post : lsymbol;
  sub_post : lsymbol;
  mul_post : lsymbol;
  div_post : lsymbol;
  add_pre : lsymbol;
  sub_pre : lsymbol;
  mul_pre : lsymbol;
  div_pre : lsymbol;
}

type ufloat_symbols = {
  ufloat_type : tysymbol;
  to_real : lsymbol;
  uadd : lsymbol;
  usub : lsymbol;
  umul : lsymbol;
  udiv : lsymbol;
}

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
  fw_error : lsymbol;
  usingle_symbols : ufloat_symbols;
  udouble_symbols : ufloat_symbols;
  single_symbols : ieee_symbols;
  double_symbols : ieee_symbols;
}

let symbols = ref None

(* Forward error associated to a real term t, eg. (x, rel, x', cst) stands for
   |t - x| <= rel x' + cst *)
type error_fmla = term * term * term * term

(** We have different errors formulas depending of the occurence of underflows.
    We distinguish each case with a separate formula. We have one formula for
    the case where no underflow occured, and a list of formulas for the case
    where underflow happened, with one formula per overflow. This is done to
    have a better combination of errors with multiplication. *)
type error = {
  no_underflow : error_fmla;
  (*
   * [ ab',cd; ab;cd'; abcd';1 ] means we potentially have an underflow on ab', on cd' and on (ab)(cd)'.
   * This causes 3 potential upper error bounds :
   * - eta |cd|
   * - eta |ab|
   * - eta
   *)
  underflow : (term * term) list;
}

(* This type corresponds to the numeric info we have on a real of float term *)
type term_info = {
  (* "(<=, y)" means "|to_real x| <= y" *)
  ineqs : (lsymbol * term) list;
  error : error option;
  (* If x has an ieee_post, it means it is the result of an arithmetic FP
     operation *)
  ieee_post : (lsymbol * term * term) option;
}

let add_basic_attr = create_attribute "expl:add_basic"
let add_combine_attr = create_attribute "expl:add_combine"
let sub_basic_attr = create_attribute "expl:sub_basic"
let sub_combine_attr = create_attribute "expl:sub_combine"
let mul_basic_attr = create_attribute "expl:mul_basic"
let mul_combine_attr = create_attribute "expl:mul_combine"

let zero =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"0" ~frac:"0" ~exp:None))
    ty_real

let one =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"1" ~frac:"0" ~exp:None))
    ty_real

let is_zero t = t_equal zero t
let add t1 t2 = fs_app (Opt.get !symbols).add [ t1; t2 ] ty_real

let add_simp t1 t2 =
  if t_equal t1 zero then
    t2
  else if t_equal t2 zero then
    t1
  else
    add t1 t2

let sub t1 t2 = fs_app (Opt.get !symbols).sub [ t1; t2 ] ty_real

let sub_simp t1 t2 =
  if t_equal t1 zero then
    fs_app (Opt.get !symbols).minus [ t2 ] ty_real
  else if t_equal t2 zero then
    t1
  else
    sub t1 t2

let mul t1 t2 = fs_app (Opt.get !symbols).mul [ t1; t2 ] ty_real

let mul_simp t1 t2 =
  if t_equal t1 zero || t_equal t2 zero then
    zero
  else if t_equal t1 one then
    t2
  else if t_equal t2 one then
    t1
  else
    mul t1 t2

let div t1 t2 = fs_app (Opt.get !symbols).div [ t1; t2 ] ty_real

let div_simp t1 t2 =
  if t_equal t1 zero then
    zero
  else if t_equal t2 one then
    t1
  else
    div t1 t2

let ( +. ) x y = add x y
let ( -. ) x y = sub x y
let ( *. ) x y = mul x y
let ( /. ) x y = div x y
let ( ++. ) x y = add_simp x y
let ( --. ) x y = sub_simp x y
let ( **. ) x y = mul_simp x y
let ( //. ) x y = div_simp x y
let ( <=. ) x y = ps_app (Opt.get !symbols).le [ x; y ]
let ( <. ) x y = ps_app (Opt.get !symbols).lt [ x; y ]

let abs t =
  let symbols = Opt.get !symbols in
  match t.t_node with
  (* Don't add an abs symbol on top of another *)
  | Tapp (ls, [ t ]) when ls_equal symbols.abs ls -> t
  | _ -> fs_app symbols.abs [ t ] ty_real

(* TODO: Add ge and gt later *)
let is_ineq_ls ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.lt || ls_equal ls symbols.le
  || ls_equal ls symbols.lt_infix
  || ls_equal ls symbols.le_infix
(* || ls_equal ls symbols.gt || ls_equal ls symbols.ge *)

let is_add_ls ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.add || ls_equal ls symbols.add_infix

let is_sub_ls ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.sub || ls_equal ls symbols.sub_infix

let is_mul_ls ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.mul || ls_equal ls symbols.mul_infix

let is_abs_ls ls = ls_equal ls (Opt.get !symbols).abs

let is_to_real_ls ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.single_symbols.to_real
  || ls_equal ls symbols.double_symbols.to_real

let is_ieee_post ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.single_symbols.add_post
  || ls_equal ls symbols.single_symbols.sub_post
  || ls_equal ls symbols.single_symbols.mul_post
  || ls_equal ls symbols.single_symbols.div_post
  || ls_equal ls symbols.double_symbols.add_post
  || ls_equal ls symbols.double_symbols.sub_post
  || ls_equal ls symbols.double_symbols.mul_post
  || ls_equal ls symbols.double_symbols.div_post

let is_ieee_pre ls =
  let symbols = Opt.get !symbols in
  ls_equal ls symbols.single_symbols.add_pre
  || ls_equal ls symbols.single_symbols.sub_pre
  || ls_equal ls symbols.single_symbols.mul_pre
  || ls_equal ls symbols.single_symbols.div_pre
  || ls_equal ls symbols.double_symbols.add_pre
  || ls_equal ls symbols.double_symbols.sub_pre
  || ls_equal ls symbols.double_symbols.mul_pre
  || ls_equal ls symbols.double_symbols.div_pre

let is_ty_float ty =
  let symbols = Opt.get !symbols in
  match ty.ty_node with
  | Tyapp (v, []) ->
    if
      ts_equal v symbols.single_symbols.ieee_type
      || ts_equal v symbols.double_symbols.ieee_type
      || ts_equal v symbols.usingle_symbols.ufloat_type
      || ts_equal v symbols.udouble_symbols.ufloat_type
    then
      true
    else
      false
  | _ -> false

let eps ieee_type =
  let symbols = Opt.get !symbols in
  let value =
    if ts_equal ieee_type symbols.single_symbols.ieee_type then
      "-24"
    else if ts_equal ieee_type symbols.double_symbols.ieee_type then
      "-53"
    else
      failwith (Format.asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:16 ~neg:false ~int:"1" ~frac:"0"
          ~exp:(Some value)))
    ty_real

let eta ieee_type =
  let symbols = Opt.get !symbols in
  let value =
    if ts_equal ieee_type symbols.single_symbols.ieee_type then
      "-150"
    else if ts_equal ieee_type symbols.single_symbols.ieee_type then
      "-1075"
    else
      failwith (Format.asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:16 ~neg:false ~int:"1" ~frac:"0"
          ~exp:(Some value)))
    ty_real

let to_real ieee_type t =
  let symbols = Opt.get !symbols in
  let to_real =
    if ts_equal ieee_type symbols.single_symbols.ieee_type then
      symbols.single_symbols.to_real
    else if ts_equal ieee_type symbols.single_symbols.ieee_type then
      symbols.double_symbols.to_real
    else
      failwith (Format.asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  fs_app to_real [ t ] ty_real

let get_info info t =
  try Mterm.find t info with
  | Not_found -> { ineqs = []; error = None; ieee_post = None }

let add_ineq info t ls t' =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = (ls, t') :: t_info.ineqs;
      error = t_info.error;
      ieee_post = t_info.ieee_post;
    }
  in
  Mterm.add t t_info info

let add_error info t error =
  let t_info = get_info info t in
  let t_info =
    { ineqs = t_info.ineqs; error = Some error; ieee_post = t_info.ieee_post }
  in
  Mterm.add t t_info info

let add_ieee_post info ls t t1 t2 =
  let t_info = get_info info t in
  let t_info =
    {
      ineqs = t_info.ineqs;
      error = t_info.error;
      ieee_post = Some (ls, t1, t2);
    }
  in
  Mterm.add t t_info info

let get_ts t =
  match t.t_ty with
  | None -> assert false
  | Some ty -> (
    match ty.ty_node with
    | Tyvar tv -> assert false
    | Tyapp (ts, []) -> ts
    | _ -> assert false)

let rec get_floats t =
  let l =
    match t.t_ty with
    | Some ty when is_ty_float ty -> [ t ]
    | _ -> []
  in
  match t.t_node with
  | Tapp (ls, tl) -> List.fold_left (fun l t -> l @ get_floats t) l tl
  | _ -> l

let get_float_name printer s t =
  match t.t_node with
  | Tvar v ->
    let name = id_unique printer v.vs_name in
    if s = "" then
      name
    else
      s ^ "," ^ name
  | Tapp (ls, []) ->
    let name = id_unique printer ls.ls_name in
    if s = "" then
      name
    else
      s ^ "," ^ name
  | _ -> assert false

(* For each new goal generated by the transformation that corresponds to a
   floating point theorem, we can apply the theorem to prove it trivially. We
   look for the attribute of the goal in order to know which theorem to
   apply. *)
let apply_theorems env info task =
  let naming_table = Args_wrapper.build_naming_tables task in
  let attrs = (task_goal task).pr_name.id_attrs in
  let goal = task_goal_fmla task in
  if
    Sattr.mem add_combine_attr attrs
    || Sattr.mem sub_combine_attr attrs
    || Sattr.mem mul_combine_attr attrs
  then
    let args =
      match goal.t_node with
      | Tapp (ls, [ t1; t2 ]) when is_ineq_ls ls -> (
        match t1.t_node with
        | Tapp (_ls, [ t ]) when is_abs_ls _ls -> (
          match t.t_node with
          | Tapp (_ls, [ t1; t2 ]) when is_sub_ls _ls -> (
            match t1.t_node with
            | Tapp (_ls, [ t ]) when is_to_real_ls _ls -> (
              let t_info = get_info info t in
              match t_info.ieee_post with
              | Some (ieee_post, t1, t2) ->
                let get_float_name = get_float_name naming_table.printer in
                List.fold_left get_float_name "" [ t1; t2 ]
              | None -> assert false)
            | _ -> assert false)
          | _ -> assert false)
        | _ -> assert false)
      | _ -> assert false
    in
    let add_expl s pr term =
      let a = create_attribute ("expl:" ^ s) in
      let t = t_attr_add a term in
      [ create_prop_decl Pgoal pr t ]
    in
    let op =
      if Sattr.mem add_combine_attr attrs then
        "add"
      else if Sattr.mem sub_combine_attr attrs then
        "sub"
      else
        "mul"
    in
    let task_list =
      Trans.apply_transform_args "apply" env
        [ op ^ "_combine"; "with"; args ]
        naming_table "" task
    in
    List.map
      (Trans.apply (Trans.goal (add_expl ("ieee " ^ op ^ " error"))))
      task_list
  else
    [ task ]

let apply_args symbols f t t_info =
  let to_real = to_real (get_ts t) in
  match t_info.error with
  | None -> f t (to_real t) zero (abs (to_real t)) zero
  | Some error ->
    let exact_t, rel_err, t', cst_err = error.no_underflow in
    if t_equal zero rel_err then
      assert false
    else
      f t exact_t rel_err t' cst_err

(* Generates the formula for the forward error of r = x .* y. 2 formulas are
   created, one that matches the multiplication theorem and one with a bit of
   simplification. *)
let get_mul_forward_error (prove_overflow : bool) (info : term_info Mterm.t)
    (x : term) (y : term) (r : term) :
    term_info Mterm.t * (prsymbol * term) * (prsymbol * term) option =
  if prove_overflow then
    assert false
  else
    let ts = get_ts r in
    let eps = eps ts in
    let eta = eta ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    let attrs = Sattr.empty in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x *. to_real y)) in
      let right = (eps *. abs (to_real x *. to_real y)) +. eta in
      let info =
        add_error info r
          {
            no_underflow =
              (to_real x *. to_real y, eps, abs (to_real x *. to_real y), eta);
            underflow = [];
          }
      in
      let attrs = Sattr.add mul_basic_attr attrs in
      let pr = create_prsymbol (id_fresh ~attrs "MulErrBasic") in
      (info, (pr, left <=. right), None)
    | _ ->
      let combine_errors_with_multiplication t1 exact_t1 t1_factor t1' t1_cst t2
          exact_t2 t2_factor t2' t2_cst r =
        let rel_err =
          eps
          +. (t1_factor +. t2_factor +. (t1_factor *. t2_factor))
             *. (one +. eps)
        in
        let cst_err =
          (((t2_cst +. (t2_cst *. t1_factor)) *. t1')
          +. ((t1_cst +. (t1_cst *. t2_factor)) *. t2')
          +. (t1_cst *. t2_cst))
          *. (one +. eps)
          +. eta
        in
        let rel_err' =
          eps
          ++. (t1_factor ++. t2_factor ++. (t1_factor **. t2_factor))
              **. (one ++. eps)
        in
        let cst_err' =
          (((t2_cst ++. (t2_cst **. t1_factor)) **. t1')
          ++. ((t1_cst ++. (t1_cst **. t2_factor)) **. t2')
          ++. (t1_cst **. t2_cst))
          **. (one ++. eps)
          ++. eta
        in
        let left = abs (to_real r -. (exact_t1 *. exact_t2)) in
        let right = (rel_err *. (t1' *. t2')) +. cst_err in
        let right' = (rel_err' **. t1' **. t2') ++. cst_err' in
        let info =
          add_error info r
            {
              no_underflow =
                (exact_t1 *. exact_t2, rel_err', t1' *. t2', cst_err');
              underflow = [];
            }
        in
        let attrs = Sattr.add mul_combine_attr attrs in
        let pr = create_prsymbol (id_fresh ~attrs "MulErrCombine") in
        if t_equal right right' && false then
          (info, (pr, left <=. right), None)
        else
          let pr' = create_prsymbol (id_fresh "MulErrCombine") in
          (info, (pr, left <=. right), Some (pr', left <=. right'))
      in
      let combine_errors_with_multiplication =
        apply_args symbols combine_errors_with_multiplication x x_info
      in
      let combine_errors_with_multiplication =
        apply_args symbols combine_errors_with_multiplication y y_info
      in
      combine_errors_with_multiplication r

(* Generates the formula for the forward error of r = x .- y *)
let get_sub_forward_error prove_overflow info x y r =
  if prove_overflow then
    assert false
  else
    let ts = get_ts r in
    let eps = eps ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    let attrs = Sattr.empty in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x -. to_real y)) in
      let right = eps *. abs (to_real x +. to_real y) in
      let info =
        add_error info r
          {
            no_underflow =
              (to_real x -. to_real y, eps, abs (to_real x +. to_real y), zero);
            underflow = [];
          }
      in
      let attrs = Sattr.add sub_basic_attr attrs in
      let pr = create_prsymbol (id_fresh ~attrs "SubErrBasic") in
      (info, (pr, left <=. right), None)
    | _ ->
      let combine_errors_with_substraction t1 exact_t1 t1_factor t1' t1_cst t2
          exact_t2 t2_factor t2' t2_cst r =
        let rel_err = t1_factor +. t2_factor +. eps in
        let cst_err =
          ((one +. eps +. t2_factor) *. t1_cst)
          +. ((one +. eps +. t1_factor) *. t2_cst)
        in
        let total_err = (rel_err *. (t1' +. t2')) +. cst_err in
        let rel_err' = t1_factor ++. t2_factor ++. eps in
        let cst_err' =
          ((one ++. eps ++. t2_factor) **. t1_cst)
          ++. ((one ++. eps ++. t1_factor) **. t2_cst)
        in
        let total_err' = (rel_err' **. (t1' ++. t2')) ++. cst_err' in
        let left = abs (to_real r -. (exact_t1 -. exact_t2)) in
        let info =
          add_error info r
            {
              no_underflow =
                (exact_t1 -. exact_t2, rel_err', t1' +. t2', cst_err');
              underflow = [];
            }
        in
        let attrs = Sattr.add sub_combine_attr attrs in
        let pr = create_prsymbol (id_fresh ~attrs "SubErrCombine") in
        if t_equal total_err total_err' then
          (info, (pr, left <=. total_err), None)
        else
          let pr' = create_prsymbol (id_fresh "SubErrCombine") in
          (info, (pr, left <=. total_err), Some (pr', left <=. total_err'))
      in
      let combine_errors_with_substraction =
        apply_args symbols combine_errors_with_substraction x x_info
      in
      let combine_errors_with_addition =
        apply_args symbols combine_errors_with_substraction y y_info
      in
      combine_errors_with_addition r

(* Generates the formula for the forward error of r = x .- y *)
let get_add_forward_error prove_overflow info x y r =
  if prove_overflow then
    assert false
  (* apply_addition_thm_for_overflow symbols info f x y r *)
  else
    let ts = get_ts r in
    let eps = eps ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    let attrs = Sattr.empty in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x +. to_real y)) in
      let right = eps *. abs (to_real x +. to_real y) in
      let info =
        add_error info r
          {
            no_underflow =
              (to_real x +. to_real y, eps, abs (to_real x +. to_real y), zero);
            underflow = [];
          }
      in
      let attrs = Sattr.add add_basic_attr attrs in
      let pr = create_prsymbol (id_fresh ~attrs "AddErrBasic") in
      (info, (pr, left <=. right), None)
    | _ ->
      let combine_errors_with_addition t1 exact_t1 t1_factor t1' t1_cst t2
          exact_t2 t2_factor t2' t2_cst r =
        let rel_err = t1_factor +. t2_factor +. eps in
        let cst_err =
          ((one +. eps +. t2_factor) *. t1_cst)
          +. ((one +. eps +. t1_factor) *. t2_cst)
        in
        let total_err = (rel_err *. (t1' +. t2')) +. cst_err in
        let rel_err' = t1_factor ++. t2_factor ++. eps in
        let cst_err' =
          ((one ++. eps ++. t2_factor) **. t1_cst)
          ++. ((one ++. eps ++. t1_factor) **. t2_cst)
        in
        let total_err' = (rel_err' **. (t1' ++. t2')) ++. cst_err' in
        let left = abs (to_real r -. (exact_t1 +. exact_t2)) in
        let info =
          add_error info r
            {
              no_underflow =
                (exact_t1 +. exact_t2, rel_err', t1' +. t2', cst_err');
              underflow = [];
            }
        in
        let attrs = Sattr.add add_combine_attr attrs in
        let pr = create_prsymbol (id_fresh ~attrs "AddErrCombine") in
        if t_equal total_err total_err' then
          (info, (pr, left <=. total_err), None)
        else
          let pr' = create_prsymbol (id_fresh "AddErrCombine") in
          (info, (pr, left <=. total_err), Some (pr', left <=. total_err'))
      in
      let combine_errors_with_addition =
        apply_args symbols combine_errors_with_addition x x_info
      in
      let combine_errors_with_addition =
        apply_args symbols combine_errors_with_addition y y_info
      in
      combine_errors_with_addition r

(* r is a result of FP arithmetic operation involving t1 and t2 *)
(* Compute new inequalities on r based on what we know on t1 and t2 *)
let use_ieee_thms prove_overflow info ieee_symbol t1 t2 r :
    term_info Mterm.t * (prsymbol * term) * (prsymbol * term) option =
  let symbols = Opt.get !symbols in
  if
    ls_equal ieee_symbol symbols.single_symbols.add_post
    || ls_equal ieee_symbol symbols.double_symbols.add_post
  then
    get_add_forward_error prove_overflow info t1 t2 r
  else if
    ls_equal ieee_symbol symbols.single_symbols.sub_post
    || ls_equal ieee_symbol symbols.double_symbols.sub_post
  then
    get_sub_forward_error prove_overflow info t1 t2 r
  else if
    ls_equal ieee_symbol symbols.single_symbols.mul_post
    || ls_equal ieee_symbol symbols.double_symbols.mul_post
  then
    get_mul_forward_error prove_overflow info t1 t2 r
  else
    failwith "Unsupported symbol"

(* Generate error formulas recursively for a term `t` using basic floating point
   theorems as well as triangle inequality. This is recursive because if `t` is
   an approximation of a term `u` which itself is an approximation of a term
   `v`, we first compute a formula for the approximation of `v` by `u` and we
   combine it with the formula we already have of the approximation of `u` by
   `t` to get a formula relating `t` to `v`. *)
(* TODO: Avoid traversing the same term twice. *)
let rec get_error_fmlas prove_overflow info t :
    term_info Mterm.t * decl list list * (prsymbol * term) option =
  let apply = get_error_fmlas prove_overflow in
  let t_info = get_info info t in
  match t_info.ieee_post with
  | Some (ieee_post, t1, t2) -> (
    let info, l1, f1 = apply info t1 in
    let info, l2, f2 = apply info t2 in
    let l =
      match f1 with
      | Some (pr1, t1) -> [ Decl.create_prop_decl Paxiom pr1 t1 ]
      | None -> []
    in
    let l =
      match f2 with
      | Some (pr2, t2) -> l @ [ Decl.create_prop_decl Paxiom pr2 t2 ]
      | None -> l
    in
    let info, (pr3, t3), simplified =
      use_ieee_thms prove_overflow info ieee_post t1 t2 t
    in
    match simplified with
    | None ->
      let l = l @ [ Decl.create_prop_decl Pgoal pr3 t3 ] in
      (info, l1 @ l2 @ [ l ], Some (pr3, t3))
    (* We have a simplified version of t3 (eg. a formula with simplified error
       bounds). We assert it and prove it using t3. *)
    | Some (pr3', t3') ->
      let l = l @ [ Decl.create_prop_decl Pgoal pr3 t3 ] in
      let l' =
        [
          Decl.create_prop_decl Paxiom pr3 t3;
          Decl.create_prop_decl Pgoal pr3' t3';
        ]
      in
      (info, l1 @ l2 @ [ l ] @ [ l' ], Some (pr3', t3')))
  | None -> (
    match t_info.error with
    | None -> (info, [], None)
    | Some error ->
      let exact_t, rel_err, t', cst_err = error.no_underflow in
      if t_equal zero rel_err then
        (info, [], None)
      else
        (info, [], None))

(* The second part of the transformation looks for the floats that are in the
   goal. For each of float `f'`, it tries to compute a formula of the form |f' -
   f| <= A|f| + B where `f` is the real value approximated by `f'`. For this,
   forward error propagation is performed using theorems on the basic float
   operations as well as the triangle inequality with the data contained in
   `info`. For each new formula created, a proof tree is generated with the
   necessary steps to prove it. *)
let compute_errors env (info, goal) =
  let goal = Opt.get goal in
  let kind, pr, goal =
    match goal.d_node with
    | Dprop (kind, pr, f) when kind = Pgoal -> (kind, pr, f)
    | _ -> assert false
  in
  let floats = get_floats goal in
  let prove_overflow =
    match goal.t_node with
    | Tapp (ls, _) when is_ieee_pre ls -> true
    | _ -> false
  in
  let l, hyps =
    List.fold_left
      (fun (l, hyps) t ->
        let _, l', hyp = get_error_fmlas prove_overflow info t in
        match hyp with
        | Some (pr, t) -> (l @ l', create_prop_decl Paxiom pr t :: hyps)
        | None -> (l, hyps))
      ([], []) floats
  in
  let g = Decl.create_prop_decl Decl.Pgoal pr goal in
  let f pr goal = l @ [ List.rev (g :: hyps) ] in
  Trans.compose_l (Trans.goal_l f) (Trans.store (apply_theorems env info))

let get_term_for_info t1 =
  match t1.t_node with
  | Tapp (ls, [ t ]) when is_to_real_ls ls -> t
  | _ -> t1

(* Parse |t1 - t1'| <= t2 *)
let parse_and_add_error_fmla info t1 t1' t2 =
  let abs_err = (t1', zero, zero, t2) in
  let rec parse t =
    if t_equal t t1' then
      (abs_err, true)
    else
      match t.t_node with
      | Tapp (_ls, [ t' ]) when is_abs_ls _ls ->
        if t_equal t' t1' then
          ((t1', one, t, zero), true)
        else
          (* TODO: Look inside abs ? *)
          (abs_err, false)
      | Tapp (_ls, [ t3; t4 ]) when is_add_ls _ls ->
        let (a, factor, a', cst), _ = parse t3 in
        if t_equal factor zero then
          let (a, factor, a', cst), _ = parse t4 in
          if t_equal factor zero then
            (abs_err, false)
          else
            ((a, factor, a', cst ++. t3), false)
        else
          ((a, factor, a', cst ++. t4), false)
      | Tapp (_ls, [ t3; t4 ]) when is_sub_ls _ls ->
        let (a, factor, a', cst), _ = parse t3 in
        if t_equal factor zero then
          (abs_err, false)
        else
          ((a, factor, a', cst --. t4), false)
      | Tapp (_ls, [ t3; t4 ]) when is_mul_ls _ls ->
        let (a, factor, a', cst), is_factor = parse t3 in
        if t_equal factor zero then
          let (a, factor, a', cst), is_factor = parse t4 in
          if t_equal factor zero then
            (abs_err, false)
          else if is_factor then
            ((a, factor **. t3, a', cst), true)
          else
            ((a, factor, a', cst **. t4), false)
        else if is_factor then
          ((a, factor **. t4, a', cst), true)
        else
          ((a, factor, a', cst **. t4), false)
      | _ -> (abs_err, false)
  in
  let error_fmla, _ = parse t2 in
  let t1 = get_term_for_info t1 in
  add_error info t1 { no_underflow = error_fmla; underflow = [] }

let rec collect info f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = collect info f1 in
    collect info f2
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls ls -> (
    match t1.t_node with
    | Tapp (_ls, [ t ]) when is_abs_ls ls -> (
      match t.t_node with
      (* |to_real x| <= y *)
      | Tapp (_ls, [ t ]) when is_to_real_ls _ls -> add_ineq info t ls t2
      (* |x' - x| <= A *)
      | Tapp (_ls, [ t1'; t2' ]) when is_sub_ls _ls ->
        parse_and_add_error_fmla info t1' t2' t2
      | _ -> info)
    | _ -> info)
  (* Look for rel_error *)
  | Tapp (ls, [ t1; t2; t3; t4 ]) when ls_equal ls (Opt.get !symbols).fw_error
    ->
    let t1 = get_term_for_info t1 in
    add_error info t1 { no_underflow = (t2, t4, abs t3, zero); underflow = [] }
  | Tapp (ls, [ t1; t2; t3 ]) when is_ieee_post ls ->
    add_ieee_post info ls t3 t1 t2
  | _ -> info

(* We look for relevant axioms in the task, and we add corresponding
 * inequalities to `info`.
 * The formulas we look for have one of the following structures :
 * - |to_real(x)| <= A
 * - |x' - x| <= A
 * - rel_err x x' A : Specific annotation to specifying a relative error.
 * - *_post_ieee r x y : r is the result of a floating point computation
 *   involving x and y
 *)
let collect_info d (info, _) =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma ->
    (collect info f, None)
  | Dprop (kind, pr, f) when kind = Pgoal -> (info, Some d)
  | _ -> (info, None)

let init_symbols env =
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
  let usingle = Env.read_theory env [ "ufloat" ] "USingle" in
  let f s = ns_find_ls usingle.th_export [ s ] in
  let usingle_symbols =
    {
      ufloat_type = ns_find_ts usingle.th_export [ "usingle" ];
      to_real = f "to_real";
      uadd = f "uadd";
      usub = f "usub";
      umul = f "umul";
      udiv = f "udiv";
    }
  in
  let udouble = Env.read_theory env [ "ufloat" ] "UDouble" in
  let f s = ns_find_ls udouble.th_export [ s ] in
  let udouble_symbols =
    {
      ufloat_type = ns_find_ts udouble.th_export [ "udouble" ];
      to_real = f "to_real";
      uadd = f "uadd";
      usub = f "usub";
      umul = f "umul";
      udiv = f "udiv";
    }
  in
  let safe32 = Env.read_theory env [ "cfloat" ] "Safe32" in
  let f s = ns_find_ls safe32.th_export [ s ] in
  let single_symbols =
    {
      ieee_type = ns_find_ts safe32.th_export [ "t" ];
      to_real = f "to_real";
      add_post = f "safe32_add_post";
      sub_post = f "safe32_sub_post";
      mul_post = f "safe32_mul_post";
      div_post = f "safe32_div_post";
      add_pre = f "safe32_add_pre";
      sub_pre = f "safe32_sub_pre";
      mul_pre = f "safe32_mul_pre";
      div_pre = f "safe32_div_pre";
    }
  in
  let safe64 = Env.read_theory env [ "cfloat" ] "Safe64" in
  let f s = ns_find_ls safe64.th_export [ s ] in
  let double_symbols =
    {
      ieee_type = ns_find_ts safe64.th_export [ "t" ];
      to_real = f "to_real";
      add_post = f "safe64_add_post";
      sub_post = f "safe64_sub_post";
      mul_post = f "safe64_mul_post";
      div_post = f "safe64_div_post";
      add_pre = f "safe64_add_pre";
      sub_pre = f "safe64_sub_pre";
      mul_pre = f "safe64_mul_pre";
      div_pre = f "safe64_div_pre";
    }
  in
  let safe64_lemmas = Env.read_theory env [ "safe64_lemmas" ] "Safe64Lemmas" in
  let fw_error = ns_find_ls safe64_lemmas.th_export [ "fw_error" ] in
  symbols :=
    Some
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
        fw_error;
        usingle_symbols;
        udouble_symbols;
        single_symbols;
        double_symbols;
      }

let numeric env =
  init_symbols env;
  Trans.bind
    (Trans.fold_decl collect_info (Mterm.empty, None))
    (compute_errors env)

let () =
  Trans.register_env_transform_l "fw_error_propagation" numeric
    ~desc:"Apply forward error propagation"
