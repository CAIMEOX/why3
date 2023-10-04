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

open Strategy
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
  sum : lsymbol;
  sin : lsymbol;
  cos : lsymbol;
  exp : lsymbol;
  log : lsymbol;
  lt : lsymbol;
  lt_infix : lsymbol;
  le : lsymbol;
  le_infix : lsymbol;
  gt : lsymbol;
  gt_infix : lsymbol;
  ge : lsymbol;
  ge_infix : lsymbol;
  abs : lsymbol;
  (* fw_error : lsymbol; *)
  usingle_symbols : ufloat_symbols;
  udouble_symbols : ufloat_symbols;
  single_symbols : ieee_symbols;
  double_symbols : ieee_symbols;
  printer : ident_printer;
}

let symbols = ref None
let ( !! ) s = Opt.get !s

(* Forward error associated to a real term t, eg. (x, rel, x', cst) stands for
   |t - x| <= rel * x' + cst *)
type error_fmla = term * term * term * term

(* This type corresponds to the numeric info we have on a real of float term *)
type term_info = {
  (* "(<=, y)" means "|to_real x| <= y" *)
  ineqs : (lsymbol * term) list;
  error : error_fmla option;
  (* If x has an ieee_post, it means it is the result of an arithmetic FP
     operation *)
  ieee_post : (lsymbol * term * term) option;
}

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
let is_one t = t_equal one t

let abs t =
  match t.t_node with
  (* Don't add an abs symbol on top of another *)
  | Tapp (ls, [ _ ]) when ls_equal !!symbols.abs ls -> t
  | _ -> fs_app !!symbols.abs [ t ] ty_real

(* TODO: Add ge and gt later *)
let is_ineq_ls ls =
  let symbols = !!symbols in
  ls_equal ls symbols.lt || ls_equal ls symbols.le
  || ls_equal ls symbols.lt_infix
  || ls_equal ls symbols.le_infix
(* || ls_equal ls symbols.gt || ls_equal ls symbols.ge *)

let is_add_ls ls = ls_equal ls !!symbols.add || ls_equal ls !!symbols.add_infix
let is_sub_ls ls = ls_equal ls !!symbols.sub || ls_equal ls !!symbols.sub_infix
let is_mul_ls ls = ls_equal ls !!symbols.mul || ls_equal ls !!symbols.mul_infix

let is_minus_ls ls =
  ls_equal ls !!symbols.minus || ls_equal ls !!symbols.minus_infix

let is_abs_ls ls = ls_equal ls !!symbols.abs

let is_to_real_ls ls =
  ls_equal ls !!symbols.single_symbols.to_real
  || ls_equal ls !!symbols.double_symbols.to_real

let is_ieee_post ls =
  let symbols = !!symbols in
  ls_equal ls symbols.single_symbols.add_post
  || ls_equal ls symbols.single_symbols.sub_post
  || ls_equal ls symbols.single_symbols.mul_post
  || ls_equal ls symbols.single_symbols.div_post
  || ls_equal ls symbols.double_symbols.add_post
  || ls_equal ls symbols.double_symbols.sub_post
  || ls_equal ls symbols.double_symbols.mul_post
  || ls_equal ls symbols.double_symbols.div_post

let is_ieee_pre ls =
  let symbols = !!symbols in
  ls_equal ls symbols.single_symbols.add_pre
  || ls_equal ls symbols.single_symbols.sub_pre
  || ls_equal ls symbols.single_symbols.mul_pre
  || ls_equal ls symbols.single_symbols.div_pre
  || ls_equal ls symbols.double_symbols.add_pre
  || ls_equal ls symbols.double_symbols.sub_pre
  || ls_equal ls symbols.double_symbols.mul_pre
  || ls_equal ls symbols.double_symbols.div_pre

let add t1 t2 = fs_app !!symbols.add [ t1; t2 ] ty_real

let add_simp t1 t2 =
  if is_zero t1 then
    t2
  else if is_zero t2 then
    t1
  else
    add t1 t2

let sub t1 t2 = fs_app !!symbols.sub [ t1; t2 ] ty_real

let sub_simp t1 t2 =
  if is_zero t1 then
    fs_app !!symbols.minus [ t2 ] ty_real
  else if is_zero t2 then
    t1
  else
    sub t1 t2

let mul t1 t2 = fs_app !!symbols.mul [ t1; t2 ] ty_real

let mul_simp t1 t2 =
  if is_zero t1 || is_zero t2 then
    zero
  else if is_one t1 then
    t2
  else if is_one t2 then
    t1
  else
    match (t1.t_node, t2.t_node) with
    | Tapp (ls1, [ t1 ]), Tapp (ls2, [ t2 ]) when is_abs_ls ls1 && is_abs_ls ls2
      ->
      abs (mul t1 t2)
    | _ -> mul t1 t2

let div t1 t2 = fs_app !!symbols.div [ t1; t2 ] ty_real

let div_simp t1 t2 =
  if is_zero t1 then
    zero
  else if is_one t2 then
    t1
  else
    div t1 t2

let minus t = fs_app !!symbols.minus [ t ] ty_real

let minus_simp t =
  match t.t_node with
  | Tapp (ls, [ t' ]) when is_minus_ls ls -> t'
  | _ -> minus t

let ( +. ) x y = add x y
let ( -. ) x y = sub x y
let ( *. ) x y = mul x y
let ( /. ) x y = div x y
let ( ++. ) x y = add_simp x y
let ( --. ) x y = sub_simp x y
let ( **. ) x y = mul_simp x y
let ( //. ) x y = div_simp x y
let ( <=. ) x y = ps_app !!symbols.le [ x; y ]
let ( <. ) x y = ps_app !!symbols.lt [ x; y ]

let is_ty_float ty =
  match ty.ty_node with
  | Tyapp (v, []) ->
    if
      ts_equal v !!symbols.single_symbols.ieee_type
      || ts_equal v !!symbols.double_symbols.ieee_type
      || ts_equal v !!symbols.usingle_symbols.ufloat_type
      || ts_equal v !!symbols.udouble_symbols.ufloat_type
    then
      true
    else
      false
  | _ -> false

let eps ieee_type =
  let value =
    if ts_equal ieee_type !!symbols.single_symbols.ieee_type then
      "-24"
    else if ts_equal ieee_type !!symbols.double_symbols.ieee_type then
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
  let value =
    if ts_equal ieee_type !!symbols.single_symbols.ieee_type then
      "-150"
    else if ts_equal ieee_type !!symbols.double_symbols.ieee_type then
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
  let to_real =
    if ts_equal ieee_type !!symbols.single_symbols.ieee_type then
      !!symbols.single_symbols.to_real
    else if ts_equal ieee_type !!symbols.double_symbols.ieee_type then
      !!symbols.double_symbols.to_real
    else
      failwith (Format.asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  fs_app to_real [ t ] ty_real

(* Merging the underflows means that if we have several error bounds (eg. one in
   no_underflow and at least one in underflow) we add all underflow errors as
   cst error in no_underflow, effectively keeping only one error bound. This is
   done when we want to use the bound error of t to compute a new bound for
   something else than multiplication *)
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
  let t =
    match t.t_node with
    | Tapp (ls, [ t ]) when is_to_real_ls ls -> t
    | _ -> t
  in
  (* Format.printf "Add error on %a@." Pretty.print_term t; *)
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
    | Tyvar _ -> assert false
    | Tyapp (ts, []) -> ts
    | _ -> assert false)

let rec get_floats t =
  let l =
    match t.t_ty with
    | Some ty when is_ty_float ty -> [ t ]
    | _ -> []
  in
  match t.t_node with
  | Tapp (_, tl) -> List.fold_left (fun l t -> l @ get_floats t) l tl
  | _ -> l

let rec print_term fmt t =
  let id_unique = id_unique !!symbols.printer in
  match t.t_node with
  | Tvar v -> Format.fprintf fmt "%s" (id_unique v.vs_name)
  | Tapp (ls, []) -> Format.fprintf fmt "%s" (id_unique ls.ls_name)
  | Tapp (ls, tl) -> (
    let s = id_unique ls.ls_name in
    match (Ident.sn_decode s, tl) with
    | Ident.SNinfix s, [ t1; t2 ] ->
      Format.fprintf fmt "((%a) %s (%a))" print_term t1 s print_term t2
    | Ident.SNget s, [ t1; t2 ] ->
      Format.fprintf fmt "%a@,[%a]%s" print_term t1 print_term t2 s
    | Ident.SNupdate s, [ t1; t2; t3 ] ->
      Format.fprintf fmt "%a@,[%a <-@ %a]%s" print_term t1 print_term t2
        print_term t3 s
    | Ident.SNprefix s, [ t ] -> Format.fprintf fmt "%s %a@." s print_term t
    | Ident.SNword s, [ t ] when Sattr.mem is_field_id_attr ls.ls_name.id_attrs
      ->
      Format.fprintf fmt "%a.%s" print_term t s
    | Ident.SNword s, tl ->
      Format.fprintf fmt "%s@ (%a)" s (Pp.print_list Pp.space print_term) tl
    (* TODO: Other applications *)
    | _ ->
      Format.fprintf fmt "(%s %a)" (id_unique ls.ls_name)
        (Format.pp_print_list ~pp_sep:Pp.space print_term)
        tl)
  | _ -> Pretty.print_term fmt t

let get_terms_names tlist =
  List.fold_left
    (fun s t ->
      let s' = Format.asprintf "%a" print_term t in
      if s = "" then
        s'
      else
        s ^ "," ^ s')
    "" tlist

let apply_args f t t_info =
  let to_real = to_real (get_ts t) in
  match t_info.error with
  | None -> f t (to_real t) zero (abs (to_real t)) zero
  | Some (exact_t, rel_err, t', cst_err) ->
    if is_zero rel_err then
      assert false
    else
      f t exact_t rel_err t' cst_err

(* Generates the formula for the forward error of r = x .* y. 2 formulas are
   created, one that matches the multiplication theorem and one with a bit of
   simplification. *)
let mul_forward_error prove_overflow info x y r s1 s2 =
  if prove_overflow then
    assert false
  else
    let ts = get_ts r in
    let eps = eps ts in
    let eta = eta ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x *. to_real y)) in
      let right = (eps *. abs (to_real x *. to_real y)) +. eta in
      let info =
        add_error info r
          (to_real x *. to_real y, eps, abs (to_real x *. to_real y), eta)
      in
      (info, Some (left <=. right), Sdo_nothing)
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
        (* let rec extract_eta t = *)
        (*   if t_equal eta t then *)
        (*     match t.t_node with *)
        (*     | Tapp (ls, [ t1; t2 ]) when is_mul_ls ls -> assert false *)
        (*     | _ -> assert false *)
        (* in *)
        (* let _ = extract_eta t2_cst in *)
        let cst_err' =
          (((one ++. eps) **. (t2_cst ++. (t2_cst **. t1_factor))) **. t1')
          ++. (((one ++. eps) **. (t1_cst ++. (t1_cst **. t2_factor))) **. t2')
          ++. ((one ++. eps) **. t1_cst **. t2_cst)
          ++. eta
        in
        let left = abs (to_real r -. (exact_t1 *. exact_t2)) in
        let right = (rel_err *. (t1' *. t2')) +. cst_err in
        let right' = (rel_err' **. t1' **. t2') ++. cst_err' in
        let info =
          add_error info r (exact_t1 *. exact_t2, rel_err', t1' *. t2', cst_err')
        in
        let args = get_terms_names [ x; y ] in
        let s =
          Sapply_trans
            ( "apply",
              [ "mul_combine"; "with"; args ],
              [
                Sdo_nothing;
                s1;
                s2;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
              ] )
        in
        if t_equal right right' then
          (info, Some (left <=. right), s)
        else
          ( info,
            Some (left <=. right'),
            Sapply_trans
              ( "assert",
                [ Format.asprintf "%a" print_term (left <=. right) ],
                [ s ] ) )
      in
      let combine_errors_with_multiplication =
        apply_args combine_errors_with_multiplication x x_info
      in
      let combine_errors_with_multiplication =
        apply_args combine_errors_with_multiplication y y_info
      in
      combine_errors_with_multiplication r

(* Generates the formula for the forward error of r = x .- y *)
let sub_forward_error prove_overflow info x y r s1 s2 =
  if prove_overflow then
    assert false
  else
    let ts = get_ts r in
    let eps = eps ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x -. to_real y)) in
      let right = eps *. abs (to_real x +. to_real y) in
      let info =
        add_error info r
          (to_real x -. to_real y, eps, abs (to_real x -. to_real y), zero)
      in
      (info, Some (left <=. right), Sdo_nothing)
    | _ ->
      let combine_errors_with_substraction _t1 exact_t1 t1_factor t1' t1_cst _t2
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
          add_error info r (exact_t1 -. exact_t2, rel_err', t1' +. t2', cst_err')
        in
        let args = get_terms_names [ x; y ] in
        let s =
          Sapply_trans
            ( "apply",
              [ "add_combine"; "with"; args ],
              [
                Sdo_nothing;
                s1;
                s2;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
              ] )
        in
        if t_equal total_err total_err' then
          (info, Some (left <=. total_err), s)
        else
          ( info,
            Some (left <=. total_err'),
            Sapply_trans
              ( "assert",
                [ Format.asprintf "%a" print_term (left <=. total_err) ],
                [ s ] ) )
      in
      let combine_errors_with_substraction =
        apply_args combine_errors_with_substraction x x_info
      in
      let combine_errors_with_substraction =
        apply_args combine_errors_with_substraction y y_info
      in
      combine_errors_with_substraction r

(* Generates the formula for the forward error of r = x .- y *)
let add_forward_error prove_overflow info x y r s1 s2 =
  if prove_overflow then
    assert false
  (* apply_addition_thm_for_overflow symbols info f x y r *)
  else
    let ts = get_ts r in
    let eps = eps ts in
    let to_real = to_real ts in
    let x_info = get_info info x in
    let y_info = get_info info y in
    match (x_info.error, y_info.error) with
    | None, None ->
      let left = abs (to_real r -. (to_real x +. to_real y)) in
      let right = eps *. abs (to_real x +. to_real y) in
      let info =
        add_error info r
          (to_real x +. to_real y, eps, abs (to_real x +. to_real y), zero)
      in
      (info, Some (left <=. right), Sdo_nothing)
    | _ ->
      let combine_errors_with_addition _t1 exact_t1 t1_factor t1' t1_cst _t2
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
          add_error info r (exact_t1 +. exact_t2, rel_err', t1' +. t2', cst_err')
        in
        let args = get_terms_names [ x; y ] in
        let s =
          Sapply_trans
            ( "apply",
              [ "add_combine"; "with"; args ],
              [
                Sdo_nothing;
                s1;
                s2;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
                Sdo_nothing;
              ] )
        in
        if t_equal total_err total_err' then
          (info, Some (left <=. total_err), s)
        else
          ( info,
            Some (left <=. total_err'),
            Sapply_trans
              ( "assert",
                [ Format.asprintf "%a" print_term (left <=. total_err) ],
                [ s ] ) )
      in
      let combine_errors_with_addition =
        apply_args combine_errors_with_addition x x_info
      in
      let combine_errors_with_addition =
        apply_args combine_errors_with_addition y y_info
      in
      combine_errors_with_addition r

(* r is a result of FP arithmetic operation involving t1 and t2 *)
(* Compute new inequalities on r based on what we know on t1 and t2 *)
let use_ieee_thms prove_overflow info ieee_symbol t1 t2 r s1 s2 :
    term_info Mterm.t * term option * strat =
  let symbols = Opt.get !symbols in
  if
    ls_equal ieee_symbol symbols.single_symbols.add_post
    || ls_equal ieee_symbol symbols.double_symbols.add_post
  then
    add_forward_error prove_overflow info t1 t2 r s1 s2
  else if
    ls_equal ieee_symbol symbols.single_symbols.sub_post
    || ls_equal ieee_symbol symbols.double_symbols.sub_post
  then
    sub_forward_error prove_overflow info t1 t2 r s1 s2
  else if
    ls_equal ieee_symbol symbols.single_symbols.mul_post
    || ls_equal ieee_symbol symbols.double_symbols.mul_post
  then
    mul_forward_error prove_overflow info t1 t2 r s1 s2
  else
    failwith "Unsupported symbol"

let get_known_fn t =
  match t.t_node with
  | Tapp (ls, args)
    when ls_equal ls !!symbols.sin || ls_equal ls !!symbols.cos
         || ls_equal ls !!symbols.sum || ls_equal ls !!symbols.log
         || ls_equal ls !!symbols.exp ->
    let args =
      List.map
        (fun arg ->
          match arg.t_node with
          | Tapp (ls, [ t ]) when is_to_real_ls ls -> t
          | _ -> arg)
        args
    in
    Some (ls, args)
  | _ -> None

let apply_sum_thm info t exact_t args strats =
  let sum_fn = List.hd args in
  match (get_info info sum_fn).error with
  (* Does this happen ? We always use induction here, so addition theorem is
     applied *)
  | Some (exact_arg, rel_err, arg', cst_err) -> failwith "TODO : Sum with error"
  | None -> (info, None, List.hd strats)

let apply_exp_thm info t exact_t args strats =
  let arg = List.hd args in
  match (get_info info arg).error with
  | Some (exact_arg, rel_err, arg', cst_err) -> failwith "TODO : Exp with error"
  | None -> (info, None, List.hd strats)

let apply_log_thm info t exact_t args strats =
  let arg = List.hd args in
  match (get_info info arg).error with
  | Some (exact_arg, rel_err, arg', cst_err) ->
    let to_real = to_real (get_ts t) in
    let exact_fn = fs_app !!symbols.log [ exact_arg ] ty_real in
    let left = abs (exact_t -. exact_fn) in
    (* TODO: Log error when we have a relative error but no cst error *)
    let right =
      exact_fn
      ++. minus_simp
            (fs_app !!symbols.log
               [ one --. ((rel_err **. arg') ++. cst_err) ]
               ty_real)
    in
    (* |log (x') - log(x)| <= -log(1-err) *)
    let f = left <=. right in
    (* TODO: apply log thm ? *)
    let s =
      Sapply_trans ("assert", [ Format.asprintf "%a" print_term f ], strats)
    in
    let left = abs (to_real t -. exact_fn) in
    let _, rel_err, t', cst_err = Opt.get (get_info info t).error in
    let cst_err = right **. (one ++. rel_err) in
    let right = (rel_err **. t') ++. cst_err in
    let info = add_error info t (exact_fn, rel_err, t', cst_err) in
    (info, Some (left <=. right), s)
  | None -> (info, None, List.hd strats)

(* t the application of a sin/cos approximation to arg.
 * exact_t is the application of the real sin/cos fn to arg.
 * fn is the real function, eg. sin or cos.
 * If arg is an approximation of a real value, then we combine the error of t
   with the error of arg.
 *)
let apply_sin_cos_thm info t exact_t fn arg strats =
  match (get_info info arg).error with
  | Some (exact_arg, arg_rel_err, arg', arg_cst_err) ->
    let to_real = to_real (get_ts t) in
    let exact_fn = fs_app fn [ exact_arg ] ty_real in
    let s = Sapply_trans ("apply", [ "sin_error_propagation" ], strats) in
    let _, fn_rel_err, t', fn_cst_err = Opt.get (get_info info t).error in
    (* TODO: t' is not always equal to abs exact_fn, manage that *)
    let cst_err =
      (((arg_rel_err *. arg') +. arg_cst_err) *. (one +. fn_rel_err))
      +. fn_cst_err
    in
    let cst_err_simp =
      (((arg_rel_err **. arg') ++. arg_cst_err) **. (one ++. fn_rel_err))
      ++. fn_cst_err
    in
    let total_err = (abs exact_fn *. fn_rel_err) +. cst_err in
    let total_err_simp = (abs exact_fn **. fn_rel_err) ++. cst_err_simp in
    let info =
      add_error info t (exact_fn, fn_rel_err, abs exact_fn, cst_err_simp)
    in
    (* TODO: We need to assert the bound on (fun y -> sin' y) @ x instead of
       sin' x to match the form of the sin lemma applied earlier. Maybe there is
       a better solution we can find here *)
    let t_func_app =
      match t.t_node with
      | Tapp (ls, [ arg ]) ->
        t_app fs_func_app
          [
            t_app_partial ls [] [ Opt.get t.t_ty ] (Some (Opt.get t.t_ty)); arg;
          ]
          t.t_ty
      | _ -> assert false
    in
    let left = abs (to_real t_func_app -. exact_fn) in
    let s =
      Sapply_trans
        ( "assert",
          [ Format.asprintf "%a" print_term (left <=. total_err) ],
          [ s ] )
    in
    let left = abs (to_real t -. exact_fn) in
    if t_equal total_err total_err_simp then
      (info, Some (left <=. total_err), s)
    else
      ( info,
        Some (left <=. total_err_simp),
        Sapply_trans
          ( "assert",
            [ Format.asprintf "%a" print_term (left <=. total_err) ],
            [ s ] ) )
  | None -> (info, None, List.hd strats)

let use_known_thm info t exact_t fn args strats =
  if ls_equal fn !!symbols.cos || ls_equal fn !!symbols.sin then
    apply_sin_cos_thm info t exact_t fn (List.hd args) strats
  else if ls_equal fn !!symbols.sum then
    apply_sum_thm info t exact_t args strats
  else if ls_equal fn !!symbols.exp then
    apply_exp_thm info t exact_t args strats
  else if ls_equal fn !!symbols.log then
    apply_log_thm info t exact_t args strats
  else
    assert false

(* Generate error formulas recursively for a term `t` using basic floating point
   theorems as well as triangle inequality. This is recursive because if `t` is
   an approximation of a term `u` which itself is an approximation of a term
   `v`, we first compute a formula for the approximation of `v` by `u` and we
   combine it with the formula we already have of the approximation of `u` by
   `t` to get a formula relating `t` to `v`. *)
(* TODO: Avoid traversing the same term twice. *)
let rec get_error_fmlas prove_overflow info t :
    term_info Mterm.t * term option * strat =
  let apply = get_error_fmlas prove_overflow in
  let t_info = get_info info t in
  (* TODO: Write this function if possible instead of passing s1 and s2 *)
  (* let combine (info,strat) t = *)
  (*   let info, f, s = apply info t in *)
  (*   let s = *)
  (*     match f with *)
  (*     | None -> s *)
  (*     | Some f -> *)
  (* Sapply_trans ("assert", [ Format.asprintf "%a" print_term f ], [ s ]) in *)
  match t_info.ieee_post with
  | Some (ieee_post, t1, t2) ->
    let info, f1, s1 = apply info t1 in
    let info, f2, s2 = apply info t2 in
    (* TODO: Maybe those asserts are redundant, try to remove them *)
    let s1 =
      match f1 with
      | None -> s1
      | Some f1 ->
        Sapply_trans ("assert", [ Format.asprintf "%a" print_term f1 ], [ s1 ])
    in
    let s2 =
      match f2 with
      | None -> s2
      | Some f2 ->
        Sapply_trans ("assert", [ Format.asprintf "%a" print_term f2 ], [ s2 ])
    in
    use_ieee_thms prove_overflow info ieee_post t1 t2 t s1 s2
  | None -> (
    match t_info.error with
    | Some (exact_t, rel_err, t', cst_err) -> (
      (* TODO: Manage the recognition of functions during parsing (collect
         function) ? *)
      match get_known_fn exact_t with
      | Some (fn, args) ->
        let info, l =
          List.fold_left
            (fun (info, l) t ->
              let info, f, s = apply info t in
              let s =
                match f with
                | None -> s
                | Some f ->
                  Sapply_trans
                    ("assert", [ Format.asprintf "%a" print_term f ], [ s ])
              in
              (info, s :: l))
            (info, []) args
        in
        use_known_thm info t exact_t fn args (List.rev l)
      | None -> (info, None, Sdo_nothing))
    | None -> (info, None, Sdo_nothing))

(* Parse |t1 - t1'| <= t2 *)
let parse_and_add_error_fmla info t1 t1' t2 =
  let is_sum, _f, i, j =
    match t1'.t_node with
    | Tapp (ls, [ f; i; j ]) when ls_equal ls !!symbols.sum ->
      (true, Some f, Some i, Some j)
    | _ -> (false, None, None, None)
  in
  let abs_err = (t1', zero, zero, t2) in
  let rec parse t =
    if t_equal t t1' then
      (abs_err, true)
    else
      match t.t_node with
      | Tapp (_ls, [ t' ]) when is_abs_ls _ls -> (
        if t_equal t' t1' then
          ((t1', one, t, zero), true)
        else
          (* TODO: Rewrite this better, also compare f and f' *)
          match t'.t_node with
          | Tapp (ls, [ _f'; i'; j' ])
            when ls_equal ls !!symbols.sum && is_sum
                 && t_equal i' (Opt.get i)
                 && t_equal j' (Opt.get j) ->
            ((t1', one, t, zero), true)
          | _ -> (abs_err, false))
      (* TODO: We should also compare f and f', but we would need to inline them
         before *)
      | Tapp (ls, [ _f'; i'; j' ])
        when ls_equal ls !!symbols.sum && is_sum
             && t_equal i' (Opt.get i)
             && t_equal j' (Opt.get j) ->
        ((t1', one, t, zero), true)
      | Tapp (_ls, [ t3; t4 ]) when is_add_ls _ls ->
        let (a, factor, a', cst), _ = parse t3 in
        if is_zero factor then
          let (a, factor, a', cst), _ = parse t4 in
          if is_zero factor then
            (abs_err, false)
          else
            ((a, factor, a', cst ++. t3), false)
        else
          ((a, factor, a', cst ++. t4), false)
      | Tapp (_ls, [ t3; t4 ]) when is_sub_ls _ls ->
        let (a, factor, a', cst), _ = parse t3 in
        if is_zero factor then
          (abs_err, false)
        else
          ((a, factor, a', cst --. t4), false)
      | Tapp (_ls, [ t3; t4 ]) when is_mul_ls _ls ->
        let (a, factor, a', cst), is_factor = parse t3 in
        if is_zero factor then
          let (a, factor, a', cst), is_factor = parse t4 in
          if is_zero factor then
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
  add_error info t1 error_fmla

let rec collect info f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = collect info f1 in
    collect info f2
  | Tapp (ls, [ t1; t2 ]) when is_ineq_ls ls -> (
    match t1.t_node with
    | Tapp (ls, [ t ]) when is_abs_ls ls -> (
      match t.t_node with
      (* |to_real x| <= y *)
      | Tapp (ls, [ t ]) when is_to_real_ls ls -> add_ineq info t ls t2
      (* |x' - x| <= A *)
      | Tapp (ls, [ t1'; t2' ]) when is_sub_ls ls ->
        Format.printf "Add error on %a ___ %a@." Pretty.print_term t1'
          Pretty.print_term f;
        parse_and_add_error_fmla info t1' t2' t2
      | _ -> info)
    | _ -> info)
  (* Look for rel_error *)
  (* | Tapp (ls, [ t1; t2; t3; t4 ]) when ls_equal ls !!symbols.fw_error -> *)
  (*   let t1 = get_term_for_info t1 in *)
  (*   add_error info t1 (t2, t4, abs t3, zero) *)
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
let collect_info info d =
  match d.d_node with
  | Dprop (kind, _, f) when kind = Paxiom || kind = Plemma -> collect info f
  | Dprop (kind, _, _) when kind = Pgoal -> info
  | _ -> info

let init = ref false

(* TODO: Change naming_table also when init is true *)
let init_symbols env printer =
  if !init = false then
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
    let minus_infix =
      ns_find_ls real_infix.th_export [ Ident.op_prefix "-." ]
    in
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
    (* let safe64_lemmas = *)
    (*   Env.read_theory env [ "safe64_lemmas" ] "Safe64Lemmas" *)
    (* in *)
    (* let fw_error = ns_find_ls safe64_lemmas.th_export [ "fw_error" ] in *)
    let sum_th = Env.read_theory env [ "creal" ] "SumReal" in
    let sum = ns_find_ls sum_th.th_export [ "sum" ] in
    let trigo = Env.read_theory env [ "real" ] "Trigonometry" in
    let sin = ns_find_ls trigo.th_export [ "sin" ] in
    let cos = ns_find_ls trigo.th_export [ "cos" ] in
    let exp_log_th = Env.read_theory env [ "real" ] "ExpLog" in
    let exp = ns_find_ls exp_log_th.th_export [ "exp" ] in
    let log = ns_find_ls exp_log_th.th_export [ "log" ] in
    symbols :=
      Some
        {
          add;
          sub;
          mul;
          div;
          minus;
          sum;
          sin;
          cos;
          exp;
          log;
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
          (* fw_error; *)
          usingle_symbols;
          udouble_symbols;
          single_symbols;
          double_symbols;
          printer;
        }

let f env task =
  let naming_table = Args_wrapper.build_naming_tables task in
  init_symbols env naming_table.printer;
  let goal = task_goal_fmla task in
  let floats = get_floats goal in
  let prove_overflow =
    match goal.t_node with
    | Tapp (ls, _) when is_ieee_pre ls -> true
    | _ -> false
  in
  let info = List.fold_left collect_info Mterm.empty (task_decls task) in
  (* For each float `f'` of the goal, we try to compute a formula of the form
     |f' - f| <= A|f| + B where `f` is the real value which is approximated by
     the float `f'`. For this, forward error propagation is performed using
     theorems on the basic float operations as well as the triangle inequality
     with the data contained in `info`. For each new formula created, a proof
     tree is generated with the necessary steps to prove it. *)
  let f, strats =
    List.fold_left
      (fun (f, l) t ->
        match get_error_fmlas prove_overflow info t with
        | _, None, _ -> (f, l)
        | _, Some f', s -> (t_and_simp f f', s :: l))
      (t_true, []) floats
  in
  if List.length strats = 0 then
    Sdo_nothing
  else if List.length strats = 1 then
    Sapply_trans ("assert", [ Format.asprintf "%a" print_term f ], strats)
  else
    let s = Sapply_trans ("split_vc", [], List.rev strats) in
    Sapply_trans ("assert", [ Format.asprintf "%a" print_term f ], [ s ])

let () =
  register_strat "numeric" f
    ~desc:"Compute@ forward@ error@ of@ float@ computations."
