(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Ptree

type pparam =
  | PPt of ident (* < 'a > *)
  | PPv of ident * pty (* x *)
  | PPr of ident * pty (* &r *)
  | PPc of ident * ident list * pparam list (* x [x...] p... *)

type pexpr = {
  pexpr_desc : pexpr_desc;
  pexpr_loc  : Loc.position;
}

and pexpr_desc =
  | PEsym of ident (* x *)
  | PEapp of pexpr * pargument (* e <ty>... t... | e... *)
  | PElam of pparam list * pexpr (* fun pl -> e *)
  | PEdef of pexpr * bool * pdefn list (* e / rec? h p = e and ... *)
  | PEset of pexpr * (ident * term * pty) list (* assign ... *)
  | PEcut of term * pexpr (* { t } e *)
  | PEbox of pexpr (* ! e *)
  | PEwox of pexpr (* ? e *)
  | PEany (* any *)

and pargument =
  | PAt of pty (* < ty > *)
  | PAv of term (* t *)
  | PAr of ident (* &r *)
  | PAc of pexpr (* (e) *)

and pdefn = {
  pdefn_desc   : pdefn_desc;
  pdefn_loc    : Loc.position;
}

and pdefn_desc = {
  pdefn_name   : ident;
  pdefn_writes : ident list;
  pdefn_params : pparam list;
  pdefn_body   : pexpr;
}

open Format

let rec pp_param fmt = function
  | PPt i -> fprintf fmt "<%s>" i.id_str
  | PPv (i, _) -> fprintf fmt "%s" i.id_str
  | PPr (i, _) -> fprintf fmt "&%s" i.id_str
  | PPc (i, w, pl) -> fprintf fmt "(%s [%a] %a)" i.id_str pp_writes w pp_params pl

and pp_writes fmt w =
  let pp_sep fmt () = fprintf fmt " " in
  let pp_v fmt s = fprintf fmt "%s" s.id_str in
  pp_print_list ~pp_sep pp_v fmt w

and pp_params fmt pl =
  let pp_sep fmt () = fprintf fmt " " in
  pp_print_list ~pp_sep pp_param fmt pl

let pp_set fmt sl =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt (s, _, _) = fprintf fmt "/ &%s = {} " s.id_str in
  pp_print_list ~pp_sep pp_v fmt sl

let rec pp_expr fmt e = match e.pexpr_desc with
  | PEsym i -> fprintf fmt "%s" i.id_str
  | PEapp (e, arg) -> fprintf fmt "%a %a" pp_expr e pp_arg arg
  | PElam (p, e) -> fprintf fmt "(fun @[%a@] → @[%a@])" pp_params p pp_expr e
  | PEdef (e, _, l) -> fprintf fmt "%a@\n%a" pp_expr e pp_defs l
  | PEset (e, l) -> fprintf fmt "%a@\n%a" pp_expr e pp_set l
  | PEcut (t, e) -> fprintf fmt "{ϕ} @[%a@]" pp_expr e
  | PEbox e -> fprintf fmt "↑ @[%a@]" pp_expr e
  | PEwox e -> fprintf fmt "↓ @[%a@]" pp_expr e
  | PEany -> fprintf fmt "any"

and pp_arg fmt = function
  | PAt _pty -> fprintf fmt "<>"
  | PAv _term -> fprintf fmt "{}"
  | PAr i -> fprintf fmt "&%s" i.id_str
  | PAc e ->
      match e.pexpr_desc with
      | PEsym i -> fprintf fmt "%s" i.id_str
      | _ -> fprintf fmt "(%a)" pp_expr e

and pp_def fmt def =
  let def = def.pdefn_desc in
  fprintf fmt "%s [%a] %a =@\n  @[%a@]"
    def.pdefn_name.id_str
    pp_writes def.pdefn_writes
    pp_params def.pdefn_params
    pp_expr def.pdefn_body

and pp_defs fmt l =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt d = fprintf fmt "/ %a" pp_def d in
  pp_print_list ~pp_sep pp_v fmt l
