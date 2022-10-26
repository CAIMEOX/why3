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

open Why3
open Ptree

type ty =
  | Tyvar   of ident
  | Tyapp   of qualid * ty list
  | Tyarrow of ty * ty
  | Tyscope of qualid * ty
  | Typaren of ty

type binder = {
  b_ident : ident;
  b_ghost : bool;
  b_null  : bool;
  b_mut   : bool;
}

type pat = {
  pat_desc  : pat_desc;
  pat_loc   : Loc.position;
}

and pat_desc =
  | Pwild
  | Pvar   of binder
  | Papp   of qualid * pat list
  | Pas    of pat * binder
  | Por    of pat * pat
  | Pcast  of pat * ty
  | Pscope of qualid * pat
  | Pparen of pat

type outcome = pat (* ident * pat list *)
(* DISCUSS: qualified outcome names? Outcomes have no global declarations
   or fixed type signatures: they rather act like OCaml labeled arguments.
   However, we can't mix two functions with (Out int) and (Out bool) from
   two libraries in the same block of code: labeled arguments do not have
   this issue. Is binding-by-name across function definitions a bad idea? *)

type expr = {
  expr_desc   : expr_desc;
  expr_loc    : Loc.position;
}

and expr_desc =
  | Elet of let_defn list * expr
  | Efun of fun_defn list * expr
  | Erec of fun_defn list * expr
  | Ewith of expr * with_defn list
  | Eif of expr * expr * expr
  | Ewhile of expr * expr
  | Ecall of qualid * expr list
  | Eassign of expr * expr
  | Eseq of expr * expr
  | Econst of Constant.constant
  | Eident of qualid
  | Escope of qualid * expr
  | Echain of expr * ident * expr
  | Eand of expr * expr
  | Eor of expr * expr
  | Enot of expr
  | Etrue
  | Efalse
  | Eparen of expr
  | Eattr of attr * expr

and let_defn  = outcome * expr (* outcome <- expr *)
and with_defn = outcome * expr (* outcome -> expr *)
and fun_defn  = ident * pat list * outcome list * expr (* TODO: spec *)

type decl = {
  decl_desc   : decl_desc;
  decl_loc    : Loc.position;
}

and decl_desc =
  | Dlet of let_defn list
  | Dfun of fun_defn list
  | Drec of fun_defn list

(* parsing tree pretty-printing *)

open Format

let rec print_decl fmt d = match d.decl_desc with
  | Dlet [] | Dfun [] | Drec [] -> assert false
  | Dlet (ld::ldl) ->
      fprintf fmt "@[<hv 0>let %a%a@]@\n"
        print_ld ld (fun fmt ldl -> List.iter (fun ld ->
          fprintf fmt "@\nand %a" print_ld ld) ldl) ldl
  | Dfun (fd::fdl) ->
      fprintf fmt "@[<hv 0>fun %a%a in@]@\n"
        print_fd fd (fun fmt fdl -> List.iter (fun fd ->
          fprintf fmt "@\nand %a" print_fd fd) fdl) fdl
  | Drec (fd::fdl) ->
      fprintf fmt "@[<hv 0>rec %a%a in@]@\n"
        print_fd fd (fun fmt fdl -> List.iter (fun fd ->
          fprintf fmt "@\nand %a" print_fd fd) fdl) fdl

and print_expr fmt e = match e.expr_desc with
  | Elet ([], _) | Efun ([], _) | Erec ([], _) -> assert false
  | Elet (ld::ldl, e) ->
      fprintf fmt "@[@[<hv 0>let %a%a in@]@\n%a endin@]"
        print_ld ld (fun fmt ldl -> List.iter (fun ld ->
          fprintf fmt "@\nand %a" print_ld ld) ldl) ldl print_expr e
  | Efun (fd::fdl, e) ->
      fprintf fmt "@[@[<hv 0>fun %a%a in@]@\n%a endin@]"
        print_fd fd (fun fmt fdl -> List.iter (fun fd ->
          fprintf fmt "@\nand %a" print_fd fd) fdl) fdl print_expr e
  | Erec (fd::fdl, e) ->
      fprintf fmt "@[@[<hv 0>rec %a%a in@]@\n%a endin@]"
        print_fd fd (fun fmt fdl -> List.iter (fun fd ->
          fprintf fmt "@\nand %a" print_fd fd) fdl) fdl print_expr e
  | Ewith (e, wdl) ->
      fprintf fmt "@[%a@\nwith@\n  @[<hv 0>%a@]endwith@]"
        print_expr e (fun fmt wdl -> List.iter (fun wd ->
          fprintf fmt "| %a@\n" print_wd wd) wdl) wdl
  | Eif (ec,et,ee) ->
      fprintf fmt "@[if %a then@ %a@ else@ %a endif@]"
        print_expr ec print_expr et print_expr ee
  | Ewhile (d,e) ->
      fprintf fmt "@[while %a do@ %a@ done@]"
        print_expr d print_expr e
  | Ecall (q,[]) ->
      fprintf fmt "@[%a ()@]" print_q q
  | Ecall (q,el) ->
      fprintf fmt "@[%a%a@]" print_q q
        (fun fmt el -> List.iter (fun e ->
          fprintf fmt "@ %a" print_expr e) el) el
  | Eassign (d,e) ->
      fprintf fmt "@[%a <-@ %a@]" print_expr d print_expr e
  | Eseq (d,e) ->
      fprintf fmt "@[%a ;@ %a@]" print_expr d print_expr e
  | Econst c ->
      Constant.print_def fmt c
  | Eident q ->
      print_q fmt q
  | Escope (q,e) ->
      fprintf fmt "@[%a.(%a)@]" print_q q print_expr e
  | Echain (d,o,e) ->
      let o = List.hd (List.rev (String.split_on_char ' ' o.id_str)) in
      fprintf fmt "@[%a %s@ %a@]" print_expr d o print_expr e
  | Eand (d,e) ->
      fprintf fmt "@[%a &&@ %a@]" print_expr d print_expr e
  | Eor (d,e) ->
      fprintf fmt "@[%a ||@ %a@]" print_expr d print_expr e
  | Enot e ->
      fprintf fmt "@[not %a@]" print_expr e
  | Etrue ->
      fprintf fmt "true"
  | Efalse ->
      fprintf fmt "false"
  | Eparen e ->
      fprintf fmt "@[(%a)@]" print_expr e
  | Eattr (ATstr {Ident.attr_string = a},e) ->
      fprintf fmt "@[[@%s]@ %a@]" a print_expr e
  | Eattr (ATpos _,e) ->
      print_expr fmt e

and print_ld fmt (o, e) =
  fprintf fmt "%a = %a" print_out o print_expr e

and print_wd fmt (o, e) =
  fprintf fmt "%a -> %a" print_out o print_expr e

and print_fd fmt (i, pl, ol, e) =
  let rec print_ol fmt = function
    | [] -> ()
    | [o] -> print_out fmt o
    | o::ol -> fprintf fmt "%a@\n| %a" print_out o print_ol ol
  in
  fprintf fmt "%a%a @[<hv 0>: %a@]@\n  = %a"
    print_id i (fun fmt pl -> List.iter (fun p ->
      fprintf fmt " %a" print_pat p) pl) pl print_ol ol print_expr e

and print_out fmt o = print_pat fmt o

and print_pat fmt p = match p.pat_desc with
  | Pwild -> fprintf fmt "_"
  | Pvar b -> print_b fmt b
  | Papp (q,[]) -> fprintf fmt "%a ()" print_q q
  | Papp (q,pl) -> fprintf fmt "%a%a" print_q q
      (fun fmt pl -> List.iter (fun p ->
        fprintf fmt " %a" print_pat p) pl) pl
  | Pas (p,b) -> fprintf fmt "%a as %a" print_pat p print_b b
  | Por (p,q) -> fprintf fmt "%a | %a" print_pat p print_pat q
  | Pcast (p,t) -> fprintf fmt "%a : %a" print_pat p print_ty t
  | Pscope (q,p) -> fprintf fmt "%a.(%a)" print_q q print_pat p
  | Pparen p -> fprintf fmt "(%a)" print_pat p

and print_ty fmt = function
  | Tyvar i -> print_id fmt i
  | Tyapp (q,tl) -> fprintf fmt "%a%a" print_q q
      (fun fmt tl -> List.iter (fun t ->
        fprintf fmt " %a" print_ty t) tl) tl
  | Tyarrow (t,s) -> fprintf fmt "%a -> %a" print_ty t print_ty s
  | Tyscope (q,t) -> fprintf fmt "%a.(%a)" print_q q print_ty t
  | Typaren t -> fprintf fmt "(%a)" print_ty t

and print_b fmt b = fprintf fmt "%s%s%s%a"
  (if b.b_ghost then "@" else "")
  (if b.b_null  then "?" else "")
  (if b.b_mut   then "&" else "") print_id b.b_ident

and print_q fmt = function
  | Qident i -> print_id fmt i
  | Qdot (q,i) -> fprintf fmt "%a.%a" print_q q print_id i

and print_id fmt i = fprintf fmt "%s" i.id_str
