type attr = string (* TODO: use Ptree.attr *)

type ident = {
  ident_string : string;
  ident_attrs  : attr list;
  ident_begin  : Lexing.position;
  ident_end    : Lexing.position;
}

(* from Ident *)
let op_infix  s = "infix " ^ s
let op_prefix s = "prefix " ^ s
let op_get    s = "mixfix []" ^ s
let op_set    s = "mixfix []<-" ^ s
let op_update s = "mixfix [<-]" ^ s
let op_cut    s = "mixfix [..]" ^ s
let op_lcut   s = "mixfix [.._]" ^ s
let op_rcut   s = "mixfix [_..]" ^ s

let op_equ   = op_infix "="
let op_neq   = op_infix "<>"
let op_tight = op_prefix

let norm = "()"

type qualid =
  | Qid  of ident
  | Qdot of qualid * ident

type ty =
  | Tyvar   of ident
  | Tyapp   of qualid * ty list
  | Tyarrow of ty * ty
  | Tyscope of qualid * ty
  | Typaren of ty

type constant =
  | ConstInt of string
  | ConstFloat of string
  | ConstString of string

type binder = {
  b_ident : ident;
  b_ghost : bool;
  b_null  : bool;
  b_mut   : bool;
}

type pat = {
  pat_desc  : pat_desc;
  pat_begin : Lexing.position;
  pat_end   : Lexing.position;
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
  expr_begin  : Lexing.position;
  expr_end    : Lexing.position;
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
  | Econst of constant
  | Eident of qualid
  | Escope of qualid * expr
  | Einfix of expr * ident * expr
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

open Format

let rec print_expr fmt e = match e.expr_desc with
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
  | Econst (ConstInt s | ConstFloat s) ->
      fprintf fmt "%s" s
  | Econst (ConstString s) ->
      fprintf fmt "\"%s\"" s
  | Eident q ->
      print_q fmt q
  | Escope (q,e) ->
      fprintf fmt "@[%a.(%a)@]" print_q q print_expr e
  | Einfix (d,o,e) ->
      let o = List.hd (List.rev (String.split_on_char ' ' o.ident_string)) in
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
  | Eattr (a,e) ->
      fprintf fmt "@[[@%s]@ %a@]" a print_expr e

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
  | Qid i -> print_id fmt i
  | Qdot (q,i) -> fprintf fmt "%a.%a" print_q q print_id i

and print_id fmt i = fprintf fmt "%s" i.ident_string
