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

%{
open Why3
open Ptree
open Mome_syntax

let floc s e = Loc.extract (s,e)

let add_attr id l =
  { id with id_ats = List.rev_append id.id_ats l }

let mk_id s b e =
  { id_str = s; id_ats = []; id_loc = floc b e }

let id_normal b e = mk_id "()" b e
let _id_anonymous b e = mk_id "_" b e

let get_op  q b e = Qident (mk_id (Ident.op_get q) b e)
let upd_op  q b e = Qident (mk_id (Ident.op_update q) b e)
let cut_op  q b e = Qident (mk_id (Ident.op_cut q) b e)
let rcut_op q b e = Qident (mk_id (Ident.op_rcut q) b e)
let lcut_op q b e = Qident (mk_id (Ident.op_lcut q) b e)

let mk_binder i g n m = { b_ident = i; b_ghost = g; b_null = n; b_mut = m }

let mk_pat  d b e = { pat_desc = d; pat_loc = floc b e }
let mk_expr d b e = { expr_desc = d; expr_loc = floc b e }
let mk_decl d b e = { decl_desc = d; decl_loc = floc b e }

let core_ident_error  = format_of_string
  "Symbol %s cannot be user-defined. User-defined symbol cannot use ' \
    before a letter. You can only use ' followed by _ or a number."

let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Error -> Format.pp_print_string fmt "syntax error"
  | _ -> raise exn)

%}

%token <string> LIDENT CORE_LIDENT QUOTE_LIDENT UIDENT CORE_UIDENT
%token <string> RIGHTSQ_QUOTE RIGHTPAR_QUOTE RIGHTPAR_USCORE
%token <string> OP0 OP1 OP2 OP3 OP4 (* decreasing priority *)
%token <string> STRING ATTRIBUTE FAIL
%token <Why3.Number.int_constant> INTEGER
%token <Why3.Number.real_constant> REAL
%token <Why3.Loc.position> POSITION

%token LET ENDLET FUN ENDFUN REC ENDREC IN ENDIN
%token IF THEN ELSE ENDIF
%token WHILE DO DONE
%token WITH ENDWITH WHERE ENDWHERE
(*
%token BREAK CONTINUE RETURN
*)
%token TRUE FALSE AS AND

%token AMP AT BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL MINUS
%token LARROW (*LRARROW*) RARROW
%token (*LEFTBRC*) LEFTPAR LEFTSQ
%token (*RIGHTBRC*) RIGHTPAR RIGHTSQ
%token QSIGN SEMICOLON UNDERSCORE
%token AMPAMP BARBAR NOT

%token INIT EOF

%nonassoc WHERE WITH
%nonassoc SEMICOLON
%nonassoc prec_attr
%nonassoc DOT
(*
%nonassoc COLON (* weaker than -> because of t: a -> b *)
                (* this breaks "... with x : int -> 5"
                   which in OCaml is simply forbidden *)
%right RARROW (*LRARROW*)
*)
%right BARBAR
%right AMPAMP
%nonassoc NOT
%right OP4 EQUAL
%left OP3 MINUS
%left OP2
%left OP1
%nonassoc prec_prefix_op
%nonassoc INTEGER REAL (* stronger than MINUS *)
%nonassoc LEFTSQ
%nonassoc OP0

%start <Mome_syntax.decl list> top_level

%%

top_level:
| top_level_decl* EOF   { $1 }
| INIT                  { assert false }
| FAIL                  { assert false }

top_level_decl:
| LET let_defn ENDLET   { mk_decl (Dlet ($2)) $startpos $endpos }
| FUN fun_defn ENDFUN   { mk_decl (Dfun ($2)) $startpos $endpos }
| REC fun_defn ENDREC   { mk_decl (Drec ($2)) $startpos $endpos }

(* Expressions *)

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr: seq_expr_nsc | seq_expr_sc  { $1 }

seq_expr_nsc:
| assign_expr
| over_expr(seq_expr_nsc) { $1 }

seq_expr_sc:
| assign_expr SEMICOLON
| over_expr(seq_expr_sc)  { $1 }

over_expr(X):
| assign_expr SEMICOLON X
    { mk_expr (Eseq ($1, $3)) $startpos $endpos }
| LET let_defn ENDLET SEMICOLON X
    { mk_expr (Elet ($2, $5)) $startpos $endpos }
| FUN fun_defn ENDFUN SEMICOLON X
    { mk_expr (Efun ($2, $5)) $startpos $endpos }
| REC fun_defn ENDREC SEMICOLON X
    { mk_expr (Erec ($2, $5)) $startpos $endpos }

assign_expr:
| expr                    { $1 }
| expr LARROW expr
    { mk_expr (Eassign ($1, $3)) $startpos $endpos }
| under_expr WHERE fun_defn ENDWHERE
    { mk_expr (Erec ($3, $1)) $startpos $endpos }
| under_expr WITH with_defn ENDWITH
    { mk_expr (Ewith ($1, $3)) $startpos $endpos }

%inline under_expr: assign_expr | seq_expr_sc  { $1 }

expr:
| single_expr             { $1 }
| single_expr ident_skip preceded(COMMA, single_expr)+
    { mk_expr (Ecall (Qident $2, $1::$3)) $startpos $endpos }

single_expr: e = mk_expr(single_expr_)  { e }

single_expr_:
| expr_arg_
    { $1 }
| single_expr AMPAMP single_expr
    { Eand ($1, $3) }
| single_expr BARBAR single_expr
    { Eor ($1, $3) }
| NOT single_expr
    { Enot $2 }
| prefix_op single_expr %prec prec_prefix_op
    { Ecall (Qident $1, [$2]) }
| minus_numeral
    { Econst $1 }
| l = single_expr ; o = infix_op_4 ; r = single_expr
    { Echain (l,o,r) }
| l = single_expr ; o = infix_op_123 ; r = single_expr
    { Ecall (Qident o, [l;r]) }
| qualid expr_arg+
    { Ecall ($1, $2) }
| qualid LEFTPAR RIGHTPAR
    { Ecall ($1, []) }
| LEFTPAR ident_skip RIGHTPAR
    { Ecall (Qident $2, []) }
| IF seq_expr THEN seq_expr ELSE seq_expr ENDIF
    { Eif ($2, $4, $6) }
| IF seq_expr THEN seq_expr expr_skip ENDIF
    { Eif ($2, $4, $5) }
| LET let_defn IN seq_expr ENDIN
    { Elet ($2, $4) }
| FUN fun_defn IN seq_expr ENDIN
    { Efun ($2, $4) }
| REC fun_defn IN seq_expr ENDIN
    { Erec ($2, $4) }
| WHILE seq_expr DO seq_expr DONE
    { Ewhile ($2, $4) }
| WHILE seq_expr DO expr_skip DONE
    { Ewhile ($2, $4) }
| attr single_expr %prec prec_attr
    { Eattr ($1, $2) }

with_defn: BAR? separated_nonempty_list(BAR,
          separated_pair(outcome, RARROW, seq_expr))  { $2 }

let_defn: separated_nonempty_list(AND,
          separated_pair(outcome, EQUAL, seq_expr))   { $1 }

fun_defn: separated_nonempty_list(AND,
          separated_pair(fun_decl, EQUAL, seq_expr))  { $1 }

fun_decl: lident_nq pat_arg* fun_out  { $1, $2, $3 }

fun_out:
| (* epsilon *)   { [] }
| COLON separated_nonempty_list(BAR, out_uni)   { $2 }

expr_skip: ident_skip     { mk_expr (Ecall (Qident $1, [])) $startpos $endpos }
ident_skip: (* epsilon *) { id_normal $startpos $endpos }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                          { Eident $1 }
| literal                         { Econst $1 }
| TRUE                            { Etrue }
| FALSE                           { Efalse }
| o = prefix_op_0 ; a = expr_arg  { Ecall (Qident o, [a]) }
| expr_sub_                       { $1 }

expr_dot_:
| lqualid                         { Eident $1 }
| o = prefix_op_0 ; a = expr_dot  { Ecall (Qident o, [a]) }
| expr_sub_                       { $1 }

expr_sub_:
| expr_block_                         { $1 }
| uqualid DOT mk_expr(expr_block_)    { Escope ($1, $3) }
| expr_dot DOT lqualid_rich           { Ecall ($3, [$1]) }
| expr_arg LEFTSQ expr rightsq
    { Ecall (get_op $4 $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ expr LARROW expr rightsq
    { Ecall (upd_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT expr rightsq
    { Ecall (cut_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT rightsq
    { Ecall (rcut_op $5 $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ DOTDOT expr rightsq
    { Ecall (lcut_op $5 $startpos($2) $endpos($2), [$1;$4]) }

expr_block_:
| LEFTPAR seq_expr RIGHTPAR   { Eparen $2 }
(*
| LEFTBRC field_list1(expr) RIGHTBRC                { Erecord $2 }
| LEFTBRC expr_arg WITH field_list1(expr) RIGHTBRC  { Eupdate ($2, $4) }
*)

(* Patterns *)

mk_pat(X): X { mk_pat $1 $startpos $endpos }

pattern: mk_pat(pattern_) { $1 }
pat_arg: mk_pat(pat_arg_) { $1 }
pat_uni: mk_pat(pat_uni_) { $1 }

outcome: mk_pat(outcome_) { $1 }
out_uni: mk_pat(out_uni_) { $1 }

outcome_:
| out_uni_                        { $1 }
| mk_pat(out_uni_) BAR outcome    { Por ($1,$3) }

out_uni_:
| pat_uni ident_skip preceded(COMMA, pat_uni)*
                                  { Papp (Qident $2, $1::$3) }
| LEFTPAR ident_skip RIGHTPAR     { Papp (Qident $2, []) }
| lident_attrs pat_arg+           { Papp (Qident $1, $2) }
| lident_attrs LEFTPAR RIGHTPAR   { Papp (Qident $1, []) }

pattern_:
| pat_uni_                        { $1 }
| pat_uni BAR pattern             { Por ($1, $3) }

pat_uni_:
| pat_arg_                        { $1 }
| uqualid pat_arg+                { Papp ($1, $2) }
| pat_uni AS binder               { Pas ($1, $3) }
| pat_uni COLON ty                { Pcast ($1, $3) }

pat_arg_:
| UNDERSCORE                      { Pwild }
| binder                          { Pvar $1 }
| uqualid                         { Papp ($1, []) }
| uqualid DOT mk_pat(pat_block_)  { Pscope ($1, $3) }
| pat_block_                      { $1 }

pat_block_:
| LEFTPAR pattern RIGHTPAR        { Pparen $2 }
(* | LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 } *)

binder:
| lident_attrs                    { mk_binder $1 false false false }
| AT lident_attrs                 { mk_binder $2 true  false false }
| QSIGN lident_attrs              { mk_binder $2 false true  false }
| AMP lident_attrs                { mk_binder $2 false false true  }
| AT QSIGN lident_attrs           { mk_binder $3 true  true  false }
| QSIGN AT lident_attrs           { mk_binder $3 true  true  false }
| AT AMP lident_attrs             { mk_binder $3 true  false true  }
| AMP AT lident_attrs             { mk_binder $3 true  false true  }
| QSIGN AMP lident_attrs          { mk_binder $3 false true  true  }
| AMP QSIGN lident_attrs          { mk_binder $3 false true  true  }
| AT QSIGN AMP lident_attrs       { mk_binder $4 true  true  true  }
| QSIGN AT AMP lident_attrs       { mk_binder $4 true  true  true  }
| QSIGN AMP AT lident_attrs       { mk_binder $4 true  true  true  }
| AT AMP QSIGN lident_attrs       { mk_binder $4 true  true  true  }
| AMP AT QSIGN lident_attrs       { mk_binder $4 true  true  true  }
| AMP QSIGN AT lident_attrs       { mk_binder $4 true  true  true  }

(* Types *)

ty:
| ty_arg                  { $1 }
| lqualid ty_arg+         { Tyapp ($1, $2) }
(*
| ty RARROW ty            { Tyarrow ($1, $3) }
*)

ty_arg:
| lqualid                 { Tyapp ($1, []) }
| quote_lident            { Tyvar $1 }
| uqualid DOT ty_block    { Tyscope ($1, $3) }
| ty_block                { $1 }

ty_block:
| LEFTPAR ty RIGHTPAR     { Typaren $2 }

(* Literals *)

minus_numeral:
| MINUS INTEGER   { Constant.(ConstInt (Number.neg_int $2)) }
| MINUS REAL      { Constant.(ConstReal (Number.neg_real $2))}

literal:
| INTEGER   { Constant.ConstInt  $1 }
| REAL      { Constant.ConstReal $1 }
| STRING    { Constant.ConstStr  $1 }

(* Qualified idents *)

qualid:
| ident                   { Qident $1 }
| uqualid DOT ident       { Qdot ($1, $3) }

uqualid:
| uident                  { Qident $1 }
| uqualid DOT uident      { Qdot ($1, $3) }

lqualid:
| lident                  { Qident $1 }
| uqualid DOT lident      { Qdot ($1, $3) }

lqualid_rich:
| lident                  { Qident $1 }
| lident_op               { Qident $1 }
| uqualid DOT lident      { Qdot ($1, $3) }
| uqualid DOT lident_op   { Qdot ($1, $3) }

(*
tqualid:
| uident                  { Qident $1 }
| squalid DOT uident      { Qdot ($1, $3) }

squalid:
| sident                  { Qident $1 }
| squalid DOT sident      { Qdot ($1, $3) }
*)

(* Idents *)

(*
ident_attrs:  attrs(ident_nq)   { $1 }
*)
lident_attrs: attrs(lident_nq)  { $1 }
(*
uident_attrs: attrs(uident_nq)  { $1 }
*)

ident:
| uident          { $1 }
| lident          { $1 }
| lident_op       { $1 }

(*
ident_nq:
| uident_nq       { $1 }
| lident_nq       { $1 }
| lident_op_nq    { $1 }
*)

(*
lident_rich:
| lident_nq       { $1 }
| lident_op_nq    { $1 }
*)

uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { mk_id $1 $startpos $endpos }

(*
uident_nq:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { let loc = floc $startpos $endpos in
                    Loc.errorm ~loc core_ident_error $1 }
*)

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { mk_id $1 $startpos $endpos }

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { let loc = floc $startpos $endpos in
                    Loc.errorm ~loc core_ident_error $1 }

(*
sident:
| lident          { $1 }
| uident          { $1 }
| STRING          { mk_id $1 $startpos $endpos }
(* TODO: we can add all keywords and save on quotes *)
*)

quote_lident:
| QUOTE_LIDENT    { mk_id $1 $startpos $endpos }

(* Symbolic operation names *)

lident_op:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { mk_id ($2^$3) $startpos $endpos }

(*
lident_op_nq:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { let loc = floc $startpos $endpos in
      Loc.errorm ~loc "Symbol (%s)%s cannot be user-defined" $2 $3 }
*)

lident_op_str:
| op_symbol                         { Ident.op_infix $1 }
| op_symbol UNDERSCORE              { Ident.op_prefix $1 }
| MINUS     UNDERSCORE              { Ident.op_prefix "-" }
| EQUAL                             { Ident.op_infix "=" }
| MINUS                             { Ident.op_infix "-" }
| OP0 UNDERSCORE?                   { Ident.op_prefix $1 }
| LEFTSQ rightsq                    { Ident.op_get $2 }
| LEFTSQ rightsq LARROW             { Ident.op_set $2 }
| LEFTSQ LARROW rightsq             { Ident.op_update $3 }
| LEFTSQ DOTDOT rightsq             { Ident.op_cut $3 }
| LEFTSQ UNDERSCORE DOTDOT rightsq  { Ident.op_rcut $4 }
| LEFTSQ DOTDOT UNDERSCORE rightsq  { Ident.op_lcut $4 }

rightsq:
| RIGHTSQ         { "" }
| RIGHTSQ_QUOTE   { $1 }

op_symbol:  OP1 | OP2 | OP3 | OP4   { $1 }

%inline prefix_op_0:
| o = OP0   { mk_id (Ident.op_prefix o)   $startpos $endpos }

prefix_op:
| op_symbol { mk_id (Ident.op_prefix $1)  $startpos $endpos }
| MINUS     { mk_id (Ident.op_prefix "-") $startpos $endpos }

%inline infix_op_123:
| o = OP1   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP2   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP3   { mk_id (Ident.op_infix o)    $startpos $endpos }
| MINUS     { mk_id (Ident.op_infix "-")  $startpos $endpos }

%inline infix_op_4:
| o = OP4   { mk_id (Ident.op_infix o)    $startpos $endpos }
| EQUAL     { mk_id (Ident.op_infix "=")  $startpos $endpos }

(* Attributes and position markers *)

attrs(X): X attr* { add_attr $1 $2 }

attr:
| ATTRIBUTE { ATstr (Ident.create_attribute $1) }
| POSITION  { ATpos $1 }
