%{
open Mome_syntax

let add_attr id l = (* id.ident_attrs is usually nil *)
  { id with ident_attrs = List.rev_append id.ident_attrs l }

let id_anonymous b e =
  { ident_string = "_"; ident_attrs = []; ident_begin = b; ident_end = e }

let mk_id s b e =
  { ident_string = s; ident_attrs = []; ident_begin = b; ident_end = e }

let get_op  q b e = Qid (mk_id (op_get q) b e)
let upd_op  q b e = Qid (mk_id (op_update q) b e)
let cut_op  q b e = Qid (mk_id (op_cut q) b e)
let rcut_op q b e = Qid (mk_id (op_rcut q) b e)
let lcut_op q b e = Qid (mk_id (op_lcut q) b e)

let mk_binder i g n m = { b_ident = i; b_ghost = g; b_null = n; b_mut = m }

let mk_pat  d b e = { pat_desc = d; pat_begin = b; pat_end = e }
let mk_expr d b e = { expr_desc = d; expr_begin = b; expr_end = e }

%}

%token <string> LIDENT CORE_LIDENT QUOTE_LIDENT UIDENT CORE_UIDENT
%token <string> RIGHTSQ_QUOTE RIGHTPAR_QUOTE RIGHTPAR_USCORE
%token <string> OP0 OP1 OP2 OP3 OP4 (* decreasing priority *)
%token <string> STRING ATTRIBUTE
%token <string> INTEGER
%token <string> FLOAT

%token LET (*FUN REC*) IN ENDIN
%token IF THEN ELSE ENDIF
%token WHILE DO DONE
(*
%token WITH ENDWITH
%token WHERE ENDWHERE
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

%token INIT EOF FAIL

(*
%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc LET FUN REC
*)
%nonassoc DOT (*RETURN*)
(*
%nonassoc below_LARROW
%nonassoc LARROW
%nonassoc below_COMMA
%nonassoc COMMA
*)
%nonassoc prec_attr
(*
%nonassoc COLON
*)
%right RARROW (*LRARROW*)
%right BARBAR
%right AMPAMP
%nonassoc NOT
%right OP4 EQUAL
%left OP3 MINUS
%left OP2
%left OP1
%nonassoc prec_prefix_op
%nonassoc INTEGER FLOAT (* stronger than MINUS *)
%nonassoc LEFTSQ
%nonassoc OP0

%start <Mome_syntax.expr> seq_expr_eof

%%

(* Expressions *)

seq_expr_eof:
| seq_expr EOF    { $1 }
| INIT            { assert false }
| FAIL            { assert false }

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr:
| assign_expr (*%prec below_SEMI*)  { $1 }
| assign_expr SEMICOLON         { $1 }
| assign_expr SEMICOLON seq_expr
    { mk_expr (Eseq ($1, $3)) $startpos $endpos }

assign_expr:
| expr (*%prec below_LARROW*)         { $1 }
| expr LARROW expr
    { mk_expr (Eassign ($1, $3)) $startpos $endpos }

expr:
| single_expr (*%prec below_COMMA*)   { $1 }
| single_expr ident_skip preceded(COMMA, single_expr)+
    { mk_expr (Ecall (Qid $2, $1::$3)) $startpos $endpos }

single_expr: e = mk_expr(single_expr_)  { e }

(*
  | Efun of fun_defn list * expr
  | Erec of fun_defn list * expr
  | Ewith of expr * with_defn list
*)

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
    { Ecall (Qid $1, [$2]) }
| minus_numeral
    { Econst $1 }
| l = single_expr ; o = infix_op_4 ; r = single_expr
    { Einfix (l,o,r) }
| l = single_expr ; o = infix_op_123 ; r = single_expr
    { Ecall (Qid o, [l;r]) }
| qualid expr_arg+
    { Ecall ($1, $2) }
| qualid LEFTPAR RIGHTPAR
    { Ecall ($1, []) }
| LEFTPAR ident_skip RIGHTPAR
    { Ecall (Qid $2, []) }
| IF seq_expr THEN seq_expr ELSE seq_expr ENDIF
    { Eif ($2, $4, $6) }
| IF seq_expr THEN seq_expr expr_skip ENDIF
    { Eif ($2, $4, $5) }
| LET separated_nonempty_list(AND,
        separated_pair(outcome, EQUAL, seq_expr))
  IN seq_expr ENDIN
    { Elet ($2, $4) }
| WHILE seq_expr DO seq_expr DONE
    { Ewhile ($2, $4) }
| WHILE seq_expr DO expr_skip DONE
    { Ewhile ($2, $4) }
| attr single_expr %prec prec_attr
    { Eattr ($1, $2) }

expr_skip: ident_skip     { mk_expr (Ecall (Qid $1, [])) $startpos $endpos }
ident_skip: (* epsilon *) { mk_id norm $startpos $endpos }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                          { Eident $1 }
| literal                         { Econst $1 }
| TRUE                            { Etrue }
| FALSE                           { Efalse }
| o = prefix_op_0 ; a = expr_arg  { Ecall (Qid o, [a]) }
| expr_sub_                       { $1 }

expr_dot_:
| lqualid                         { Eident $1 }
| o = prefix_op_0 ; a = expr_dot  { Ecall (Qid o, [a]) }
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

outcome_:
| out_uni_                        { $1 }
| mk_pat(out_uni_) BAR outcome    { Por ($1,$3) }

out_uni_:
| pat_uni ident_skip preceded(COMMA, pat_uni)*
                                  { Papp (Qid $2, $1::$3) }
| LEFTPAR ident_skip RIGHTPAR     { Papp (Qid $2, []) }
| lident_attrs pat_arg+           { Papp (Qid $1, $2) }
| lident_attrs LEFTPAR RIGHTPAR   { Papp (Qid $1, []) }

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
| ty RARROW ty            { Tyarrow ($1, $3) }

ty_arg:
| lqualid                 { Tyapp ($1, []) }
| quote_lident            { Tyvar $1 }
| uqualid DOT ty_block    { Tyscope ($1, $3) }
| ty_block                { $1 }

ty_block:
| LEFTPAR ty RIGHTPAR     { Typaren $2 }

(* Literals *)

minus_numeral:
| MINUS INTEGER { ConstInt   ("-" ^ $2) }
| MINUS FLOAT   { ConstFloat ("-" ^ $2) }

literal:
| INTEGER { ConstInt    $1 }
| FLOAT   { ConstFloat  $1 }
| STRING  { ConstString $1 }

(* Qualified idents *)

qualid:
| ident                   { Qid $1 }
| uqualid DOT ident       { Qdot ($1, $3) }

uqualid:
| uident                  { Qid $1 }
| uqualid DOT uident      { Qdot ($1, $3) }

lqualid:
| lident                  { Qid $1 }
| uqualid DOT lident      { Qdot ($1, $3) }

lqualid_rich:
| lident                  { Qid $1 }
| lident_op               { Qid $1 }
| uqualid DOT lident      { Qdot ($1, $3) }
| uqualid DOT lident_op   { Qdot ($1, $3) }

(*
tqualid:
| uident                  { Qid $1 }
| squalid DOT uident      { Qdot ($1, $3) }

squalid:
| sident                  { Qid $1 }
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
| CORE_UIDENT     { let loc = floc $startpos($1) $endpos($1) in
*)

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { mk_id $1 $startpos $endpos }

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
(*
| CORE_LIDENT     { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc core_ident_error $1 }
*)

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
(*
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { let loc = floc $startpos $endpos in
      Loc.errorm ~loc "Symbol (%s)%s cannot be user-defined" $2 $3 }
*)
*)

lident_op_str:
| op_symbol                         { op_infix $1 }
| op_symbol UNDERSCORE              { op_prefix $1 }
| MINUS     UNDERSCORE              { op_prefix "-" }
| EQUAL                             { op_infix "=" }
| MINUS                             { op_infix "-" }
| OP0 UNDERSCORE?                   { op_prefix $1 }
| LEFTSQ rightsq                    { op_get $2 }
| LEFTSQ rightsq LARROW             { op_set $2 }
| LEFTSQ LARROW rightsq             { op_update $3 }
| LEFTSQ DOTDOT rightsq             { op_cut $3 }
| LEFTSQ UNDERSCORE DOTDOT rightsq  { op_rcut $4 }
| LEFTSQ DOTDOT UNDERSCORE rightsq  { op_lcut $4 }

rightsq:
| RIGHTSQ         { "" }
| RIGHTSQ_QUOTE   { $1 }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }

%inline prefix_op_0:
| o = OP0   { mk_id (op_prefix o)   $startpos $endpos }

prefix_op:
| op_symbol { mk_id (op_prefix $1)  $startpos $endpos }
| MINUS     { mk_id (op_prefix "-") $startpos $endpos }

%inline infix_op_123:
| o = OP1   { mk_id (op_infix o)    $startpos $endpos }
| o = OP2   { mk_id (op_infix o)    $startpos $endpos }
| o = OP3   { mk_id (op_infix o)    $startpos $endpos }
| MINUS     { mk_id (op_infix "-")  $startpos $endpos }

%inline infix_op_4:
| o = OP4   { mk_id (op_infix o)    $startpos $endpos }
| EQUAL     { mk_id (op_infix "=")  $startpos $endpos }

(* Attributes and position markers *)

attrs(X): X attr* { add_attr $1 $2 }

attr:
| ATTRIBUTE { $1 }
(* TODO:
| ATTRIBUTE { ATstr (Ident.create_attribute $1) }
| POSITION  { ATpos $1 }
*)
