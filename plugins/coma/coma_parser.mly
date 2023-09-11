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

(*- exemple :

      rev_append [] {l0 r0} =
        loop
        / loop = { rev l ++ r = rev l0 ++ r0 }
            ! unList {l} (fun {h t} -> assign &r {cons h r}
                               (fun -> assign &l {t} (loop)))
                         (out)
        / out = { r = rev l0 ++ r0 } ? halt
        / &r = {r0}
        / &l = {l0}
 -*)

%{
open Why3
open Ptree
open Coma_syntax

let floc s e = Loc.extract (s,e)

let mk_pexpr d b e = { pexpr_desc = d; pexpr_loc = floc b e }
let mk_defn d b e = { pdefn_desc = d; pdefn_loc = floc b e }

%}

%token BANG QUESTION SLASH

%start <Coma_syntax.pdefn list> top_level
%start <unit> dummy

%%

top_level:
| defn* EOF   { $1 }

defn:
| id=lident w=prewrites p=coma_params EQUAL e=coma_prog
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $startpos $endpos }

local_defn:
| id=lident w=prewrites p=coma_params EQUAL e=coma_expr
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $startpos $endpos }

coma_prog:
| e=coma_expr
  { e }
| e=coma_prog SLASH d=local_defn
  { mk_pexpr (PEdef (e, false, [d])) $startpos $endpos }
| e=coma_prog SLASH AMP id=lident EQUAL LEFTBRC t=term RIGHTBRC
  { mk_pexpr (PEset (e, [id, t])) $startpos $endpos }

coma_expr:
| d = coma_desc
  { mk_pexpr d $startpos $endpos }

coma_desc:
| LEFTBRC t=term RIGHTBRC e=coma_expr
  { PEcut (t, e) }
| BANG e=coma_expr
  { PEbox e }
| QUESTION e=coma_expr
  { PEwox e }
| e=coma_expr2 al=coma_arg*
  { let app e a = mk_pexpr (PEapp (e, a)) $startpos $endpos in
    let e = List.fold_left app e al in
    e.pexpr_desc }

coma_expr2:
| d = coma_desc2
  { mk_pexpr d $startpos $endpos }

coma_desc2:
| x=lident
  { PEsym x }
| ANY
  { PEany }
| c=coma_closure
  { c.pexpr_desc }
| LEFTPAR e=coma_prog RIGHTPAR
  { e.pexpr_desc }

coma_closure:
| LEFTPAR FUN p=coma_params ARROW e=coma_prog RIGHTPAR
  { let d = PElam (p, e) in
    mk_pexpr d $startpos $endpos }

prewrites:
| w = loption(prewrites_)
  { w }

prewrites_:
| LEFTSQ w=lident* RIGHTSQ
  { w }

coma_arg:
| LT ty=ty GT
  { At ty }
| LEFTBRC t=term RIGHTBRC
  { Av t }
| AMP x=lident
  { Ar x }
| LEFTPAR e=coma_prog RIGHTPAR
  { Ac e }
| c=coma_closure
  { Ac c }

coma_params:
| pl=coma_param*
  { (List.flatten pl) }

coma_tvar:
| x=QUOTE_LIDENT
  { PPt (mk_id x $startpos $endpos) }

coma_param:
| LT l=coma_tvar* GT
  { l }
| LEFTBRC lid=lident+ RIGHTBRC
  { List.map (fun id -> PPv id) lid }
| LEFTPAR id=lident w=prewrites p=coma_params RIGHTPAR
  { [PPc (id, w, p)] }

/* silent Menhir's errors about unreachable non terminal symbols */

dummy:
| module_head_parsing_only scope_head_parsing_only dummy_decl* EOF
    { }

dummy_decl:
| meta_decl {}
| use_clone_parsing_only {}
| prog_decl {}
| pure_decl {}
