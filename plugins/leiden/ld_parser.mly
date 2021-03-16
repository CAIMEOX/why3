(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{

  open Why3
  open Ld_ast

  let floc s e = Loc.extract (s,e)

%}

%start ldfile
%type <Ld_ast.ldfile> ldfile

%%

ldfile:
  | ASSERT LEFTBRC term RIGHTBRC EOF { () }
;
