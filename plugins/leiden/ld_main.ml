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

open Why3
open Ld_ast

let debug = Debug.register_flag "leiden"
  ~desc:"Leiden plugin debug flag"

let () = Exn_printer.register (fun fmt exn -> match exn with
  | Ld_parser.Error -> Format.fprintf fmt "syntax error"
  | _ -> raise exn)

let parse_channel file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  try
    Ld_parser.ldfile Lexer.token lb
  with
    Ld_parser.Error as e -> raise (Loc.Located (Loc.extract (lb.Lexing.lex_start_p,lb.Lexing.lex_curr_p),e))

let read_channel _env _path file c =
  let _f : Ld_ast.ldfile = parse_channel file c in
  Debug.dprintf debug "coucou@.";
  Wstdlib.Mstr.empty

let () =
  Env.register_format Env.base_language "leiden" ["ld"] read_channel
    ~desc:"Andrei's experimental language"
