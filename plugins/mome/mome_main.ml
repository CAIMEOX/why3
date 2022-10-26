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

let read_channel _env _path file c =
  let ast = Mome_lexer.parse file c in
  Format.printf "@[%a@]@." (fun fmt l ->
    List.iter (fun d -> Mome_syntax.print_decl fmt d) l) ast;
  Wstdlib.Mstr.empty

let () = Env.register_format Env.base_language "mome" ["mome"] read_channel
  ~desc:"Memory Model language"
