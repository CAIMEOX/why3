
open Why3

let read_channel env path file c =
  let ast = Mome_lexer.parse file c in
  Format.printf "@[%a@]@." Mome_syntax.print_expr ast;
  Wstdlib.Mstr.empty

let () = Env.register_format Env.base_language "mome" ["mome"] read_channel
  ~desc:"Memory Model language"
