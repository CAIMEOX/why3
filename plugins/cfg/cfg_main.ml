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

open Cfg_paths
open Cfg_ast
open Why3
open Pmodule
open Ptree

let has_stackify = ref false
let stackify = ref (fun _ -> failwith "stackify is not compiled")

let set_stackify f = stackify := f; has_stackify := true

let stackify_attr = Ident.create_attribute "cfg:stackify"

let translate_cfg_fundef (x : cfg_fundef) =
  let (id, _, _, _, _, _, _, _, _) = x in
  if List.exists (function ATstr a -> Ident.attr_equal a stackify_attr | _ -> false) id.id_ats
  then !stackify x else Cfg_paths.translate_cfg_fundef x

let translate_letcfg d is_const =
  let loc = Loc.dummy_position in
  let (id, ghost, rk, args, retty, pat, mask, spec, body) = translate_cfg_fundef d in

  let rk = if is_const then Expr.RKfunc else rk in
  let r =
    Dlet (id, ghost, rk, Ptree_helpers.expr ~loc (Efun (args, retty, pat, mask, spec, body)))
  in
  Debug.dprintf Cfg_paths.debug "%a@." (Mlw_printer.pp_decl ~attr:true) r;
  r

let translate_reccfg ds is_const =
  let translated_fundefs = List.map (fun d ->
    let (id, ghost, rk, args, retty, pat, mask, spec, body) = translate_cfg_fundef d in
    let rk = if is_const then Expr.RKfunc else rk in
    (id, ghost, rk, args, retty, pat, mask, spec, body)
    ) ds in

  Drec translated_fundefs

let rec translate_decl d acc =
  match d with
  | Dmlw_decl d -> d :: acc
  | Dletcfg (d, const) -> (translate_letcfg d const)::acc
  | Dreccfg (l, const) -> translate_reccfg l const :: acc
  | Cfg_ast.Dscope (l, b, i, ds) -> Ptree.Dscope (l, b, i, List.fold_right translate_decl ds []) :: acc

let translate (m,dl) =
  (m,List.fold_right translate_decl dl [])


let read_channel env _path file c =
  let f : Cfg_ast.cfg_file = Cfg_lexer.parse_channel file c in
  let ptree = Modules (List.map translate f) in
  Debug.dprintf debug "%a@." (Mlw_printer.pp_mlw_file ~attr:true) ptree;
  let mm = Typing.type_mlw_file env [] (file ^ ".mlw") ptree in
  mm

let () =
  Env.register_format mlw_language "mlcfg" ["mlcfg"; "stdout"] read_channel
    ~desc:"whyml extended with functions implemented by control-flow-graphs"
