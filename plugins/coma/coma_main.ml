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
open Why3
open Coma_syntax
open Coma_typing
open Coma_vc
open Ptree

let mk_goal tuc s e =
  let prs = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
  Theory.add_prop_decl tuc Decl.Pgoal prs (vc e)

(* let add_vc tuc (s, _, _, d) = mk_goal tuc s.hs_name.id_string d *)

let add_vcf tuc name d = mk_goal tuc name d

let parse_simpl_use env tuc = function
  | Duseimport (_, _, [Qdot (Qident l, m), None]) ->
      let th = Env.read_theory env [l.id_str] m.id_str in
      Theory.use_export tuc th
  | _ -> Loc.errorm "unhandled usage of `use'"

let read_channel env path file c =

  let uses, ast = Coma_lexer.parse_channel file c in

  let tuc = Theory.create_theory ~path (Ident.id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = List.fold_left (parse_simpl_use env) tuc uses in

  let factor def e = {
    pexpr_desc = PEdef (e, false, [def]);
    pexpr_loc  = def.pdefn_loc;
  } in

  let eany = { pexpr_loc = Loc.dummy_position ; pexpr_desc = PEany } in
  let astf = List.fold_right factor ast eany in

  let astf = type_prog tuc ctx0 astf in

  Format.printf "@[%a@]@." Coma_syntax.pp_expr astf;

  (* let _ctx, ast = Lists.map_fold_left (type_defn tuc) ctx0 ast in
     let ast = (create_hsymbol (id_fresh "dummy"), [], [], _expr2) :: ast in
     let tuc = List.fold_left add_vc tuc ast in *)

  let tuc = add_vcf tuc file astf in

  (* let tuc = mk_goal tuc "expr1" expr1 in
     let tuc = mk_goal tuc "expr2" expr2 in *)

  Wstdlib.Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
