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
open Wstdlib
open Ident
open Ty
open Term
open Coma_syntax
open Coma_vc

type vr = Ref of vsymbol | Var of vsymbol

type ctx = {
  vars: vr Mstr.t;
  denv: Dterm.denv;
  hdls: (hsymbol * vsymbol list * param list) Mstr.t;
}

let ctx0 = {
  vars = Mstr.empty;
  denv = Dterm.denv_empty;
  hdls = Mstr.empty;
}

let add_hdl hs w pl ctx =
  let str = hs.hs_name.id_string in
  { ctx with hdls = Mstr.add str (hs, w, pl) ctx.hdls }

let add_var vs ctx =
  let str = vs.vs_name.id_string in
  { ctx with vars = Mstr.add str (Var vs) ctx.vars;
             denv = Mstr.add str (Dterm.DTgvar vs) ctx.denv }

let add_ref vs ctx =
  let str = vs.vs_name.id_string in
  { ctx with vars = Mstr.add str (Ref vs) ctx.vars;
             denv = Mstr.add str (Dterm.DTgvar vs) ctx.denv }

open Ptree


let rec type_param tuc ctx = function
  | PPv (id, ty) ->
      let ty = Typing.ty_of_pty tuc ty in
      let vs = create_vsymbol (id_fresh ~loc:id.id_loc id.id_str) ty in
      add_var vs ctx, Pv vs
  | PPr (id, ty) ->
      let ty = Typing.ty_of_pty tuc ty in
      let vs = create_vsymbol (id_fresh ~loc:id.id_loc id.id_str) ty in
      add_ref vs ctx, Pr vs
  | PPc (id, w, pl) ->
      let _ctx1, params = Lists.map_fold_left (type_param tuc) ctx pl in
      let get_vs (id: Ptree.ident) =
        try match Mstr.find id.id_str ctx.vars with
          | Ref v -> v
          | Var _ -> Loc.errorm ~loc:id.id_loc "the variable %s is not a reference" id.id_str
        with Not_found -> Loc.errorm ~loc:id.id_loc "unbounded variable %s" id.id_str
      in
      let w = List.map get_vs w in
      let hs = { hs_name = id_register (id_fresh ~loc:id.id_loc id.id_str) } in
      (* Format.printf "{{{%s}}}" hs.hs_name.id_string; *)
      add_hdl hs w params ctx, Pc (hs, w, params)
  | PPt i -> Loc.errorm ~loc:i.id_loc "polymorphism is not supported yet"

let type_term tuc ctx t =
  Typing.type_term_in_denv (Theory.get_namespace tuc) Theory.(tuc.uc_known) Theory.(tuc.uc_crcmap) ctx.denv t

let type_fmla tuc ctx t =
  Typing.type_fmla_in_denv (Theory.get_namespace tuc) Theory.(tuc.uc_known) Theory.(tuc.uc_crcmap) ctx.denv t

let rec check_param ~loc l r = match l,r with
  | Pt _, Pt _ -> ()
  | Pr l, Pr r
  | Pv l, Pv r  when ty_equal l.vs_ty r.vs_ty -> ()
  | Pc (_, _, l), Pc (_, _, r) -> check_params ~loc l r
  | _ -> Loc.errorm ~loc "type error"

and check_params ~loc l r =
  try List.iter2 (check_param ~loc) l r
  with Invalid_argument _ -> Loc.errorm ~loc "bad arity: %d argument(s) expected, %d given" (List.length l) (List.length r)

let rec type_expr tuc ctx { pexpr_desc=d; pexpr_loc=loc } =
  match d with
  | PEsym id ->
      let h, _, pl =
        try Mstr.find id.id_str ctx.hdls
        with Not_found -> Loc.errorm ~loc:id.id_loc "unbounded handler %s" id.id_str in
      Esym h, pl
  | PEapp (e, a) ->
      let e, te = type_expr tuc ctx e in
      (match te, a with
       | [], _ -> assert false
       | Pv vs :: tes, PAv t ->
           let tt = type_term tuc ctx t in
           (match tt.t_ty with
            | Some ty when ty_equal ty vs.vs_ty -> ()
            | _ -> Loc.errorm ~loc:t.term_loc "type error in application"
           );
           Eapp (e, Av tt), tes
       | Pr rs :: tes, PAr id ->
           let s =
             try match Mstr.find id.id_str ctx.vars with
               | Ref v -> v
               | Var _ -> Loc.errorm ~loc:id.id_loc "the variable %s is not a reference" id.id_str
             with Not_found -> Loc.errorm ~loc:id.id_loc "unbounded variable %s" id.id_str
           in
           if ty_equal rs.vs_ty s.vs_ty then
             Eapp (e, Ar s), tes
           else
             Loc.errorm ~loc:id.id_loc "type error in application"
       | Pc (_h, _vs, pl) :: tes, PAc ea ->
           let ea, tea = type_expr tuc ctx ea in
           check_params ~loc pl tea;
           Eapp (e, Ac ea), tes
       | Pt _ :: _tes, PAt _ -> Loc.errorm ~loc:loc "polymorphism is not supported yet"
       | _ ->  Loc.errorm ~loc "type error with the application")
  | PEany -> Eany, []
  | PEbox e ->
      let e = type_prog ~loc tuc ctx e in
      Ebox e, []
  | PEwox e ->
      let e = type_prog ~loc tuc ctx e in
      Ewox e, []

  (* | PEset (e, [id,t,pty]) ->
      let tt = type_term tuc ctx t in
      let ty = Typing.ty_of_pty tuc pty in
      (match tt.t_ty with
       | Some tty when ty_equal tty ty -> ()
       | _ -> Loc.errorm ~loc:id.id_loc "type error with &%s's assignation" id.id_str
      );
      let vs = create_vsymbol (id_fresh ~loc:id.id_loc id.id_str) ty in
      let ctx = add_ref vs ctx in
      let e = type_prog ~loc tuc ctx e in
      Eset (e, [vs,tt]), [] *)

  | PEset (e, l) ->
      let f ctx (id, t, pty) =
        let tt = type_term tuc ctx t in
        let ty = Typing.ty_of_pty tuc pty in
        (match tt.t_ty with
         | Some tty when ty_equal tty ty -> ()
         | _ -> Loc.errorm ~loc:id.id_loc "type error with &%s's assignation" id.id_str
        );
        let vs = create_vsymbol (id_fresh ~loc:id.id_loc id.id_str) ty in
        add_ref vs ctx, (vs,tt)
      in
      let ctx, ll = Lists.map_fold_left f ctx l in
      let e = type_prog ~loc tuc ctx e in
      Eset (e, ll), []

  | PEcut (t,e) ->
      let tt = type_fmla tuc ctx t in
      let e = type_prog ~loc tuc ctx e in
      Ecut (tt, e), []

  | PEdef (e, false, d) ->
      let ctt = List.fold_left
          (fun acc {pdefn_desc=d; pdefn_loc=loc} ->
             let id = d.pdefn_name in
             let ident = id_register (id_fresh ~loc:id.id_loc id.id_str) in
             let h = { hs_name = ident } in
             let ctx1, params = Lists.map_fold_left (type_param tuc) ctx d.pdefn_params in
             let writes = [] in
             add_hdl h writes params acc)
          ctx d in

      let ctx1, def = Lists.map_fold_left (type_defn tuc) ctt d in
      let e = type_prog ~loc:(e.pexpr_loc) tuc ctx1 e in
      Edef (e, false, def), []

  | PEdef (e, true, d) ->
      let ctx_up, def = Lists.map_fold_left (fun ctxup elt -> let up, e = type_defn tuc ctx elt in up,e ) ctx d in
      let e = type_prog ~loc:(e.pexpr_loc) tuc ctx_up e in
      Edef (e, true, def), []

  | PElam (pl, e) ->
    let ctx1, params = Lists.map_fold_left (type_param tuc) ctx pl in
    let e = type_prog ~loc:(e.pexpr_loc) tuc ctx1 e in
    Elam (params, e), params

and type_prog ?loc tuc ctx d =
  let e, te = type_expr tuc ctx d in
  if Stdlib.(<>) te [] then Loc.errorm ?loc "every programm must be box-typed";
  e

and type_defn tuc ctx {pdefn_desc=d; pdefn_loc=loc} =
  let id = d.pdefn_name in
  let ident = id_register (id_fresh ~loc:id.id_loc id.id_str) in
  let h = { hs_name = ident } in
  let ctx1, params = Lists.map_fold_left (type_param tuc) ctx d.pdefn_params in
  let writes = [] in
  let ctx1 = add_hdl h writes params ctx1 in (* allow recursion *)
  let e, pl = type_expr tuc ctx1 d.pdefn_body in

  if Stdlib.(<>) pl [] then Loc.errorm ~loc "handler %s is not fully applied" id.id_str;

  add_hdl h writes params ctx, (h, writes, params, e)

let mk_goal tuc s e =
  let prs = Decl.create_prsymbol (id_fresh ("vc_" ^ s)) in
  Theory.add_prop_decl tuc Decl.Pgoal prs (vc e)

let add_vc tuc (s, _, _, d) = mk_goal tuc s.hs_name.id_string d

let add_vcf tuc name d = mk_goal tuc name d

let parse_simpl_use env tuc = function
  | Duseimport (_, _, [Qdot (Qident l, m), None]) ->
      let th = Env.read_theory env [l.id_str] m.id_str in
      Theory.use_export tuc th
  | _ -> Loc.errorm "unhandled usage of `use'"

let read_channel env path file c =

  let uses, ast = Coma_lexer.parse_channel file c in

  let factor def e =
    { pexpr_desc = PEdef (e, false, [def]) ;
      pexpr_loc  = def.pdefn_loc ;
    } in

  let pastf =
    List.fold_right factor
      ast
      { pexpr_loc = Loc.dummy_position ; pexpr_desc = PEany }
  in

  let tuc = Theory.create_theory ~path (id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = List.fold_left (parse_simpl_use env) tuc uses in

  let astf = type_prog tuc ctx0 pastf in

  (* let _ctx, ast = Lists.map_fold_left (type_defn tuc) ctx0 ast in

  (* let ast = (create_hsymbol (id_fresh "dummy"), [], [], _expr2) :: ast in *)

  Format.printf "@[%a@]@."
    (fun fmt l ->
       Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
       (fun fmt d -> Coma_syntax.pp_def fmt d)
       fmt l)
    ast; 

  let tuc = List.fold_left add_vc tuc ast in *)

  let tuc = add_vcf tuc file astf in

  (* let tuc = mk_goal tuc "expr1" expr1 in *)
  (* let tuc = mk_goal tuc "expr2" expr2 in *)

  Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
