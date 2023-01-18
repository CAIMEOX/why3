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

open Term
open Decl
open Ty
open Theory

let rec simp t =
  match t.t_node with
  | Tapp (ls, terms) ->
    let ls =
      try Mls.find ls mls with
      | Not_found -> ls
    in
    let terms = List.map rep terms in
    t_app_infer ls terms
  | Tif (t1, t2, t3) -> t_if (rep t1) (rep t2) (rep t3)
  | Tlet (term, term_bound) ->
    let vs, t = t_open_bound term_bound in
    let t = rep t in
    let term_bound = t_close_bound vs t in
    t_let (rep term) term_bound
  | Tcase (term, term_branchs) ->
    t_case (rep term)
      (List.map
         (fun branch ->
           let pat, t = t_open_branch branch in
           let t = rep t in
           t_close_branch pat t)
         term_branchs)
  | Teps term_bound ->
    let vs, t = t_open_bound term_bound in
    let t = rep t in
    let term_bound = t_close_bound vs t in
    t_eps term_bound
  | Tquant (quant, term_quant) ->
    let vs, trigger, t = t_open_quant term_quant in
    let t = rep t in
    let term_quant = t_close_quant vs trigger t in
    t_quant quant term_quant
  | Tbinop (binop, t1, t2) -> t_binary binop (rep t1) (rep t2)
  | Tnot term -> t_not (rep term)
  | _ -> t

let simplify d =
  match d.d_node with
  | Dprop (kind, _, f) ->
    let t = simp t in
    [ create_prop_decl kind pr t ]
  | _ -> [ d ]

let simplify_fn env =
  Trans.compose
    (Trans.lookup_transform "inline_trivial" env)
    (Trans.decl simplify None)

let () =
  Trans.register_env_transform "simplify_fn" simplify_fn
    ~desc:"Perform@ reduction@ of@ function@ application"
