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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require list.List.

(* Why3 comment *)
(* combine is replaced with (Lists.List.combine x x1) by the coq driver *)

(* Why3 goal *)
Lemma combine'def {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} :
  forall (x:Init.Datatypes.list a) (y:Init.Datatypes.list b),
  match (x, y) with
  | (Init.Datatypes.cons x0 x1, Init.Datatypes.cons y0 y1) =>
      ((Lists.List.combine x y) =
       (Init.Datatypes.cons (x0, y0) (Lists.List.combine x1 y1)))
  | _ => ((Lists.List.combine x y) = Init.Datatypes.nil)
  end.
Proof.
now intros [|xh xt] [|yh yt].
Qed.

