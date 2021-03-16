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
Require int.Int.
Require list.List.
Require list.Nth.
Require option.Option.
Require list.HdTl.

(* Why3 goal *)
Lemma Nth_tl {a:Type} {a_WT:WhyType a} :
  forall (l1:Init.Datatypes.list a) (l2:Init.Datatypes.list a),
  ((list.HdTl.tl l1) = (Init.Datatypes.Some l2)) ->
  forall (i:Numbers.BinNums.Z), ~ (i = (-1%Z)%Z) ->
  ((list.Nth.nth i l2) = (list.Nth.nth (i + 1%Z)%Z l1)).
Proof.
intros [|x1 l1] l2 h1 i h2.
easy.
simpl.
generalize (Zeq_bool_if (i + 1) 0).
case Zeq_bool.
intro H.
exfalso.
omega.
intros _.
simpl in h1.
inversion h1.
apply (f_equal (fun i => Nth.nth i l2)).
exact (Zpred_succ i).
Qed.

(* Why3 goal *)
Lemma Nth0_head {a:Type} {a_WT:WhyType a} :
  forall (l:Init.Datatypes.list a), ((list.Nth.nth 0%Z l) = (list.HdTl.hd l)).
Proof.
now intros [|h t].
Qed.

