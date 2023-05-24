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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

Require Import Lia.

(* Why3 comment *)
(* abs is replaced with (ZArith.BinInt.Z.abs x) by the coq driver *)

(* Why3 goal *)
Lemma abs'def :
  forall (x:Numbers.BinNums.Z),
  ((x >= 0%Z)%Z -> ((ZArith.BinInt.Z.abs x) = x)) /\
  (~ (x >= 0%Z)%Z -> ((ZArith.BinInt.Z.abs x) = (-x)%Z)).
Proof.
intros x.
split ; intros H.
apply Z.abs_eq; auto with zarith.
apply Zabs_non_eq.
apply Znot_gt_le.
contradict H.
auto with zarith.
Qed.

(* Why3 goal *)
Lemma Abs_le :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  ((ZArith.BinInt.Z.abs x) <= y)%Z <-> ((-y)%Z <= x)%Z /\ (x <= y)%Z.
Proof.
intros x y.
lia.
Qed.

(* Why3 goal *)
Lemma Abs_pos :
  forall (x:Numbers.BinNums.Z), ((ZArith.BinInt.Z.abs x) >= 0%Z)%Z.
Proof.
auto with zarith.
Qed.

