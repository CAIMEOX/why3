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
Require Reals.Rtrigo_def.
Require Reals.Rpower.
Require Reals.R_sqrt.
Require BuiltIn.
Require int.Int.
Require int.Power.
Require real.Real.
Require real.FromInt.
Require real.Square.
Require real.ExpLog.

Import Rpower.

(* Why3 comment *)
(* pow is replaced with (Reals.Rpower.Rpower x x1) by the coq driver *)

(* Why3 goal *)
Lemma Pow_def :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R), (0%R < x)%R ->
  ((Reals.Rpower.Rpower x y) =
   (Reals.Rtrigo_def.exp (y * (Reals.Rpower.ln x))%R)).
Proof.
easy.
Qed.

(* Why3 goal *)
Lemma Pow_pos :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R), (0%R < x)%R ->
  (0%R < (Reals.Rpower.Rpower x y))%R.
Proof.
intros x y h1.
apply Exp_prop.exp_pos.
Qed.

(* Why3 goal *)
Lemma Pow_plus :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R)
    (z:Reals.Rdefinitions.R),
  (0%R < z)%R ->
  ((Reals.Rpower.Rpower z (x + y)%R) =
   ((Reals.Rpower.Rpower z x) * (Reals.Rpower.Rpower z y))%R).
Proof.
intros x y z h1.
now apply Rpower_plus.
Qed.

(* Why3 goal *)
Lemma Pow_mult :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R)
    (z:Reals.Rdefinitions.R),
  (0%R < x)%R ->
  ((Reals.Rpower.Rpower (Reals.Rpower.Rpower x y) z) =
   (Reals.Rpower.Rpower x (y * z)%R)).
Proof.
intros x y z h1.
now apply Rpower_mult.
Qed.

(* Why3 goal *)
Lemma Pow_x_zero :
  forall (x:Reals.Rdefinitions.R), (0%R < x)%R ->
  ((Reals.Rpower.Rpower x 0%R) = 1%R).
Proof.
intros x h1.
now apply Rpower_O.
Qed.

(* Why3 goal *)
Lemma Pow_x_one :
  forall (x:Reals.Rdefinitions.R), (0%R < x)%R ->
  ((Reals.Rpower.Rpower x 1%R) = x).
Proof.
intros x h1.
now apply Rpower_1.
Qed.

(* Why3 goal *)
Lemma Pow_one_y :
  forall (y:Reals.Rdefinitions.R), ((Reals.Rpower.Rpower 1%R y) = 1%R).
Proof.
intros y.
unfold Rpower.
rewrite ln_1.
rewrite Rmult_0_r.
now apply  Rtrigo_def.exp_0.
Qed.

(* Why3 goal *)
Lemma Pow_x_two :
  forall (x:Reals.Rdefinitions.R), (0%R < x)%R ->
  ((Reals.Rpower.Rpower x 2%R) = (Reals.RIneq.Rsqr x)).
Proof.
intros x h1.
rewrite (Rpower_pow 2) by easy.
simpl.
now rewrite Rmult_1_r.
Qed.

(* Why3 goal *)
Lemma Pow_half :
  forall (x:Reals.Rdefinitions.R), (0%R < x)%R ->
  ((Reals.Rpower.Rpower x (1 / 2)%R) = (Reals.R_sqrt.sqrt x)).
Proof.
intros x h1.
unfold Rdiv. rewrite Rmult_1_l.
now apply Rpower_sqrt.
Qed.

(* Why3 goal *)
Lemma pow_from_int :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z), (0%Z < x)%Z ->
  (0%Z <= y)%Z ->
  ((Reals.Rpower.Rpower (BuiltIn.IZR x) (BuiltIn.IZR y)) =
   (BuiltIn.IZR (int.Power.power x y))).
Proof.
intros x y h1 h2.
rewrite <- Z2Nat.id with (1 := h2).
rewrite <- pow_IZR.
rewrite <- INR_IZR_INZ.
apply Rpower_pow.
now apply (IZR_lt 0).
Qed.

