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
Require Reals.Rbasic_fun.
Require BuiltIn.
Require real.Real.

Import Rbasic_fun.

(* Why3 comment *)
(* abs is replaced with (Reals.Rbasic_fun.Rabs x) by the coq driver *)

(* Why3 goal *)
Lemma abs'def :
  forall (x:Reals.Rdefinitions.R),
  ((0%R <= x)%R -> ((Reals.Rbasic_fun.Rabs x) = x)) /\
  (~ (0%R <= x)%R -> ((Reals.Rbasic_fun.Rabs x) = (-x)%R)).
Proof.
intros x.
split ; intros H.
apply Rabs_right.
now apply Rle_ge.
apply Rabs_left.
now apply Rnot_le_lt.
Qed.

(* Why3 goal *)
Lemma Abs_le :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((Reals.Rbasic_fun.Rabs x) <= y)%R <-> ((-y)%R <= x)%R /\ (x <= y)%R.
intros x y.
unfold Rabs.
case Rcase_abs ; intros H ; (split ; [intros H0;split | intros (H0,H1)]).
rewrite <- (Ropp_involutive x).
now apply Ropp_le_contravar.
apply Rlt_le.
apply Rlt_le_trans with (1 := H).
apply Rle_trans with (2 := H0).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite <- (Ropp_involutive y).
now apply Ropp_le_contravar.
apply Rge_le in H.
apply Rle_trans with (2 := H).
apply Rle_trans with (Ropp x).
now apply Ropp_le_contravar.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
exact H0.
exact H1.
Qed.

(* Why3 goal *)
Lemma Abs_pos :
  forall (x:Reals.Rdefinitions.R), (0%R <= (Reals.Rbasic_fun.Rabs x))%R.
exact Rabs_pos.
Qed.

(* Why3 goal *)
Lemma Abs_sum :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((Reals.Rbasic_fun.Rabs (x + y)%R) <=
   ((Reals.Rbasic_fun.Rabs x) + (Reals.Rbasic_fun.Rabs y))%R)%R.
exact Rabs_triang.
Qed.

(* Why3 goal *)
Lemma Abs_prod :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((Reals.Rbasic_fun.Rabs (x * y)%R) =
   ((Reals.Rbasic_fun.Rabs x) * (Reals.Rbasic_fun.Rabs y))%R).
exact Rabs_mult.
Qed.

(* Why3 goal *)
Lemma triangular_inequality :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R)
    (z:Reals.Rdefinitions.R),
  ((Reals.Rbasic_fun.Rabs (x - z)%R) <=
   ((Reals.Rbasic_fun.Rabs (x - y)%R) + (Reals.Rbasic_fun.Rabs (y - z)%R))%R)%R.
intros x y z.
replace (x - z)%R with ((x - y) + (y - z))%R by ring.
apply Rabs_triang.
Qed.

