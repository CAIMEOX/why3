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
Require Reals.R_sqrt.
Require BuiltIn.
Require real.Real.

(* Why3 goal *)
Lemma sqr'def :
  forall (x:Reals.Rdefinitions.R), ((Reals.RIneq.Rsqr x) = (x * x)%R).
Proof.
intros x.
reflexivity.
Qed.

Import R_sqrt.

(* Why3 comment *)
(* sqrt is replaced with (Reals.R_sqrt.sqrt x) by the coq driver *)

(* Why3 goal *)
Lemma Sqrt_positive :
  forall (x:Reals.Rdefinitions.R), (0%R <= x)%R ->
  (0%R <= (Reals.R_sqrt.sqrt x))%R.
intros x _.
apply sqrt_pos.
Qed.

(* Why3 goal *)
Lemma Sqrt_square :
  forall (x:Reals.Rdefinitions.R), (0%R <= x)%R ->
  ((Reals.RIneq.Rsqr (Reals.R_sqrt.sqrt x)) = x).
exact sqrt_sqrt.
Qed.

(* Why3 goal *)
Lemma Square_sqrt :
  forall (x:Reals.Rdefinitions.R), (0%R <= x)%R ->
  ((Reals.R_sqrt.sqrt (x * x)%R) = x).
exact sqrt_square.
Qed.

(* Why3 goal *)
Lemma Sqrt_mul :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  (0%R <= x)%R /\ (0%R <= y)%R ->
  ((Reals.R_sqrt.sqrt (x * y)%R) =
   ((Reals.R_sqrt.sqrt x) * (Reals.R_sqrt.sqrt y))%R).
intros x y (hx & hy); now apply sqrt_mult.
Qed.

(* Why3 goal *)
Lemma Sqrt_le :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  (0%R <= x)%R /\ (x <= y)%R ->
  ((Reals.R_sqrt.sqrt x) <= (Reals.R_sqrt.sqrt y))%R.
intros x y (h1 & h2); apply sqrt_le_1; auto.
apply Rle_trans with x; auto.
Qed.

