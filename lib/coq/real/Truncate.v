(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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
Require AnyFunction.
Require int.Int.
Require real.Real.
Require real.FromInt.

Require Import Flocq.Core.Core.
Require Import Lra.

(* Why3 goal *)
Notation truncate := Ztrunc.

(* Why3 goal *)
Lemma Truncate_int :
  forall (i:Numbers.BinNums.Z), ((truncate (BuiltIn.IZR i)) = i).
Proof.
  exact Ztrunc_IZR.
Qed.

(* Why3 goal *)
Lemma Truncate_down_pos :
  forall (x:Reals.Rdefinitions.R), (0%R <= x)%R ->
  ((BuiltIn.IZR (truncate x)) <= x)%R /\
  (x < (BuiltIn.IZR ((truncate x) + 1%Z)%Z))%R.
Proof.
  intros x h.
  rewrite (Ztrunc_floor x h).
  split.
  apply Zfloor_lb.
  rewrite plus_IZR; simpl.
  apply Zfloor_ub.
Qed.

(* Why3 goal *)
Lemma Truncate_up_neg :
  forall (x:Reals.Rdefinitions.R), (x <= 0%R)%R ->
  ((BuiltIn.IZR ((truncate x) - 1%Z)%Z) < x)%R /\
  (x <= (BuiltIn.IZR (truncate x)))%R.
Proof.
  intros x h.
  rewrite (Ztrunc_ceil x h).
  split;[|apply Zceil_ub].
  case (Req_dec (IZR (Zfloor x)) x); intro.
  rewrite <-H, Zceil_IZR, H, minus_IZR; simpl.
  lra.
  rewrite (Zceil_floor_neq _ H).
  rewrite minus_IZR, plus_IZR; simpl.
  pose proof (Zfloor_lb x).
  destruct (Rle_lt_or_eq_dec _ _ H0); try easy.
  lra.
Qed.

(* Why3 goal *)
Lemma Real_of_truncate :
  forall (x:Reals.Rdefinitions.R),
  ((x - 1%R)%R <= (BuiltIn.IZR (truncate x)))%R /\
  ((BuiltIn.IZR (truncate x)) <= (x + 1%R)%R)%R.
Proof.
  intro x.
  destruct (Rle_lt_dec x 0).
  + rewrite Ztrunc_ceil; auto.
    destruct (Req_dec (IZR (Zfloor x)) x).
    rewrite <-H at 2 3; rewrite Zceil_IZR, H; split; lra.
    rewrite Zceil_floor_neq; auto.
    pose proof (Zfloor_lb x);
      pose proof (Zfloor_ub x).
    rewrite plus_IZR; split; lra.
  + rewrite Ztrunc_floor by lra.
    pose proof (Zfloor_lb x);
      pose proof (Zfloor_ub x).
    split; lra.
Qed.

(* Why3 goal *)
Lemma Truncate_monotonic :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R), (x <= y)%R ->
  ((truncate x) <= (truncate y))%Z.
Proof.
  apply Ztrunc_le.
Qed.

(* Why3 goal *)
Lemma Truncate_monotonic_int1 :
  forall (x:Reals.Rdefinitions.R) (i:Numbers.BinNums.Z),
  (x <= (BuiltIn.IZR i))%R -> ((truncate x) <= i)%Z.
Proof.
  intros x i h.
  destruct (Rle_lt_dec x 0).
  + rewrite Ztrunc_ceil; auto.
    apply Zceil_glb; assumption.
  + rewrite Ztrunc_floor by lra.
    apply le_IZR.
    apply Rle_trans with (r2:=x);[apply Zfloor_lb|assumption].
Qed.

(* Why3 goal *)
Lemma Truncate_monotonic_int2 :
  forall (x:Reals.Rdefinitions.R) (i:Numbers.BinNums.Z),
  ((BuiltIn.IZR i) <= x)%R -> (i <= (truncate x))%Z.
Proof.
  intros x i h.
  destruct (Rle_lt_dec x 0).
  + rewrite Ztrunc_ceil; auto.
    apply le_IZR.
    apply Rle_trans with (r2:=x);[assumption|apply Zceil_ub].
  + rewrite Ztrunc_floor by lra.
    apply Zfloor_lub; assumption.
Qed.

(* Why3 goal *)
Notation floor := Zfloor.

(* Why3 goal *)
Notation ceil := Zceil.

(* Why3 goal *)
Lemma Floor_int :
  forall (i:Numbers.BinNums.Z), ((floor (BuiltIn.IZR i)) = i).
Proof.
  exact Zfloor_IZR.
Qed.

(* Why3 goal *)
Lemma Ceil_int : forall (i:Numbers.BinNums.Z), ((ceil (BuiltIn.IZR i)) = i).
Proof.
  exact Zceil_IZR.
Qed.

(* Why3 goal *)
Lemma Floor_down :
  forall (x:Reals.Rdefinitions.R),
  ((BuiltIn.IZR (floor x)) <= x)%R /\
  (x < (BuiltIn.IZR ((floor x) + 1%Z)%Z))%R.
Proof.
  intro x.
  split.
  apply Zfloor_lb.
  rewrite plus_IZR.
  apply Zfloor_ub.
Qed.

Lemma ceil_lb: forall x, ((IZR (ceil x) - 1) < x)%R.
Proof.
  intro.
  case (Req_dec (IZR (Zfloor x)) x); intro.
  rewrite <-H, Zceil_IZR, H; simpl; lra.
  rewrite (Zceil_floor_neq _ H).
  rewrite plus_IZR; simpl.
  pose proof (Zfloor_lb x).
  destruct (Rle_lt_or_eq_dec _ _ H0); try easy.
  lra.
Qed.

(* Why3 goal *)
Lemma Ceil_up :
  forall (x:Reals.Rdefinitions.R),
  ((BuiltIn.IZR ((ceil x) - 1%Z)%Z) < x)%R /\ (x <= (BuiltIn.IZR (ceil x)))%R.
Proof.
intro x.
split; [|apply Zceil_ub].
rewrite minus_IZR.
apply ceil_lb.
Qed.

(* Why3 goal *)
Lemma Floor_monotonic :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R), (x <= y)%R ->
  ((floor x) <= (floor y))%Z.
Proof.
  apply Zfloor_le.
Qed.

(* Why3 goal *)
Lemma Ceil_monotonic :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R), (x <= y)%R ->
  ((ceil x) <= (ceil y))%Z.
Proof.
  apply Zceil_le.
Qed.

