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
Require int.Abs.

Require Import Zquot.

(* Why3 comment *)
(* div is replaced with (ZArith.BinInt.Z.quot x x1) by the coq driver *)

(* Why3 comment *)
(* mod1 is replaced with (ZArith.BinInt.Z.rem x x1) by the coq driver *)

(* Why3 goal *)
Lemma Div_mod :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z), ~ (y = 0%Z) ->
  (x = ((y * (ZArith.BinInt.Z.quot x y))%Z + (ZArith.BinInt.Z.rem x y))%Z).
intros x y _.
apply Z.quot_rem'.
Qed.

(* Why3 goal *)
Lemma Div_bound :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (0%Z <= x)%Z /\ (0%Z < y)%Z ->
  (0%Z <= (ZArith.BinInt.Z.quot x y))%Z /\
  ((ZArith.BinInt.Z.quot x y) <= x)%Z.
intros x y (Hx,Hy).
split.
now apply Z.quot_pos.
destruct (Z.eq_dec y 1) as [H|H].
rewrite H, Z.quot_1_r.
apply Z.le_refl.
destruct (Zle_lt_or_eq 0 x Hx) as [H'|H'].
apply Zlt_le_weak.
apply Z.quot_lt with (1 := H').
omega.
now rewrite <- H', Zquot_0_l.
Qed.

(* Why3 goal *)
Lemma Mod_bound :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z), ~ (y = 0%Z) ->
  ((-(ZArith.BinInt.Z.abs y))%Z < (ZArith.BinInt.Z.rem x y))%Z /\
  ((ZArith.BinInt.Z.rem x y) < (ZArith.BinInt.Z.abs y))%Z.
intros x y Zy.
destruct (Zle_or_lt 0 x) as [Hx|Hx].
refine ((fun H => conj (Z.lt_le_trans _ 0 _ _ (proj1 H)) (proj2 H)) _).
clear -Zy ; zify ; omega.
now apply Zrem_lt_pos.
refine ((fun H => conj (proj1 H) (Z.le_lt_trans _ 0 _ (proj2 H) _)) _).
clear -Zy ; zify ; omega.
apply Zrem_lt_neg with (2 := Zy).
now apply Zlt_le_weak.
Qed.

(* Why3 goal *)
Lemma Div_sign_pos :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (0%Z <= x)%Z /\ (0%Z < y)%Z -> (0%Z <= (ZArith.BinInt.Z.quot x y))%Z.
intros x y (Hx, Hy).
now apply Z.quot_pos.
Qed.

(* Why3 goal *)
Lemma Div_sign_neg :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (x <= 0%Z)%Z /\ (0%Z < y)%Z -> ((ZArith.BinInt.Z.quot x y) <= 0%Z)%Z.
intros x y (Hx, Hy).
generalize (Z.quot_pos (-x) y).
rewrite Zquot_opp_l.
omega.
Qed.

(* Why3 goal *)
Lemma Mod_sign_pos :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (0%Z <= x)%Z /\ ~ (y = 0%Z) -> (0%Z <= (ZArith.BinInt.Z.rem x y))%Z.
intros x y (Hx, Zy).
now apply Zrem_lt_pos.
Qed.

(* Why3 goal *)
Lemma Mod_sign_neg :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (x <= 0%Z)%Z /\ ~ (y = 0%Z) -> ((ZArith.BinInt.Z.rem x y) <= 0%Z)%Z.
intros x y (Hx, Zy).
now apply Zrem_lt_neg.
Qed.

(* Why3 goal *)
Lemma Rounds_toward_zero :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z), ~ (y = 0%Z) ->
  ((ZArith.BinInt.Z.abs ((ZArith.BinInt.Z.quot x y) * y)%Z) <=
   (ZArith.BinInt.Z.abs x))%Z.
intros x y Zy.
rewrite Zmult_comm.
zify.
generalize (Z.mul_quot_le x y).
generalize (Z.mul_quot_ge x y).
omega.
Qed.

(* Why3 goal *)
Lemma Div_1 :
  forall (x:Numbers.BinNums.Z), ((ZArith.BinInt.Z.quot x 1%Z) = x).
exact Z.quot_1_r.
Qed.

(* Why3 goal *)
Lemma Mod_1 :
  forall (x:Numbers.BinNums.Z), ((ZArith.BinInt.Z.rem x 1%Z) = 0%Z).
exact Z.rem_1_r.
Qed.

(* Why3 goal *)
Lemma Div_inf :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (0%Z <= x)%Z /\ (x < y)%Z -> ((ZArith.BinInt.Z.quot x y) = 0%Z).
exact Z.quot_small.
Qed.

(* Why3 goal *)
Lemma Mod_inf :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  (0%Z <= x)%Z /\ (x < y)%Z -> ((ZArith.BinInt.Z.rem x y) = x).
exact Z.rem_small.
Qed.

(* Why3 goal *)
Lemma Div_mult :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) (z:Numbers.BinNums.Z),
  (0%Z < x)%Z /\ (0%Z <= y)%Z /\ (0%Z <= z)%Z ->
  ((ZArith.BinInt.Z.quot ((x * y)%Z + z)%Z x) =
   (y + (ZArith.BinInt.Z.quot z x))%Z).
intros x y z (Hx&Hy&Hz).
rewrite (Zplus_comm y).
rewrite <- Z_quot_plus.
now rewrite Zplus_comm, Zmult_comm.
apply Zmult_le_0_compat with (2 := Hz).
apply Zplus_le_0_compat with (1 := Hz).
apply Zmult_le_0_compat with (1 := Hy).
now apply Zlt_le_weak.
intros H.
now rewrite H in Hx.
Qed.

(* Why3 goal *)
Lemma Mod_mult :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) (z:Numbers.BinNums.Z),
  (0%Z < x)%Z /\ (0%Z <= y)%Z /\ (0%Z <= z)%Z ->
  ((ZArith.BinInt.Z.rem ((x * y)%Z + z)%Z x) = (ZArith.BinInt.Z.rem z x)).
intros x y z (Hx&Hy&Hz).
rewrite Zplus_comm, Zmult_comm.
apply Z_rem_plus.
apply Zmult_le_0_compat with (2 := Hz).
apply Zplus_le_0_compat with (1 := Hz).
apply Zmult_le_0_compat with (1 := Hy).
now apply Zlt_le_weak.
Qed.

