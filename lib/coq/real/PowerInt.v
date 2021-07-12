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
Require Reals.Rfunctions.
Require BuiltIn.
Require int.Int.
Require real.Real.
Require real.RealInfix.

Require Import Lia.
Require Import Exponentiation.
Import Rfunctions.

(* Why3 comment *)
(* power is replaced with (Reals.Rfunctions.powerRZ x x1) by the coq driver *)

Lemma power_is_exponentiation :
  forall x n, (0 <= n)%Z -> powerRZ x n = Exponentiation.power _ R1 Rmult x n.
Proof.
intros x [|n|n] H.
easy.
2: now elim H.
unfold Exponentiation.power, powerRZ.
simpl.
induction (nat_of_P n).
easy.
simpl.
now rewrite IHn0.
Qed.

(* Why3 goal *)
Lemma Power_0 :
  forall (x:Reals.Rdefinitions.R), ((Reals.Rfunctions.powerRZ x 0%Z) = 1%R).
Proof.
intros x.
easy.
Qed.

(* Why3 goal *)
Lemma Power_s :
  forall (x:Reals.Rdefinitions.R) (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  ((Reals.Rfunctions.powerRZ x (n + 1%Z)%Z) =
   (x * (Reals.Rfunctions.powerRZ x n))%R).
Proof.
intros x n h1.
rewrite 2!power_is_exponentiation by auto with zarith.
now apply Power_s.
Qed.

(* Why3 goal *)
Lemma Power_s_alt :
  forall (x:Reals.Rdefinitions.R) (n:Numbers.BinNums.Z), (0%Z < n)%Z ->
  ((Reals.Rfunctions.powerRZ x n) =
   (x * (Reals.Rfunctions.powerRZ x (n - 1%Z)%Z))%R).
Proof.
intros x n h1.
rewrite <- Power_s.
apply f_equal.
ring.
lia.
Qed.

(* Why3 goal *)
Lemma Power_1 :
  forall (x:Reals.Rdefinitions.R), ((Reals.Rfunctions.powerRZ x 1%Z) = x).
Proof.
exact Rmult_1_r.
Qed.

(* Why3 goal *)
Lemma Power_sum :
  forall (x:Reals.Rdefinitions.R) (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= m)%Z ->
  ((Reals.Rfunctions.powerRZ x (n + m)%Z) =
   ((Reals.Rfunctions.powerRZ x n) * (Reals.Rfunctions.powerRZ x m))%R).
Proof.
intros x n m h1 h2.
rewrite 3!power_is_exponentiation by auto with zarith.
apply Power_sum ; auto with real.
Qed.

(* Why3 goal *)
Lemma Power_mult :
  forall (x:Reals.Rdefinitions.R) (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= m)%Z ->
  ((Reals.Rfunctions.powerRZ x (n * m)%Z) =
   (Reals.Rfunctions.powerRZ (Reals.Rfunctions.powerRZ x n) m)).
Proof.
intros x n m h1 h2.
rewrite 3!power_is_exponentiation by auto with zarith.
apply Power_mult ; auto with real.
Qed.

(* Why3 goal *)
Lemma Power_comm1 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((x * y)%R = (y * x)%R) -> forall (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  (((Reals.Rfunctions.powerRZ x n) * y)%R =
   (y * (Reals.Rfunctions.powerRZ x n))%R).
Proof.
intros x y h1 n h2.
apply Rmult_comm.
Qed.

(* Why3 goal *)
Lemma Power_comm2 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((x * y)%R = (y * x)%R) -> forall (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  ((Reals.Rfunctions.powerRZ (x * y)%R n) =
   ((Reals.Rfunctions.powerRZ x n) * (Reals.Rfunctions.powerRZ y n))%R).
Proof.
intros x y h1 n h2.
rewrite 3!power_is_exponentiation by auto with zarith.
apply Power_comm2 ; auto with real.
Qed.

(* Why3 goal *)
Lemma Pow_ge_one :
  forall (x:Reals.Rdefinitions.R) (n:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (1%R <= x)%R -> (1%R <= (Reals.Rfunctions.powerRZ x n))%R.
Proof.
intros x n (h1,h2).
generalize h1.
pattern n; apply Z_lt_induction; auto.
clear n h1; intros n Hind h1.
assert (h: (n = 0 \/ 0 < n)%Z) by lia.
destruct h.
subst n; rewrite Power_0; auto with *.
replace n with ((n-1)+1)%Z by ring.
rewrite Power_s; auto with zarith.
assert (h : (1 <= powerRZ x (n-1))%R).
apply Hind; lia.
replace 1%R with (1*1)%R by auto with real.
apply Rmult_le_compat; auto with real.
Qed.

