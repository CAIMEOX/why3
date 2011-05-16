(* Beware! Only edit allowed sections below    *)
(* This file is generated by Why3's Coq driver *)
Require Import ZArith.
Require Import Rbase.
Parameter ghost : forall (a:Type), Type.

Definition unit  := unit.

Parameter ignore: forall (a:Type), a  -> unit.

Implicit Arguments ignore.

Parameter label_ : Type.

Parameter at1: forall (a:Type), a -> label_  -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a  -> a.

Implicit Arguments old.

Parameter power: Z -> Z  -> Z.


Axiom Power_0 : forall (x:Z), ((power x 0%Z) = 1%Z).

Axiom Power_s : forall (x:Z) (n:Z), (0%Z <  n)%Z -> ((power x
  n) = (x * (power x (n - 1%Z)%Z))%Z).

Axiom Power_1 : forall (x:Z), ((power x 1%Z) = x).

Theorem Power_sum : forall (x:Z) (n:Z) (m:Z), (0%Z <= n)%Z ->
  ((0%Z <= m)%Z -> ((power x (n + m)%Z) = ((power x n) * (power x m))%Z)).
(* YOU MAY EDIT THE PROOF BELOW *)
intros x n m Hn Hm.
generalize Hm.
pattern m.
apply Z_lt_induction; auto.
intros n0 Hind Hn0.
assert (h:(n0 = 0 \/ n0 > 0)%Z) by omega.
destruct h.
subst n0; rewrite Power_0; ring_simplify (n+0)%Z; ring.
rewrite Power_s; auto with zarith.
replace (n+n0-1)%Z with (n+(n0-1))%Z by omega.
rewrite Hind; auto with zarith.
rewrite (Power_s x n0).
ring.
omega.
Qed.
(* DO NOT EDIT BELOW *)


