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

Parameter ref : forall (a:Type), Type.

Definition sqr(x:Z): Z := (x * x)%Z.

Theorem WP_isqrt : forall (x:Z), (0%Z <= x)%Z -> forall (result:Z),
  (result = 0%Z) -> forall (result1:Z), (result1 = 1%Z) ->
  (((0%Z <= result)%Z /\ (((sqr result) <= x)%Z /\
  (result1 = (sqr (result + 1%Z)%Z)))) -> forall (sum:Z), forall (count:Z),
  ((0%Z <= count)%Z /\ (((sqr count) <= x)%Z /\
  (sum = (sqr (count + 1%Z)%Z)))) -> forall (result2:Z), (result2 = sum) ->
  ((result2 <= x)%Z -> forall (result3:Z), (result3 = count) ->
  forall (count1:Z), (count1 = (result3 + 1%Z)%Z) -> forall (result4:Z),
  (result4 = sum) -> forall (result5:Z), (result5 = count1) ->
  forall (sum1:Z), (sum1 = ((result4 + (2%Z * result5)%Z)%Z + 1%Z)%Z) ->
  (((0%Z <= count1)%Z /\ (((sqr count1) <= x)%Z /\
  (sum1 = (sqr (count1 + 1%Z)%Z)))) -> (0%Z <= (x - count)%Z)%Z))).
(* YOU MAY EDIT THE PROOF BELOW *)
intros.

Qed.
(* DO NOT EDIT BELOW *)


