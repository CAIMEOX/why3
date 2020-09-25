(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.

(* Why3 assumption *)
Definition unit := unit.

Parameter iter: forall {a:Type} {a_WT:WhyType a}, (a -> a) -> Z -> a -> a.

Axiom iter_def : forall {a:Type} {a_WT:WhyType a}, forall (f:(a -> a)) (k:Z)
  (x:a), (0%Z <= k)%Z -> (((k = 0%Z) -> ((iter f k x) = x)) /\
  ((~ (k = 0%Z)) -> ((iter f k x) = (iter f (k - 1%Z)%Z (f x))))).

Axiom iter_1 : forall {a:Type} {a_WT:WhyType a}, forall (f:(a -> a)) (x:a),
  ((iter f 1%Z x) = (f x)).

Axiom iter_s : forall {a:Type} {a_WT:WhyType a}, forall (f:(a -> a)) (k:Z)
  (x:a), (0%Z < k)%Z -> ((iter f k x) = (f (iter f (k - 1%Z)%Z x))).

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter eq: t -> t -> Prop.

Axiom eq_spec : forall (x:t) (y:t), (eq x y) <-> (x = y).

Parameter f: t -> t.

Parameter x0: t.

(* Why3 assumption *)
Definition x (i:Z): t := (iter (fun (y0:t) => (f y0)) i x0).

Parameter mu: Z.

Parameter lambda: Z.

Axiom mu_range : (0%Z <= mu)%Z.

Axiom lambda_range : (1%Z <= lambda)%Z.

Axiom distinct : forall (i:Z) (j:Z), ((0%Z <= i)%Z /\
  (i < (mu + lambda)%Z)%Z) -> (((0%Z <= j)%Z /\ (j < (mu + lambda)%Z)%Z) ->
  ((~ (i = j)) -> ~ ((x i) = (x j)))).

Axiom cycle : forall (n:Z), (mu <= n)%Z -> ((x (n + lambda)%Z) = (x n)).

(* Why3 goal *)
Theorem cycle_induction : forall (n:Z), (mu <= n)%Z -> forall (k:Z),
  (0%Z <= k)%Z -> ((x (n + (lambda * k)%Z)%Z) = (x n)).
(* Why3 intros n h1 k h2. *)
(* YOU MAY EDIT THE PROOF BELOW *)
intros n hn.
apply natlike_ind.
ring_simplify (n + lambda * 0)%Z; auto.
intros.
unfold Zsucc.
replace (n + lambda * (x1 + 1))%Z with ((n+lambda*x1)+lambda)%Z by ring.
rewrite cycle; auto.
assert (0 <= lambda * x1)%Z.
apply Zmult_le_0_compat; (generalize lambda_range; omega).
omega.
Qed.
