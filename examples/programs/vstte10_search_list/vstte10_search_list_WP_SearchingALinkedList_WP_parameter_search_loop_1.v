(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require int.Int.

(* Why3 assumption *)
Definition unit  := unit.

Parameter qtmark : Type.

Parameter at1: forall (a:Type), a -> qtmark -> a.
Implicit Arguments at1.

Parameter old: forall (a:Type), a -> a.
Implicit Arguments old.

(* Why3 assumption *)
Definition implb(x:bool) (y:bool): bool := match (x,
  y) with
  | (true, false) => false
  | (_, _) => true
  end.

(* Why3 assumption *)
Inductive list (a:Type) :=
  | Nil : list a
  | Cons : a -> (list a) -> list a.
Set Contextual Implicit.
Implicit Arguments Nil.
Unset Contextual Implicit.
Implicit Arguments Cons.

(* Why3 assumption *)
Set Implicit Arguments.
Fixpoint length (a:Type)(l:(list a)) {struct l}: Z :=
  match l with
  | Nil => 0%Z
  | (Cons _ r) => (1%Z + (length r))%Z
  end.
Unset Implicit Arguments.

Axiom Length_nonnegative : forall (a:Type), forall (l:(list a)),
  (0%Z <= (length l))%Z.

Axiom Length_nil : forall (a:Type), forall (l:(list a)),
  ((length l) = 0%Z) <-> (l = (Nil :(list a))).

(* Why3 assumption *)
Inductive option (a:Type) :=
  | None : option a
  | Some : a -> option a.
Set Contextual Implicit.
Implicit Arguments None.
Unset Contextual Implicit.
Implicit Arguments Some.

Parameter nth: forall (a:Type), Z -> (list a) -> (option a).
Implicit Arguments nth.

Axiom nth_def : forall (a:Type), forall (n:Z) (l:(list a)),
  match l with
  | Nil => ((nth n l) = (None :(option a)))
  | (Cons x r) => ((n = 0%Z) -> ((nth n l) = (Some x))) /\ ((~ (n = 0%Z)) ->
      ((nth n l) = (nth (n - 1%Z)%Z r)))
  end.

(* Why3 assumption *)
Definition zero_at(l:(list Z)) (i:Z): Prop := ((nth i l) = (Some 0%Z)) /\
  forall (j:Z), ((0%Z <= j)%Z /\ (j < i)%Z) -> ~ ((nth j l) = (Some 0%Z)).

(* Why3 assumption *)
Definition no_zero(l:(list Z)): Prop := forall (j:Z), ((0%Z <= j)%Z /\
  (j < (length l))%Z) -> ~ ((nth j l) = (Some 0%Z)).

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

(* Why3 assumption *)
Definition contents (a:Type)(v:(ref a)): a :=
  match v with
  | (mk_ref x) => x
  end.
Implicit Arguments contents.

(* Why3 assumption *)
Definition hd (a:Type)(l:(list a)): (option a) :=
  match l with
  | Nil => (None :(option a))
  | (Cons h _) => (Some h)
  end.
Implicit Arguments hd.

(* Why3 assumption *)
Definition tl (a:Type)(l:(list a)): (option (list a)) :=
  match l with
  | Nil => (None :(option (list a)))
  | (Cons _ t) => (Some t)
  end.
Implicit Arguments tl.



(* Why3 goal *)
Theorem WP_parameter_search_loop : forall (l:(list Z)), forall (s:(list Z)),
  forall (i:Z), ((0%Z <= i)%Z /\ (((i + (length s))%Z = (length l)) /\
  ((forall (j:Z), (0%Z <= j)%Z -> ((nth j s) = (nth (i + j)%Z l))) /\
  forall (j:Z), ((0%Z <= j)%Z /\ (j < i)%Z) -> ~ ((nth j
  l) = (Some 0%Z))))) -> ((~ (s = (Nil :(list Z)))) -> ((~ (s = (Nil :(list
  Z)))) -> forall (result:Z),
  match s with
  | Nil => False
  | (Cons h _) => (result = h)
  end -> ((result = 0%Z) -> ((((0%Z <= i)%Z /\ (i < (length l))%Z) /\
  (zero_at l i)) \/ ((i = (length l)) /\ (no_zero l)))))).
(* YOU MAY EDIT THE PROOF BELOW *)
intuition.
destruct s.
destruct H4.
subst; subst.
clear H0 H1.
left.
split.
replace (length (Cons 0 s))%Z with (1 + length s)%Z in H by auto.
generalize (Length_nonnegative _ s).
omega.
red; intuition.
assert (H0: (0 <= 0)%Z) by omega.
generalize (H3 0%Z H0).
generalize (nth_def _ 0%Z (Cons 0%Z s)).
ring_simplify (i+0)%Z.
intuition.
rewrite H4 in H1.
auto.
Qed.


