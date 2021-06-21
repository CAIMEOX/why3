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
Require HighOrd.
Require int.Int.

Require Import ClassicalEpsilon Lia.
Require Logic.ProofIrrelevance.
Require set.Set set.Cardinal.

(* Why3 goal *)
Definition fset : forall (a:Type), Type.
Proof.
intros.
(* "apply (sig Cardinal.is_finite)." is not possible: a is not Why3Type *) 
apply (sig (fun (f: a -> bool) => exists l: List.list a, List.NoDup l /\ forall e, List.In e l <-> f e = true)).
Defined.

Global Instance set_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (fset a).
Proof.
intros.
split.
exists (fun _ => false).
exists nil. split; [ apply List.NoDup_nil | intuition; discriminate H ].
intros x y.
apply excluded_middle_informative.
Qed.

(* Why3 goal *)
Definition mem {a:Type} {a_WT:WhyType a} : a -> fset a -> Prop.
Proof.
intros. destruct X0 as (f, P).
apply (set.Set.mem X f).
Defined.

(* Why3 assumption *)
Definition infix_eqeq {a:Type} {a_WT:WhyType a} (s1:fset a) (s2:fset a) :
    Prop :=
  forall (x:a), mem x s1 <-> mem x s2.

(* Why3 goal *)
Lemma extensionality {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), infix_eqeq s1 s2 -> (s1 = s2).
Proof.
intros s1 s2 h1.
unfold infix_eqeq in h1. unfold mem in h1.
destruct s1, s2.
assert (x = x0).
eapply set.Set.extensionality. intro. eauto.
subst.
assert (e = e0).
(* TODO maybe provable on such property ? *)
apply Logic.ProofIrrelevance.proof_irrelevance.
subst. reflexivity.
Qed.

(* Why3 assumption *)
Definition subset {a:Type} {a_WT:WhyType a} (s1:fset a) (s2:fset a) : Prop :=
  forall (x:a), mem x s1 -> mem x s2.

(* Why3 goal *)
Lemma subset_refl {a:Type} {a_WT:WhyType a} : forall (s:fset a), subset s s.
Proof.
intros s.
destruct s. eapply set.Set.subset_refl.
Qed.

(* Why3 goal *)
Lemma subset_trans {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a) (s3:fset a), subset s1 s2 -> subset s2 s3 ->
  subset s1 s3.
Proof.
intros s1 s2 s3 h1 h2.
destruct s1, s2, s3.
eapply set.Set.subset_trans; eauto.
Qed.

(* Why3 assumption *)
Definition is_empty {a:Type} {a_WT:WhyType a} (s:fset a) : Prop :=
  forall (x:a), ~ mem x s.

(* Why3 goal *)
Definition empty {a:Type} {a_WT:WhyType a} : fset a.
Proof.
exists (fun x => false). 
apply Cardinal.is_finite_empty. unfold set.Set.is_empty.
unfold set.Set.mem. intuition.
Defined.

(* Why3 goal *)
Lemma is_empty_empty {a:Type} {a_WT:WhyType a} : is_empty (empty : fset a).
Proof.
unfold empty, is_empty, mem, set.Set.mem. intuition.
Qed.

(* Why3 goal *)
Lemma empty_is_empty {a:Type} {a_WT:WhyType a} :
  forall (s:fset a), is_empty s -> (s = (empty : fset a)).
Proof.
intros s h1.
eapply extensionality. intro. unfold empty, is_empty, mem, set.Set.mem in *.
destruct s. intuition. destruct (h1 _ H). 
Qed.

(* Why3 goal *)
Definition add {a:Type} {a_WT:WhyType a} : a -> fset a -> fset a.
Proof.
intros e f.
destruct f as (f, H).
exists (map.Map.set f e true).
apply Cardinal.is_finite_add. assumption.
Defined.

(* Why3 goal *)
Lemma add_def {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:fset a) (y:a), mem y (add x s) <-> mem y s \/ (y = x).
Proof.
intros x s y.
unfold mem. unfold add. destruct s.
unfold Map.set, set.Set.mem. destruct why_decidable_eq; intuition.
Qed.

(* Why3 goal *)
Lemma mem_singleton {a:Type} {a_WT:WhyType a} :
  forall (x:a) (y:a), mem y (add x (empty : fset a)) -> (y = x).
Proof.
intros x y h1.
unfold empty, mem, add, Map.set, set.Set.mem in *.
destruct why_decidable_eq; inversion h1; eauto.
Qed.

(* Why3 goal *)
Definition remove {a:Type} {a_WT:WhyType a} : a -> fset a -> fset a.
Proof.
intros e f.
destruct f as (f, H).
exists (Map.set f e false). eapply Cardinal.is_finite_remove.
assumption.
Defined.

(* Why3 goal *)
Lemma remove_def {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:fset a) (y:a), mem y (remove x s) <-> mem y s /\ ~ (y = x).
Proof.
intros x s y.
unfold mem, remove, set.Set.mem, Map.set. destruct s.
destruct why_decidable_eq; intuition.
Qed.

(* Why3 goal *)
Lemma add_remove {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:fset a), mem x s -> ((add x (remove x s)) = s).
Proof.
intros x s h1.
apply extensionality.
intro.
unfold mem, add, remove, mem in *.
destruct s.
rewrite set.Set.add_remove; eauto.
reflexivity.
Qed.

(* Why3 goal *)
Lemma remove_add {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:fset a), ((remove x (add x s)) = (remove x s)).
Proof.
intros x s.
apply extensionality.
intro.
unfold mem, add, remove in *.
destruct s.
rewrite set.Set.remove_add; eauto.
reflexivity.
Qed.

(* Why3 goal *)
Lemma subset_remove {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:fset a), subset (remove x s) s.
Proof.
intros x s.
unfold mem, remove in *.
destruct s.
apply set.Set.subset_remove; eauto.
Qed.

(* Why3 goal *)
Definition union {a:Type} {a_WT:WhyType a} : fset a -> fset a -> fset a.
Proof.
intros f1 f2.
destruct f1 as (f1, H1).
destruct f2 as (f2, H2).
exists (set.Set.union f1 f2). eapply Cardinal.is_finite_union; eauto.
Defined.

(* Why3 goal *)
Lemma union_def {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a) (x:a),
  mem x (union s1 s2) <-> mem x s1 \/ mem x s2.
Proof.
intros s1 s2 x.
unfold mem, union.
destruct s1, s2.
eapply set.Set.union'def.
Qed.

(* Why3 goal *)
Lemma subset_union_1 {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset s1 (union s1 s2).
Proof.
intros s1 s2.
unfold mem, union.
destruct s1, s2.
eapply set.Set.subset_union_1.
Qed.

(* Why3 goal *)
Lemma subset_union_2 {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset s2 (union s1 s2).
Proof.
intros s1 s2.
unfold mem, union.
destruct s1, s2.
eapply set.Set.subset_union_2.
Qed.

(* Why3 goal *)
Definition inter {a:Type} {a_WT:WhyType a} : fset a -> fset a -> fset a.
Proof.
intros f1 f2.
destruct f1 as (f1, H1).
destruct f2 as (f2, H2).
exists (set.Set.inter f1 f2). eapply Cardinal.is_finite_inter_left; eauto.
Defined.

(* Why3 goal *)
Lemma inter_def {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a) (x:a),
  mem x (inter s1 s2) <-> mem x s1 /\ mem x s2.
Proof.
intros s1 s2 x.
unfold mem, inter.
destruct s1, s2.
eapply set.Set.inter'def.
Qed.

(* Why3 goal *)
Lemma subset_inter_1 {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset (inter s1 s2) s1.
Proof.
intros s1 s2.
unfold mem, inter.
destruct s1, s2.
eapply set.Set.subset_inter_1.
Qed.

(* Why3 goal *)
Lemma subset_inter_2 {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset (inter s1 s2) s2.
Proof.
intros s1 s2.
unfold mem, inter.
destruct s1, s2.
eapply set.Set.subset_inter_2.
Qed.

(* Why3 goal *)
Definition diff {a:Type} {a_WT:WhyType a} : fset a -> fset a -> fset a.
Proof.
intros f1 f2.
destruct f1 as (f1, H1).
destruct f2 as (f2, H2).
exists (set.Set.diff f1 f2). eapply Cardinal.is_finite_diff; eauto.
Defined.

(* Why3 goal *)
Lemma diff_def {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a) (x:a),
  mem x (diff s1 s2) <-> mem x s1 /\ ~ mem x s2.
Proof.
intros s1 s2 x.
unfold mem, diff.
destruct s1, s2.
eapply set.Set.diff'def.
Qed.

(* Why3 goal *)
Lemma subset_diff {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset (diff s1 s2) s1.
Proof.
intros s1 s2.
unfold mem, diff.
destruct s1, s2.
eapply set.Set.subset_diff.
Qed.

(* Why3 goal *)
Definition pick {a:Type} {a_WT:WhyType a} : fset a -> a.
Proof.
intros f.
destruct f as (f, H).
apply (set.Set.pick f).
Defined.

(* Why3 goal *)
Lemma pick_def {a:Type} {a_WT:WhyType a} :
  forall (s:fset a), ~ is_empty s -> mem (pick s) s.
Proof.
intros s h1.
unfold mem, pick.
destruct s.
eapply set.Set.pick_def.
intuition.
Qed.

(* Why3 assumption *)
Definition disjoint {a:Type} {a_WT:WhyType a} (s1:fset a) (s2:fset a) : Prop :=
  forall (x:a), ~ mem x s1 \/ ~ mem x s2.

(* Why3 goal *)
Lemma disjoint_inter_empty {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), disjoint s1 s2 <-> is_empty (inter s1 s2).
Proof.
intros s1 s2.
unfold disjoint, mem, is_empty, inter.
destruct s1, s2.
simpl. eapply set.Set.disjoint_inter_empty.
Qed.

(* Why3 goal *)
Lemma disjoint_diff_eq {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), disjoint s1 s2 <-> ((diff s1 s2) = s1).
Proof.
intros s1 s2.
split; intros.
- apply extensionality. intro.
  unfold diff, disjoint, mem, is_empty, inter in *.
  destruct s1, s2.
  eapply set.Set.disjoint_diff_eq in H. rewrite H. reflexivity.
- assert (forall e, mem e (diff s1 s2) <-> mem e s1).
  rewrite H. intuition.
  clear H.
  unfold diff, disjoint, mem, is_empty, inter in *.
  destruct s1, s2.
  intros. apply set.Set.disjoint_diff_eq.
  apply set.Set.extensionality. intro. eapply H0.
Qed.

(* Why3 goal *)
Lemma disjoint_diff_s2 {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), disjoint (diff s1 s2) s2.
Proof.
intros s1 s2.
unfold disjoint, mem, is_empty, inter.
destruct s1, s2.
eapply set.Set.disjoint_diff_s2.
Qed.

Lemma filter_NoDup: forall {A} (l: list A) f, List.NoDup l -> List.NoDup (List.filter f l).
Proof.
induction l; intros.
- constructor.
- simpl. destruct (f a); eauto. econstructor; eauto.
  rewrite List.filter_In. intro. inversion H. intuition.
  eapply IHl; eauto. inversion H; eauto.
  eapply IHl. inversion H; eauto.
Qed.

(* Why3 goal *)
Definition filter {a:Type} {a_WT:WhyType a} :
  fset a -> (a -> Init.Datatypes.bool) -> fset a.
Proof.
intros s filter.
destruct s as (f, H).
exists (fun x => filter x && f x)%bool.
destruct H as (l, Hl).
exists (List.filter filter l).
split.
apply filter_NoDup; eauto. apply Hl.
intros.
rewrite List.filter_In. rewrite Bool.andb_true_iff. destruct Hl. rewrite H0. intuition.
Defined.

(* Why3 goal *)
Lemma filter_def {a:Type} {a_WT:WhyType a} :
  forall (s:fset a) (p:a -> Init.Datatypes.bool) (x:a),
  mem x (filter s p) <-> mem x s /\ ((p x) = Init.Datatypes.true).
Proof.
intros s p x.
unfold mem, filter.
destruct s. unfold set.Set.mem.
rewrite Bool.andb_true_iff. intuition.
Qed.

(* Why3 goal *)
Lemma subset_filter {a:Type} {a_WT:WhyType a} :
  forall (s:fset a) (p:a -> Init.Datatypes.bool), subset (filter s p) s.
Proof.
intros s p.
unfold subset, filter, mem, set.Set.mem.
destruct s.
intros.
rewrite Bool.andb_true_iff in H. intuition.
Qed.

(* Why3 goal *)
Definition map {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} :
  (a -> b) -> fset a -> fset b.
Proof.
intros map fs.
destruct fs as (fs, H).
exists (set.Set.map map fs).
eapply Cardinal.is_finite_map.
assumption.
Defined.

(* Why3 goal *)
Lemma map_def {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} :
  forall (f:a -> b) (u:fset a) (y:b),
  mem y (map f u) <-> (exists x:a, mem x u /\ (y = (f x))).
Proof.
intros f u y.
unfold map, mem.
destruct u.
eapply set.Set.map'def.
Qed.

(* Why3 goal *)
Lemma mem_map {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} :
  forall (f:a -> b) (u:fset a), forall (x:a), mem x u -> mem (f x) (map f u).
Proof.
intros f u x h1.
unfold map, mem.
destruct u.
eapply set.Set.mem_map.
assumption.
Qed.

(* Why3 goal *)
Definition cardinal {a:Type} {a_WT:WhyType a} : fset a -> Numbers.BinNums.Z.
Proof.
intros fs.
destruct fs as (fs, H).
eapply (Cardinal.cardinal fs).
Defined.

(* Why3 goal *)
Lemma cardinal_nonneg {a:Type} {a_WT:WhyType a} :
  forall (s:fset a), (0%Z <= (cardinal s))%Z.
Proof.
intros s.
unfold cardinal. destruct s.
eapply Cardinal.cardinal_nonneg.
Qed.

(* Why3 goal *)
Lemma cardinal_empty {a:Type} {a_WT:WhyType a} :
  forall (s:fset a), is_empty s <-> ((cardinal s) = 0%Z).
Proof.
intros s.
unfold cardinal. destruct s.
eapply Cardinal.cardinal_empty.
assumption.
Qed.

(* Why3 goal *)
Lemma cardinal_add {a:Type} {a_WT:WhyType a} :
  forall (x:a), forall (s:fset a),
  (mem x s -> ((cardinal (add x s)) = (cardinal s))) /\
  (~ mem x s -> ((cardinal (add x s)) = ((cardinal s) + 1%Z)%Z)).
Proof.
intros x s.
unfold cardinal. destruct s.
eapply Cardinal.cardinal_add.
assumption.
Qed.

(* Why3 goal *)
Lemma cardinal_remove {a:Type} {a_WT:WhyType a} :
  forall (x:a), forall (s:fset a),
  (mem x s -> ((cardinal (remove x s)) = ((cardinal s) - 1%Z)%Z)) /\
  (~ mem x s -> ((cardinal (remove x s)) = (cardinal s))).
Proof.
intros x s.
unfold cardinal. destruct s.
eapply Cardinal.cardinal_remove.
assumption.
Qed.

(* Why3 goal *)
Lemma cardinal_subset {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset s1 s2 ->
  ((cardinal s1) <= (cardinal s2))%Z.
Proof.
intros s1 s2 h1.
unfold cardinal. destruct s1, s2.
eapply Cardinal.cardinal_subset; assumption.
Qed.

(* Why3 goal *)
Lemma subset_eq {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), subset s1 s2 ->
  ((cardinal s1) = (cardinal s2)) -> (s1 = s2).
Proof.
intros s1 s2 h1 h2.
apply extensionality. intro.
unfold cardinal, subset, mem in *.
destruct s1, s2.
eapply Cardinal.subset_eq in h2; eauto.
rewrite h2. reflexivity.
Qed.

(* Why3 goal *)
Lemma cardinal1 {a:Type} {a_WT:WhyType a} :
  forall (s:fset a), ((cardinal s) = 1%Z) -> forall (x:a), mem x s ->
  (x = (pick s)).
Proof.
intros s h1 x h2.
unfold mem, pick in *.
destruct s.
eapply Cardinal.cardinal1; eauto.
Qed.

(* Why3 goal *)
Lemma cardinal_union {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a),
  ((cardinal (union s1 s2)) =
   (((cardinal s1) + (cardinal s2))%Z - (cardinal (inter s1 s2)))%Z).
Proof.
intros s1 s2.
unfold cardinal, union, inter in *.
destruct s1, s2.
eapply Cardinal.cardinal_union; eauto.
Qed.

(* Why3 goal *)
Lemma cardinal_inter_disjoint {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a), disjoint s1 s2 ->
  ((cardinal (inter s1 s2)) = 0%Z).
Proof.
intros s1 s2 h1.
unfold cardinal, inter, disjoint, mem in *.
destruct s1, s2.
eapply Cardinal.cardinal_inter_disjoint; eauto.
Qed.

(* Why3 goal *)
Lemma cardinal_diff {a:Type} {a_WT:WhyType a} :
  forall (s1:fset a) (s2:fset a),
  ((cardinal (diff s1 s2)) = ((cardinal s1) - (cardinal (inter s1 s2)))%Z).
Proof.
intros s1 s2.
unfold cardinal, inter, disjoint, mem in *.
destruct s1, s2.
eapply Cardinal.cardinal_diff; eauto.
Qed.

(* Why3 goal *)
Lemma cardinal_filter {a:Type} {a_WT:WhyType a} :
  forall (s:fset a) (p:a -> Init.Datatypes.bool),
  ((cardinal (filter s p)) <= (cardinal s))%Z.
Proof.
intros s p.
unfold cardinal, filter in *.
destruct s.
unfold Cardinal.cardinal.

destruct ClassicalEpsilon.excluded_middle_informative; [| intuition].
- destruct ClassicalEpsilon.classical_indefinite_description.
  destruct ClassicalEpsilon.excluded_middle_informative; [| intuition].
  destruct ClassicalEpsilon.classical_indefinite_description.
  specialize (a1 i0). specialize (a0 i).
  destruct a0, a1.
  assert (length x0 <= length x1).
  {
   eapply List.NoDup_incl_length; eauto.
   intro. intros. rewrite H2. rewrite H0 in H3. rewrite Bool.andb_true_iff in H3.
   apply H3.
  }
  lia.
- destruct ClassicalEpsilon.classical_indefinite_description.
  destruct ClassicalEpsilon.excluded_middle_informative; [| intuition].
  unfold Z.zero. lia.
Qed.

(* Why3 goal *)
Lemma cardinal_map {a:Type} {a_WT:WhyType a} {b:Type} {b_WT:WhyType b} :
  forall (f:a -> b) (s:fset a), ((cardinal (map f s)) <= (cardinal s))%Z.
Proof.
intros f s.
unfold cardinal, inter, disjoint, mem in *.
destruct s.
eapply Cardinal.cardinal_map; eauto.
Qed.

