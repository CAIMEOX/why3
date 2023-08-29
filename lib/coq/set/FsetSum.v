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
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require set.Fset.

Require Import Lia.

(* Why3 goal *)
Definition sum {a:Type} {a_WT:WhyType a} :
  set.Fset.fset a -> (a -> Numbers.BinNums.Z) -> Numbers.BinNums.Z.
Proof.
intros fs conv.
destruct fs as (f, H).
(* We use the list to define the algorithm *)
eapply ClassicalEpsilon.constructive_indefinite_description in H.
destruct H as (l, H).
apply (List.fold_left (fun acc x => conv x + acc)%Z l 0%Z).
Defined.

(* Why3 goal *)
Lemma sum_def_empty {a:Type} {a_WT:WhyType a} :
  forall (s:set.Fset.fset a) (f:a -> Numbers.BinNums.Z),
  set.Fset.is_empty s -> ((sum s f) = 0%Z).
Proof.
intros s f h1.
unfold sum, Fset.is_empty, Fset.mem, set.Set.mem in *. destruct s.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct x0. 
+ reflexivity.
+ destruct a0. destruct (h1 a1).
  apply H0. left. reflexivity.
Qed.

Lemma fold_left_symm: forall {A} {B} l i s (conv: B -> A) 
  (Hsymm: forall a (b: A), s a b = s b a)
  (Hassoc: forall a b c, s (s a b) c = s a (s b c)) v,
  s (List.fold_left (fun acc x => s (conv x) acc) l i) v = 
  List.fold_left (fun acc x => s (conv x) acc) l (s i v).
Proof.
induction l; intros.
+ simpl. reflexivity.
+ simpl. rewrite IHl; eauto.
  rewrite Hassoc. reflexivity.
Qed.

Lemma fold_left_iff_symm: forall {A} {B} l l1 i (s: A -> A -> A) (conv: B -> A)
  (Hsymm: forall a b, s a b = s b a)
  (Hassoc: forall a b c, s (s a b) c = s a (s b c))
  (Heq: forall e, List.In e l <-> List.In e l1)
  (Hdup: List.NoDup l) (Hdup': List.NoDup l1),
  List.fold_left (fun acc x => s (conv x) acc) l i = 
  List.fold_left (fun acc x => s (conv x) acc) l1 i.
Proof.
induction l; intros.
+ destruct l1. reflexivity. specialize (Heq b). destruct Heq. destruct H0. 
  left. reflexivity.
+ simpl.
  destruct (List.in_split a l1) as [l1' [l1'' Hsplit]].
  - eapply Heq. left. reflexivity.
  - rewrite (IHl (List.app l1' l1'')); eauto.
    * rewrite Hsplit. rewrite List.fold_left_app.
      rewrite List.fold_left_app. simpl. rewrite (Hsymm (conv a) (List.fold_left _ _ _)). 
      rewrite fold_left_symm; eauto. rewrite Hsymm. reflexivity.
    * intros. rewrite List.in_app_iff. rewrite Hsplit in Heq.
      specialize (Heq e). rewrite List.in_app_iff in Heq. simpl in Heq.
      split; intros.
      ++ intuition. subst. inversion Hdup; intuition. subst. inversion Hdup; intuition.
      ++ destruct H. destruct Heq. assert (a = e \/ List.In e l). apply H1. auto. destruct H2; eauto. 
         subst. eapply List.NoDup_remove_2 in Hdup'. rewrite List.in_app_iff in Hdup'. destruct Hdup'; eauto.
         destruct Heq. assert (a = e \/ List.In e l). apply H1. auto. destruct H2; eauto. 
         subst. eapply List.NoDup_remove_2 in Hdup'. rewrite List.in_app_iff in Hdup'. destruct Hdup'; eauto.
    * inversion Hdup; auto.
    * rewrite Hsplit in Hdup'. eapply List.NoDup_remove_1; eauto.
Qed. 

(* Why3 goal *)
Lemma sum_add {a:Type} {a_WT:WhyType a} :
  forall (s:set.Fset.fset a) (f:a -> Numbers.BinNums.Z) (x:a),
  (set.Fset.mem x s -> ((sum (set.Fset.add x s) f) = (sum s f))) /\
  (~ set.Fset.mem x s ->
   ((sum (set.Fset.add x s) f) = ((sum s f) + (f x))%Z)).
Proof.
intros s f x.
unfold sum, Fset.mem, set.Set.mem, Fset.add.
destruct s as (sf, H).
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct a0 as (Hx0dup, Hx0eq). destruct a1 as (Hx1dup, Hx1eq).
split. intros.
+ eapply fold_left_iff_symm; eauto.
  * intuition.
  * intuition.
  * intros. rewrite Hx0eq. rewrite Hx1eq. unfold Map.set. 
    destruct why_decidable_eq; try subst; intuition.
+ intros.
  assert (List.In x x0). { eapply Hx0eq. unfold Map.set. destruct why_decidable_eq; eauto. }
  destruct (List.in_split x x0 H1) as [x0' [x0'' Hx0]].
  rewrite Hx0. rewrite List.fold_left_app. simpl. 
  rewrite (Zplus_comm (f x)). symmetry. 
  erewrite <- (fold_left_iff_symm (List.app x0' x0'')); eauto.
  * rewrite List.fold_left_app. rewrite fold_left_symm.
    ++ auto.
    ++ intuition.
    ++ intuition.
  * intuition.
  * intuition.
  * intros. rewrite List.in_app_iff. rewrite Hx0 in Hx0eq.
    specialize (Hx0eq e). rewrite List.in_app_iff in Hx0eq. simpl in Hx0eq.
    unfold Map.set in *. split; intros.
    ++ destruct H2.
       ** apply Hx1eq. destruct why_decidable_eq.
          -- subst. eapply List.NoDup_remove_2 in Hx0dup. intuition.
          -- intuition.
       ** eapply Hx1eq. destruct why_decidable_eq.
          -- subst. eapply List.NoDup_remove_2 in Hx0dup. intuition.
          -- intuition.
    ++ eapply Hx1eq in H2.
       destruct why_decidable_eq.
       -- subst. destruct H0. assumption.
       -- intuition.
  * rewrite Hx0 in Hx0dup. eapply List.NoDup_remove_1 in Hx0dup; eauto.
Qed.

(* Why3 goal *)
Lemma sum_remove {a:Type} {a_WT:WhyType a} :
  forall (s:set.Fset.fset a) (f:a -> Numbers.BinNums.Z) (x:a),
  (set.Fset.mem x s ->
   ((sum (set.Fset.remove x s) f) = ((sum s f) - (f x))%Z)) /\
  (~ set.Fset.mem x s -> ((sum (set.Fset.remove x s) f) = (sum s f))).
Proof.
intros s f x.
split; intros.
+ assert (s = Fset.add x (Fset.remove x s)).
  {
    apply Fset.extensionality. intro. rewrite Fset.add_remove; eauto. reflexivity.
  }
  rewrite H0 at 2. destruct (sum_add (Fset.remove x s) f x).
  rewrite H2. ring.
  rewrite Fset.remove_def. intuition.
+ assert (s = Fset.remove x s). 
  {
    apply Fset.extensionality. intro. 
    rewrite Fset.remove_def. intuition. subst. destruct H; assumption.
  }
  rewrite <- H0. reflexivity.
Qed.

Lemma sum_diff {a:Type} {a_WT:WhyType a} :
  forall (s1:set.Fset.fset a) (s2:set.Fset.fset a),
  forall (f:a -> Numbers.BinNums.Z),
  Fset.subset s1 s2 -> 
    (sum s2 f - sum s1 f = sum (set.Fset.diff s2 s1) f)%Z.
Proof.
intros.
assert (sum s2 f = sum (Fset.diff s2 s1) f + sum s1 f)%Z.
{
  unfold sum, Fset.diff, Fset.union, Fset.subset, Fset.disjoint, 
    Fset.inter, Fset.mem, set.Set.mem, Fset.add in *.
destruct s1 as (sf1, H1).
destruct s2 as (sf2, H2).
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct a1 as (Hdidup, Hdieq).
destruct a0 as (Hx0dup, Hx0eq).
destruct a2 as (Hx1dup, Hx1eq).
  rewrite fold_left_symm; try now intuition.
  rewrite Z.add_0_l. rewrite <- List.fold_left_app.
  eapply fold_left_iff_symm; eauto.
  + intuition.
  + intuition.
  + intros. rewrite List.in_app_iff. rewrite Hx1eq. rewrite Hx0eq.
    rewrite Hdieq. rewrite set.Set.diff'def. unfold set.Set.mem.
    split; intros.
    - destruct (Bool.bool_dec (sf1 e) true); intuition.
    - intuition.
  + eapply Cardinal.NoDup_app; eauto.
    - intros. rewrite Hx1eq in H0. rewrite Hdieq. rewrite set.Set.diff'def.
      intuition.
}
lia.
Qed.

Lemma sum_union_disj {a:Type} {a_WT:WhyType a} :
  forall (s1:set.Fset.fset a) (s2:set.Fset.fset a),
  forall (f:a -> Numbers.BinNums.Z)
    (Hdisj: set.Fset.disjoint s1 s2),
  (sum (set.Fset.union s1 s2) f) = ((sum s1 f) + (sum s2 f))%Z.
Proof.
intros s1 s2 f Hdisj.
unfold sum, Fset.union, Fset.disjoint, Fset.inter, Fset.mem, set.Set.mem, Fset.add in *.
destruct s1 as (sf1, H1).
destruct s2 as (sf2, H2).
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct ClassicalEpsilon.constructive_indefinite_description.
destruct a0 as (Hundup, Huneq).
destruct a1 as (Hx0dup, Hx0eq).
destruct a2 as (Hx1dup, Hx1eq).
  rewrite fold_left_symm; try now intuition.
  rewrite Z.add_0_l. rewrite <- List.fold_left_app.
  eapply fold_left_iff_symm; eauto.
  + intuition.
  + intuition.
  + intros. rewrite List.in_app_iff. rewrite Hx1eq. rewrite Hx0eq. rewrite Huneq.
    rewrite set.Set.union'def. clear - e. intuition.
  + eapply Cardinal.NoDup_app; eauto.
    * intros. intro. apply Hx0eq in H0. apply Hx1eq in H.
      specialize (Hdisj e). intuition.
Qed.

(* Why3 goal *)
Lemma sum_union {a:Type} {a_WT:WhyType a} :
  forall (s1:set.Fset.fset a) (s2:set.Fset.fset a),
  forall (f:a -> Numbers.BinNums.Z),
  ((sum (set.Fset.union s1 s2) f) =
   (((sum s1 f) + (sum s2 f))%Z - (sum (set.Fset.inter s1 s2) f))%Z).
Proof.
intros s1 s2 f.
assert (sum (Fset.union s1 s2) f - sum (Fset.inter s1 s2) f = 
  (sum s1 f - sum (Fset.inter s1 s2) f) + (sum s2 f - sum (Fset.inter s1 s2) f))%Z.
{
  rewrite sum_diff; [rewrite sum_diff; [rewrite sum_diff |] |].
  + assert (Fset.diff (Fset.union s1 s2) (Fset.inter s1 s2) = 
          Fset.union (Fset.diff s1 (Fset.inter s1 s2)) (Fset.diff s2 (Fset.inter s1 s2))).
    {
      eapply Fset.extensionality. intro e.
      rewrite Fset.union_def. rewrite Fset.diff_def. rewrite Fset.diff_def. rewrite Fset.diff_def.
      rewrite Fset.union_def. rewrite Fset.inter_def. intuition.
    }
    rewrite H.
    pose (s1' := Fset.diff s1 (Fset.inter s1 s2)). fold s1'.
    pose (s2' := Fset.diff s2 (Fset.inter s1 s2)). fold s2'.
    eapply sum_union_disj.
    unfold s1', s2'. intro. rewrite Fset.diff_def. rewrite Fset.diff_def.
    rewrite Fset.inter_def. tauto.
  + eapply Fset.subset_inter_2.
  + eapply Fset.subset_inter_1.
  + eapply Fset.subset_trans with s1. eapply Fset.subset_inter_1.
    eapply Fset.subset_union_1.
}
lia.
Qed.

(* Why3 goal *)
Lemma sum_eq {a:Type} {a_WT:WhyType a} :
  forall (s:set.Fset.fset a),
  forall (f:a -> Numbers.BinNums.Z) (g:a -> Numbers.BinNums.Z),
  (forall (x:a), set.Fset.mem x s -> ((f x) = (g x))) ->
  ((sum s f) = (sum s g)).
Proof.
intros s f g h1.
unfold sum, Fset.mem, set.Set.mem in *.
destruct s as (sf, H).
destruct ClassicalEpsilon.constructive_indefinite_description.
clear H.
assert (forall e, List.In e x -> f e = g e).
{
  intros. rewrite h1. reflexivity. apply a0. assumption.
}
assert (forall l (f: int -> a -> int) g a 
  (Heq: forall e acc, List.In e l -> f acc e = g acc e),
  List.fold_left f l a = List.fold_left g l a).
{
  induction l; simpl; intros; eauto.
  rewrite Heq; eauto.
}
erewrite H0; eauto. 
intros. simpl. rewrite H; eauto.
Qed.

(* Why3 goal *)
Lemma cardinal_is_sum {a:Type} {a_WT:WhyType a} :
  forall (s:set.Fset.fset a),
  ((set.Fset.cardinal s) = (sum s (fun (us:a) => 1%Z))).
Proof.
intros s.
unfold sum, Fset.mem, set.Set.mem, Fset.cardinal in *.
destruct s as (sf, H).
destruct ClassicalEpsilon.constructive_indefinite_description.
unfold Cardinal.cardinal.
destruct ClassicalEpsilon.excluded_middle_informative; [|intuition].
destruct ClassicalEpsilon.classical_indefinite_description.
specialize (a1 H).
assert (Z.of_nat (length x0) = Z.of_nat (length x)).
{
  erewrite (Cardinal.length_prop why_decidable_eq x nil x0); eauto.
  + simpl. rewrite Nat.sub_0_r. reflexivity.
  + apply a0.
  + constructor.
  + apply a1.
  + intros e Habs. inversion Habs.
  + intros. simpl. destruct a1, a0. rewrite H1, H3. intuition.
}
rewrite H0.
clear -x.
induction x; eauto.
assert (Z.of_nat (length (a0 :: x)) = Z.of_nat (length x) + 1)%Z.
simpl. rewrite Zpos_P_of_succ_nat. ring.
rewrite H.
rewrite IHx. rewrite @fold_left_symm; eauto.
intuition.
intuition.
Qed.

