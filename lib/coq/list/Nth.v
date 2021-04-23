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
Require list.List.
Require option.Option.

(* Why3 goal *)
Definition nth {a:Type} {a_WT:WhyType a} :
  Numbers.BinNums.Z -> Init.Datatypes.list a -> Init.Datatypes.option a.
exact (fix nth n l := match l with nil => None | cons h t => if Zeq_bool n Z0 then Some h else nth (n - 1)%Z t end).
Defined.

(* Why3 goal *)
Lemma nth'def {a:Type} {a_WT:WhyType a} :
  forall (n:Numbers.BinNums.Z) (l:Init.Datatypes.list a),
  match l with
  | Init.Datatypes.nil => ((nth n l) = Init.Datatypes.None)
  | Init.Datatypes.cons x r =>
      ((n = 0%Z) -> ((nth n l) = (Init.Datatypes.Some x))) /\
      (~ (n = 0%Z) -> ((nth n l) = (nth (n - 1%Z)%Z r)))
  end.
Proof.
intros n l.
revert n.
induction l.
easy.
intros n.
split.
intros ->.
easy.
simpl.
generalize (Zeq_bool_if n 0).
now case Zeq_bool.
Qed.

