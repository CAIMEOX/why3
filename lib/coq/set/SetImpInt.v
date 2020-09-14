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
Require HighOrd.
Require AnyFunction.
Require int.Int.
Require set.Fset.
Require set.FsetInt.
Require set.SetImp.

(* Why3 goal *)
Definition set : Type.
Proof.
(* TODO find something more interesting. *)
apply bool.
Defined.

(* Why3 goal *)
Definition to_fset : set -> set.Fset.fset Numbers.BinNums.Z.
Proof.
(* TODO find something more interesting. *)
intros. exists (fun _ => false).
exists nil. intuition.
constructor. inversion H.
Defined.

(* Why3 goal *)
Definition choose : set -> Numbers.BinNums.Z.
Proof.
(* TODO find something more interesting. *)
intros. apply Z.zero.
Defined.

(* Why3 goal *)
Lemma choose'spec :
  forall (s:set), ~ set.Fset.is_empty (to_fset s) ->
  set.Fset.mem (choose s) (to_fset s).
Proof.
intros s h1.
destruct h1. unfold to_fset, Fset.is_empty, Fset.mem, set.Set.mem.
intuition.
Qed.

