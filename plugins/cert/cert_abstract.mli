open Why3
open Term
open Task
open Ty

open Cert_syntax

(** Abstract Why3 type option into ctype *)
val abstract_otype : ty option -> ctype

(** Abstract Why3 term into cterm *)
val abstract_term : term -> cterm
val abstract_terms_ctask : term ctask -> cterm ctask

(** Abstracting Why3 task into ctask: extract only the logical core *)
val abstract_task : Env.env option -> task -> term ctask
