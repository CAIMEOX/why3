open Why3
open Term
open Task
open Ty

open Cert_syntax

val abstract_otype : ty option -> ctype

val abstract_term : term -> cterm

val abstract_terms_task : term ctask -> cterm ctask

val abstract_task : Env.env option -> task -> term ctask
