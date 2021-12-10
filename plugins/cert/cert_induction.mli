open Why3
open Term
open Trans
open Task

open Cert_certificates

val induction : term -> term option -> Env.env -> (task list * scert) trans
