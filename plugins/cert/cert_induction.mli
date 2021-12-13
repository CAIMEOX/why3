open Why3
open Term
open Trans
open Task

open Cert_certificates

(** Certifying version of transformation induction from Ind_itp *)
val induction : term -> term option -> Env.env -> (task list * scert) trans
