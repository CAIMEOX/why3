open Why3
open Decl
open Trans
open Task

open Cert_certificates

(** Certifying version of transformation normalize_hyp_or_goal from Compute *)
val compute :
  bool -> int option -> prsymbol option -> Env.env -> (task list * scert) trans
