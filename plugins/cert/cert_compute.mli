open Why3
open Decl
open Trans
open Task

open Cert_certificates

val ccompute :
  bool -> int option -> prsymbol option -> Env.env -> (task list * scert) trans
