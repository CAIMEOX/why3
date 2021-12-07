open Why3
open Term
open Decl

open Cert_certificates

val rewrite : prsymbol -> bool -> term list option -> prsymbol option -> ctrans
