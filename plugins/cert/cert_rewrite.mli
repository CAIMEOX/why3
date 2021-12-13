open Why3
open Term
open Decl

open Cert_certificates

(** Certifying version of transformation rewrite from Apply *)
val rewrite : prsymbol -> bool -> term list option -> prsymbol option -> ctrans
