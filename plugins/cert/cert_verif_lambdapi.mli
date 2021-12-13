open Cert_syntax
open Cert_certificates

(** This checker relies on the superficial encoding of proof tasks into Lambdapi *)
val checker_lambdapi : kcert -> cterm ctask -> cterm ctask list -> unit
