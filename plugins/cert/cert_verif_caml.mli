open Cert_syntax
open Cert_certificates

(** This checker uses an efficient computational approach *)
val checker_caml : kcert -> cterm ctask -> cterm ctask list -> unit
