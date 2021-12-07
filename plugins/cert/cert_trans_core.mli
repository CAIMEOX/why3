open Why3
open Decl
open Term

open Cert_certificates

val tprint :
  bool -> bool -> prsymbol option -> ctrans

val assumption : ctrans

val contradict : ctrans

val crename : prsymbol -> ctrans

val close : ctrans

val destruct_all : bool -> bool -> prsymbol option -> ctrans

val intro : bool -> bool -> prsymbol option -> ctrans

val cdir : bool -> prsymbol option -> ctrans

val cassert : term -> ctrans

val inst : term -> prsymbol option -> ctrans

val exfalso : ctrans

val case : term -> ctrans

val swap : prsymbol option -> ctrans

val revert : lsymbol -> ctrans

val trivial : ctrans

val intros : ctrans

val split_logic : bool -> bool -> prsymbol option -> ctrans

val blast : ctrans

val clear : prsymbol list -> ctrans
