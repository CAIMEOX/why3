open Why3
open Decl
open Task
open Trans

open Cert_certificates

(** Operator to define new certifying transformations by composing certificates *)
val decl_cert : (decl -> decl list * scert) -> task -> task * scert
val decl_l_cert : (decl -> decl list list * scert) -> task -> task list * scert

(** Certifying identity transformation *)
val id_ctrans : ctrans

(** Combinators on transformations with a certificate *)
val compose : ctrans -> ctrans -> ctrans
val compose_list : ctrans list -> ctrans
val ite : (task list * scert) trans -> ctrans -> ctrans -> (task list * scert) trans
val try_close : ctrans list -> ctrans
val repeat : ctrans -> ctrans

(** Choose and update the "target": the set of declarations we focus on *)
type target = Pr of prsymbol | Everywhere | Anywhere | Nowhere
val default_goal : task -> prsymbol option -> prsymbol
val find_target : bool -> bool -> prsymbol option -> task -> target
val match_tg : target -> prsymbol -> bool
val update_tg_c : target * scert -> scert option -> target * scert

(** Define certificates independently from transformations *)
val revert_cert : prsymbol -> decl list -> scert
val intro_cert : prsymbol -> decl list -> scert
