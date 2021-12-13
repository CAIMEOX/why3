open Why3
open Term
open Ident
open Task
open Ty
open Format

(** Utility **)
val print_list : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val verif_failed : string -> 'a

(** Types for certifying transformations *)
type cbind = CTforall | CTexists | CTlambda
type ctype =
  | CTyvar of tvsymbol
  | CTprop
  | CTyapp of ident * ctype list
  | CTarrow of ctype * ctype

(** Interpreted types *)
val ctint : ctype
val ctreal : ctype
val ctbool : ctype

(** Utility functions on ctype *)
val cty_equal : ctype -> ctype -> bool
val find_vars : ctype -> Stv.t
val cty_ty_subst : ctype Mtv.t -> ctype -> ctype
val cty_same : ctype -> ctype -> bool
val is_predicate : ctype -> bool

(** Pretty printing of ctype (compatible with Lambdapi) *)
val ip : ident_printer
val prid : formatter -> ident -> unit
val prty : formatter -> ctype -> unit
val prty_paren : formatter -> ctype -> unit

(** Terms for certifying transformations *)
type cterm =
  | CTqtype of tvsymbol list * cterm
  | CTbvar of int
  | CTfvar of ident * ctype list
  | CTint of BigInt.t
  | CTapp of cterm * cterm
  | CTbinop of binop * cterm * cterm
  | CTbind of cbind * ctype * cterm
  | CTnot of cterm
  | CTtrue
  | CTfalse

(** Interpreted terms *)
val id_eq : ident
val id_true : ident
val id_false : ident
val le_str : string
val ge_str : string
val lt_str : string
val gt_str : string
val pl_str : string
val ml_str : string
val pre_mn_str : string
val inf_mn_str : string
val eq : ctype -> cterm

(** Utility functions on cterm *)
val ct_map : (cterm -> cterm) -> cterm -> cterm
val ct_equal : cterm -> cterm -> bool
val replace_cterm : cterm -> cterm -> cterm -> cterm
val ct_ty_subst : ctype Mtv.t -> cterm -> cterm
val ct_bv_subst : int -> cterm -> cterm -> cterm
val ct_open : cterm -> cterm -> cterm
val locally_closed : cterm -> bool
val ct_fv_subst : ident -> cterm -> cterm -> cterm
val ct_subst : cterm Mid.t -> cterm -> cterm
val ct_fv_close : ident -> int -> cterm -> cterm
val ct_close : ident -> cterm -> cterm

(** Pretty printing of terms (compatible with Lambdapi) *)
val prct : formatter -> cterm -> unit
val prquant : formatter -> cterm -> unit
val prarr : formatter -> cterm -> unit
val prdisj : formatter -> cterm -> unit
val prconj : formatter -> cterm -> unit
val prnot : formatter -> cterm -> unit
val prapp : formatter -> cterm -> unit
val prpv : formatter -> cterm -> unit

(** Tasks for certifying transformations *)
type 't ctask = {
    uid : ident;
    get_ls : string -> lsymbol;
    types_interp : Sid.t;
    types : Sid.t;
    sigma_interp : ctype Mid.t;
    sigma : ctype Mid.t;
    gamma_delta : ('t * bool) Mid.t;
  }

(** Pretty printing of ctask *)
val hip : ident_printer
val prhyp : formatter -> ident -> unit
val practa : formatter -> cterm ctask -> unit
val prcta : formatter -> term ctask -> unit
val eprlcta : cterm ctask -> cterm ctask list -> unit

(** Utility functions on ctask (used notably in the OCaml checker) *)
val ctask_equal : cterm ctask -> cterm ctask -> bool
val find_variable : string -> Mid.key -> 'a ctask -> ctype
val find_formula : string -> Mid.key -> 'a ctask -> 'a * bool
val ctask_new : (string -> lsymbol) -> Sid.t -> ctype Mid.t -> 'a ctask
val dummy_ctask : 'a -> 'b ctask
val add_type : Sid.elt -> 'a ctask -> 'a ctask
val add_var : Mid.key -> ctype -> 'a ctask -> 'a ctask
val remove_var : Mid.key -> 'a ctask -> 'a ctask
val remove : Mid.key -> 'a ctask -> 'a ctask
val add : Mid.key -> 'a * bool -> 'a ctask -> 'a ctask
val has_ident_context : ident -> cterm ctask -> bool

(** Typing algorithm *)
val type_matching : ctype Mtv.t -> ctype -> ctype -> ctype Mtv.t
val for_all2_type_matching :
  ctype Mtv.t -> ctype list -> ctype list -> ctype Mtv.t
val infer_type : 'a ctask -> cterm -> ctype
val well_typed : 'a ctask -> cterm -> unit
val infers_into : ?e_str:string -> 'a ctask -> cterm -> ctype -> unit

val instantiate : cterm -> cterm -> cterm
val instantiate_safe : 'a ctask -> cterm -> cterm -> cterm

(** Certifying transformations *)
type 'certif ctransformation = (task list * 'certif) Trans.trans
