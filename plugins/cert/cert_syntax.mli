open Why3
open Term
open Ident
open Decl
open Task
open Ty
open Format

val print_list : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit

val verif_failed : string -> 'a

type cquant = CTforall | CTexists | CTlambda

type ctype =
  | CTyvar of tvsymbol
  | CTprop
  | CTyapp of ident * ctype list
  | CTarrow of ctype * ctype

val ctint : ctype
val ctreal : ctype
val ctbool : ctype
val cty_equal : ctype -> ctype -> bool

val find_vars : ctype -> Stv.t

val cty_ty_subst : ctype Mtv.t -> ctype -> ctype

val cty_same : ctype -> ctype -> bool

val is_predicate : ctype -> bool

val ip : ident_printer
val hip : ident_printer
val prid : formatter -> ident -> unit
val prhyp : formatter -> ident -> unit

val prls : formatter -> lsymbol -> unit
val prpr : formatter -> prsymbol -> unit
val prty : formatter -> ctype -> unit
val prty_paren : formatter -> ctype -> unit
val prdty : formatter -> ctype -> unit
val prdty_paren : formatter -> ctype -> unit

type cterm =
  | CTqtype of tvsymbol list * cterm
  | CTbvar of int
  | CTfvar of ident * ctype list
  | CTint of BigInt.t
  | CTapp of cterm * cterm
  | CTbinop of binop * cterm * cterm
  | CTquant of cquant * ctype * cterm
  | CTnot of cterm
  | CTtrue
  | CTfalse

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

val pcte : formatter -> cterm -> unit
val pquant : formatter -> cterm -> unit
val prarr : formatter -> cterm -> unit
val prdisj : formatter -> cterm -> unit
val prconj : formatter -> cterm -> unit
val prnot : formatter -> cterm -> unit
val prapp : formatter -> cterm -> unit
val prpv : formatter -> cterm -> unit

type 't ctask = {
    uid : ident;
    get_ls : string -> lsymbol;
    types_interp : Sid.t;
    types : Sid.t;
    sigma_interp : ctype Mid.t;
    sigma : ctype Mid.t;
    gamma_delta : ('t * bool) Mid.t;
  }

val pacta : formatter -> cterm ctask -> unit
val pcta : formatter -> term ctask -> unit
val eplcta : cterm ctask -> cterm ctask list -> unit

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

val has_ident_context : ident -> (cterm * 'a) Mid.t -> bool

val type_matching : ctype Mtv.t -> ctype -> ctype -> ctype Mtv.t
val for_all2_type_matching :
  ctype Mtv.t -> ctype list -> ctype list -> ctype Mtv.t
val infer_type : 'a ctask -> cterm -> ctype
val well_typed : 'a ctask -> cterm -> unit
val infers_into : ?e_str:string -> 'a ctask -> cterm -> ctype -> unit

val instantiate : cterm -> cterm -> cterm
val instantiate_safe : 'a ctask -> cterm -> cterm -> cterm

type 'certif ctransformation = (task list * 'certif) Trans.trans
