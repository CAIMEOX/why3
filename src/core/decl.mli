(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Stdlib

(** Logic Declarations *)

open Ident
open Ty
open Term

(** {2 Type declaration} *)

type constructor = lsymbol * lsymbol option list
(** constructor symbol with the list of projections *)

type data_decl = tysymbol * constructor list

(** {2 Logic symbols declaration} *)

type ls_defn

type logic_decl = lsymbol * ls_defn

val make_ls_defn : lsymbol -> vsymbol list -> term -> logic_decl

val open_ls_defn : ls_defn -> vsymbol list * term

val open_ls_defn_cb : ls_defn -> vsymbol list * term *
                    (lsymbol -> vsymbol list -> term -> logic_decl)

val ls_defn_axiom : ls_defn -> term

val ls_defn_of_axiom : term -> logic_decl option
(** tries to reconstruct a definition from a defining axiom. Do not apply
    this to recursive definitions: it may successfully build a logic_decl,
    which will fail later because of non-assured termination *)

val ls_defn_decrease : ls_defn -> int list
(** [ls_defn_decrease ld] returns a list of argument positions
    (numbered from 0) that ensures a lexicographical structural
    descent for every recursive call. Triggers are ignored.

    NOTE: This is only meaningful if the [ls_defn] comes
    from a declaration; on the result of [make_ls_defn],
    [ls_defn_decrease] will always return an empty list. *)

(** {2 Inductive predicate declaration} *)

type prsymbol = private {
  pr_name : ident;
}

module Mpr : Map.S with type key = prsymbol
module Spr : Mpr.Set
module Hpr : Hashtbl.S with type key = prsymbol
module Wpr : Hashweak.S with type key = prsymbol

val create_prsymbol : preid -> prsymbol

val pr_equal : prsymbol -> prsymbol -> bool

val pr_hash : prsymbol -> int

type ind_decl = lsymbol * (prsymbol * term) list

type ind_sign = Ind | Coind

type ind_list = ind_sign * ind_decl list

(* Proposition declaration *)

type prop_kind =
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal     (* prove, do not use as a premise *)
  | Pskip     (* do not prove, do not use as a premise *)

type prop_decl = prop_kind * prsymbol * term

(** {2 Declaration type} *)

type decl = private {
  d_node : decl_node;
  d_syms : Sid.t;         (* idents used in declaration *)
  d_news : Sid.t;         (* idents introduced in declaration *)
  d_tag  : Hashweak.tag;  (* unique magical tag *)
}

and decl_node =
  | Dtype  of tysymbol          (* abstract types and aliases *)
  | Ddata  of data_decl list    (* recursive algebraic types *)
  | Dparam of lsymbol           (* abstract functions and predicates *)
  | Dlogic of logic_decl list   (* recursive functions and predicates *)
  | Dind   of ind_list          (* (co)inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)

module Mdecl : Map.S with type key = decl
module Sdecl : Mdecl.Set
module Wdecl : Hashweak.S with type key = decl
module Hdecl : Hashtbl.S  with type key = decl

val d_equal : decl -> decl -> bool
val d_hash : decl -> int

(** {2 Declaration constructors} *)

val create_ty_decl : tysymbol -> decl
val create_data_decl : data_decl list -> decl
val create_param_decl : lsymbol -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_sign -> ind_decl list -> decl
val create_prop_decl : prop_kind -> prsymbol -> term -> decl

(* exceptions *)

exception IllegalTypeAlias of tysymbol
exception NonPositiveTypeDecl of tysymbol * lsymbol * ty

exception InvalidIndDecl of lsymbol * prsymbol
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception NoTerminationProof of lsymbol
exception BadLogicDecl of lsymbol * lsymbol
exception UnboundVar of vsymbol
exception ClashIdent of ident

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

exception BadConstructor of lsymbol
exception BadRecordField of lsymbol
exception RecordFieldMissing of lsymbol * lsymbol
exception DuplicateRecordField of lsymbol * lsymbol

(** {2 Utilities} *)

val decl_map : (term -> term) -> decl -> decl

val decl_fold : ('a -> term -> 'a) -> 'a -> decl -> 'a

val decl_map_fold : ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl

module DeclTF : sig

  val decl_map : (term -> term) -> (term -> term) -> decl -> decl

  val decl_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> decl -> 'a

  val decl_map_fold : ('a -> term -> 'a * term) ->
                      ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl
end

(** {2 Known identifiers} *)

type known_map = decl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> decl -> known_map
val merge_known : known_map -> known_map -> known_map

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident
exception NonFoundedTypeDecl of tysymbol

val find_constructors : known_map -> tysymbol -> constructor list
val find_inductive_cases : known_map -> lsymbol -> (prsymbol * term) list
val find_logic_definition : known_map -> lsymbol -> ls_defn option
val find_prop : known_map -> prsymbol -> term
val find_prop_decl : known_map -> prsymbol -> prop_kind * term

(** Records *)

exception EmptyRecord

val parse_record :
  known_map -> (lsymbol * 'a) list -> lsymbol * lsymbol list * 'a Mls.t
(** [parse_record kn field_list] takes a list of record field assignments,
    checks it for well-formedness and returns the corresponding constructor,
    the full list of projection symbols, and the map from projection symbols
    to assigned values. *)

val make_record :
  known_map -> (lsymbol * term) list -> ty -> term

val make_record_update :
  known_map -> term -> (lsymbol * term) list -> ty -> term

val make_record_pattern :
  known_map -> (lsymbol * pattern) list -> ty -> pattern

