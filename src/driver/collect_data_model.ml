(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Printer
open Smtv2_model_defs
open Model_parser

let debug_cntex = Debug.register_flag "cntex_collection"
    ~desc:"Intermediate representation debugging for counterexamples"

let is_true = function Const (Boolean true) -> true | _ -> false

type context = {
  (** Bindings for top-level constants and function parameters *)
  values: model_value Mstr.t;

  (** Top-level function definitions *)
  functions: function_def Mstr.t;

  (** Bindings for prover variables, mutable to cache values during evaluation *)
  prover_values: model_value Hstr.t;

  (** Don't interprete prover vars, which is required to make the case analysis
     in projection and field functions *)
  opaque_prover_vars: bool;

  (** Don't interprete (boolean) function applications *)
  as_constraint: bool;

  (** Other info fields *)
  fields_projs: Ident.ident Mstr.t;
  table: definition Mstr.t;
  pm: printer_mapping;
  list_records: string list Mstr.t;
}

(* let rec eval ctx oty t =
 *   Format.eprintf "@[<hv2>[EVAL %a %a@ (@[<h>%a@])@ (@[<h>%t@])@]@." Pp.(print_option string) oty print_term t Pp.(print_list space (print_pair string Model_parser.print_model_value_human)) (Mstr.bindings ctx.values)
 *     (fun fmt -> Hstr.iter (fun s -> Format.fprintf fmt "%s: %a, " s Model_parser.print_model_value_human) ctx.prover_values) ;
 *   let res = eval' ctx oty t in
 *   Format.eprintf "] -> %a@." Model_parser.print_model_value_human res;
 *   res *)

let rec eval ctx oty = function
  | Tconst c -> Const c
  | Tunparsed s -> Unparsed s
  | Tprover_var (ty, v) ->
      if ctx.opaque_prover_vars then
        Var v
      else
        Opt.get_def (Var v) (eval_prover_var ctx ty v)
  | Tvar v ->
      if List.mem v ctx.pm.noarg_constructors then
        Apply (v, [])
      else
        Mstr.find_def (Var v) v ctx.values
  | Tite (t1, t2, t3) ->
      if ctx.as_constraint then
        Ite (eval ctx None t1, eval ctx None t2, eval ctx None t3)
      else
      if is_true (eval ctx None t1) then eval ctx oty t2 else eval ctx oty t3
  | Tlet (bs, t) ->
      let aux values (s, t) = Mstr.add s (eval ctx None t) values in
      let values = List.fold_left aux ctx.values bs in
      eval {ctx with values} oty t
  | Tapply ("=", [t1; t2]) when not ctx.as_constraint ->
      Const (Boolean (eval ctx None t1 = eval ctx None t2))
  | Tapply ("or", ts) when not ctx.as_constraint ->
      Const (Boolean List.(exists is_true (map (eval ctx None) ts)))
  | Tapply ("and", ts) when not ctx.as_constraint ->
      Const (Boolean List.(for_all is_true (map (eval ctx None) ts)))
  | Tapply ("not", [t]) when not ctx.as_constraint -> (
      match eval ctx None t with
      | Const (Boolean b) -> Const (Boolean (not b))
      | t -> Apply ("not", [t]) )
  | Tapply (s, ts) -> (
      match Mstr.find_opt s ctx.list_records with
      | Some fs -> (* A record construction *)
          let ctx = {ctx with opaque_prover_vars= false} in
          Record List.(combine fs (map (eval ctx None (* TODO ty *)) ts))
      | None ->
          match Mstr.find_opt s ctx.functions with
          | Some fd -> (* A function call *)
              let bind_arg (v, s) t = Mstr.add v (eval ctx (Some s) t) in
              let values = List.fold_right2 bind_arg fd.params ts ctx.values in
              eval {ctx with values} (Some fd.sort) fd.body
          | None -> (* Cannot reduce *)
              Apply (s, List.map (eval ctx None) ts) )
  | Tarray a ->
      Array (eval_array {ctx with opaque_prover_vars= false} a)
  | Tas_array t ->
      Array (eval_as_array {ctx with opaque_prover_vars= false} t)

and eval_prover_var ctx ty v =
  assert (not ctx.opaque_prover_vars);
  try Some (Hstr.find ctx.prover_values v) with Not_found ->
    let res =
      (* Format.eprintf "EVAL PROVER VAR' %s %s@." ty v; *)
      let get_fields name = function
        | Dfunction {params= [param, ty']; sort; body}
        (* | Dfunction ([param, Some ty'], oty'', t) *)
          when Mstr.mem name ctx.fields_projs && ty' = ty -> (
            let values = Mstr.add param (Var v) ctx.values in
            match eval {ctx with values; opaque_prover_vars= true} (Some sort) body with
                | Var v -> eval_prover_var ctx sort v
                | mv -> Some mv )
        | _ -> None in
      let fs = Mstr.bindings (Mstr.mapi_filter get_fields ctx.table) in
      (* Format.eprintf "EVAL VAR %s %s: %a@." v ty Pp.(print_list space string) (List.map fst fs); *)
      (* Format.eprintf "FIELDS for %s: %a@." v
       *   Pp.(print_list space (print_pair string Model_parser.print_model_value)) fs; *)
      if fs = [] then
        None
      else if List.for_all (fun (f, _) -> Mstr.mem f ctx.pm.list_fields) fs then
        Some (Record fs)
      else (
        match List.find_opt (fun (f, _) -> Mstr.mem f ctx.pm.list_projections) fs with
        | Some (f, t) -> Some (Proj (f, t))
        | None -> None ) in
    Opt.iter (Hstr.add ctx.prover_values v) res;
    res

and eval_array ctx = function
  | Aconst t -> {arr_indices= []; arr_others= eval ctx None t}
  | Avar v -> Format.ksprintf failwith "eval_array var %s" v (*try Aconst (Mstr.find v bindings) with Not_found -> a*)
  | Astore (a, key, value) ->
      let a = eval_array ctx a in
      let key = eval ctx None key and value = eval ctx None value in
      {a with arr_indices= {arr_index_key= key; arr_index_value= value} :: a.arr_indices}

and eval_as_array ctx = function
  | Tvar v -> (
      match Mstr.find_opt v ctx.functions with
      | Some {params= [arg, key_sort]; sort= val_sort; body= t} ->
          let rec aux = function
            | Tite (Tapply ("=", [Tvar var; t1]), t2, t3) ->
                if var <> arg then Format.ksprintf failwith "eval_as_array %s - %s" arg var;
                let a = aux t3 in
                let ix = {
                    arr_index_key= eval ctx (Some key_sort) t1;
                    arr_index_value= eval ctx (Some val_sort) t2;
                  } in
                {a with arr_indices= ix :: a.arr_indices}
            | t -> {arr_others= eval ctx (Some val_sort) t; arr_indices= []} in
          aux t
      | _ -> Format.ksprintf failwith "eval_as_array: var %s" v )
  | Tarray a -> eval_array ctx a
  | t -> Format.kasprintf failwith "eval_as_array: term %a" print_term t

(************************************************************************)
(*            Import Smtv2_model_defs to model elements                 *)
(************************************************************************)

let create_list pm defs =

  let table, assts, dcld =
    let aux (table, assts, dcld) = function
      | Dfunction {name} as d ->
          Mstr.add name d table, assts, dcld
      | Ddecl_fun {name} | Ddecl_const {name} ->
          table, assts, Sstr.add name dcld
      | Dassert t -> table, t :: assts, dcld in
    List.fold_left aux (Mstr.empty, [], Sstr.empty) defs in

  (* Convert list_records to take replace fields with model_trace when necessary. *)
  let list_records =
    let select fi =
      if fi.field_trace <> "" then fi.field_trace else
        match fi.field_ident with
        | Some id -> id.Ident.id_string
        | None -> fi.field_name in
    Mstr.mapi (fun _ -> List.map select) pm.Printer.list_records in

  let print_def fmt (s, def) =
    Format.fprintf fmt "%s: %a" s print_definition def in
  Debug.dprintf debug_cntex "@[<hv2>Table: %a@]@."
    Pp.(print_list newline print_def) (Mstr.bindings table);

  let const_funcs =
    let aux = function
      | Dfunction r when r.params = [] -> Some (Some r.sort, r.body)
      | _ -> None in
    Mstr.map_filter aux table in

  let print_const_func fmt (s,(_,t)) = Format.fprintf fmt "%s: %a" s print_term t in
  Debug.dprintf debug_cntex "@[<hv2>Const funcs: %a@]@."
    Pp.(print_list newline print_const_func) (Mstr.bindings const_funcs);

  let just_function = function
    | Dfunction r when r.params <> [] -> Some r
    | _ -> None in
  let functions = Mstr.map_filter just_function table in

  let just_const_value = function Ddecl_const _ -> Some Constrained | _ -> None in
  let const_values = Mstr.map_filter just_const_value table in

  let print_const_value fmt (s,v) =
    Format.fprintf fmt "%s: %a" s print_model_value_human v in
  Debug.dprintf debug_cntex "@[<hov2>Const values:%a@]@."
    Pp.(print_list newline print_const_value) (Mstr.bindings const_values);

  let ctx =
    let fields_projs = fields_projs pm in
    let ctx = {functions; values= const_values; prover_values= Hstr.create 5; pm;
               fields_projs; table; list_records; opaque_prover_vars= false;
               as_constraint= false} in
    let const_funcs' = Mstr.map (fun (oty,t) -> eval ctx oty t) const_funcs in
    let aux _ _ _ = failwith "same name for const value and const func" in
    {ctx with values= Mstr.union aux const_funcs' const_values} in

  let eval_const_func (oty, t) = eval ctx oty t in
  let table = Mstr.map eval_const_func const_funcs in

  let print_mv fmt (s, mv) =
    Format.fprintf fmt "%s: %a" s print_model_value_human mv in
  Debug.dprintf debug_cntex "@[<hv2>Result: %a@]@."
    Pp.(print_list newline print_mv) (Mstr.bindings table);

  let cnstrs = List.map (eval {ctx with as_constraint= true} None) assts in

  Debug.dprintf debug_cntex "@[<hv2>Constraints: %a@]@."
    Pp.(print_list newline print_model_value_human) cnstrs;

  table, cnstrs, dcld
