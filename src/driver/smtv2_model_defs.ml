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
open Model_parser

type ident = string

type sort = Sort of ident * sort list

type term =
  | Tconst of model_const
  | Tvar of ident
  | Tprover_var of sort * ident
  | Tapply of (string * term list)
  | Tarray of array
  | Tite of term * term * term
  | Tlet of (string * term) list * term
  | Tas_array of term
  | Tunparsed of string

and array =
  | Avar of ident (* Used by let-bindings only *)
  | Aconst of term
  | Astore of array * term * term

type function_def = {
  name: ident;
  params: (ident * sort) list;
  sort: sort;
  body: term
}

type definition =
  | Dfunction of function_def
  | Ddecl_fun of {
      name: ident;
      params: sort list;
      sort: sort;
    }
  | Ddecl_const of { name: ident; sort: sort }
  | Dassert of term

let add_element x (t: definition Mstr.t) =
  match x with
  | None -> t
  | Some (key, value) ->
      Mstr.add key value t

let rec subst var value = function
  | Tconst _ as t -> t
  | Tarray a -> Tarray (subst_array var value a)
  | Tvar v | Tprover_var (_, v) as t -> if v = var then value else t
  | Tlet (bs, t') as t ->
      if List.exists (fun (s,_) -> s = var) bs then t
      else Tlet (List.map (fun (s,t) -> s, subst var value t) bs, subst var value t')
  | Tite (t1, t2, t3) ->
    let t1 = subst var value t1 in
    let t2 = subst var value t2 in
    let t3 = subst var value t3 in
    Tite (t1, t2, t3)
  (* | Record (n, l) ->
   *   Record (n, List.map (fun (f, t) -> f, subst var value t) l) *)
  | Tas_array t -> Tas_array (subst var value t)
  | Tapply (s, lt) ->
    Tapply (s, List.map (subst var value) lt)
  | Tunparsed _ as t -> t

and subst_array var value = function
  | Avar v ->
    if v = var then
      match value with
      | Tarray a -> a
      | _ -> Avar v
    else
      Avar v
  | Aconst t -> Aconst (subst var value t)
  | Astore (a, t1, t2) ->
      let t1 = subst var value t1 in
      let t2 = subst var value t2 in
      let a = subst_array var value a in
      Astore (a, t1, t2)

let substitute l t =
  List.fold_left (fun t (var, value) -> subst var value t) t l


(************************************************************************)
(*                              Printing                                *)
(************************************************************************)

let rec print_sort fmt (Sort (id, args)) =
  if args = [] then Pp.string fmt id else
    Format.fprintf fmt "%s%a" id Pp.(print_list space print_sort) args

let rec print_term fmt = let open Format in function
  | Tconst v -> print_model_const_human fmt v
  | Tapply (s, lt) ->
      fprintf fmt "@[<hv2>(Apply %s %a)@]" s
        Pp.(print_list space print_term) lt
  | Tarray a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Tvar v -> fprintf fmt "(Var %s)" v
  | Tprover_var (sort,v) -> fprintf fmt "(Prover_var %s:%a)" v print_sort sort
  | Tlet (bs, t) ->
      let print_binding fmt (s,t) = fprintf fmt "(%s %a)" s print_term t in
      fprintf fmt "(Let (%a) %a)" Pp.(print_list space print_binding) bs print_term t
  | Tite (cond, tthen, telse) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a)@]"
        print_term cond print_term tthen print_term telse
  (* | Record (n, l) ->
   *     fprintf fmt "@[<hv2>(Record %s %a)@]" n
   *       Pp.(print_list semi (fun fmt (x, a) -> fprintf fmt "(%s, %a)" x print_term a)) l *)
  | Tas_array t -> fprintf fmt "@[<hv2>(As_array %a)@]" print_term t
  | Tunparsed s -> fprintf fmt "(UNPARSED %s)" s

and print_array fmt = function
  | Avar v -> Format.fprintf fmt "@[<hv2>(Avar %s)@]" v
  | Aconst t -> Format.fprintf fmt "@[<hv2>(Aconst %a)@]" print_term t
  | Astore (a, t1, t2) -> Format.fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
                            print_array a print_term t1 print_term t2

and print_definition fmt =
  let open Format in function
    | Dfunction r ->
        fprintf fmt "@[<hv2>(define-fun %s (%a)@ %a@ %a)@]" r.name Pp.(print_list space string) (List.map fst r.params)
          print_sort r.sort print_term r.body
    | Ddecl_fun r ->
        fprintf fmt "@[<hv2>(declare-fun %s (%a)@ %a)@]" r.name
          Pp.(print_list space print_sort) r.params print_sort r.sort
    | Ddecl_const r ->
        fprintf fmt "@[<hv2>(declare-const %s@ %a)@]" r.name print_sort r.sort
    | Dassert t -> fprintf fmt "@[<hv2>(Dassert %a)@]" print_term t
