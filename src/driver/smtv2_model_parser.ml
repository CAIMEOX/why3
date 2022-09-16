(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Term
open Smtv2_model_defs

let debug =
  Debug.register_flag "smtv2_parser"
    ~desc:
      "Print@ debugging@ messages@ about@ parsing@ the@ SMTv2@ model@ for@ \
       counterexamples."

module FromStringToSexp = struct
  exception E of string

  let fix_CVC18_bug_on_float_constants =
    let r = Re.Str.regexp "\\((fp #b[01] #b[01]+ #b[01]+\\)" in
    fun s -> Re.Str.global_replace r "\\1)" s

  let parse_string str =
    Debug.dprintf debug "[parse_string] model_string = %s@." str;
    let lexbuf = Lexing.from_string str in
    try Sexp.read_list lexbuf
    with Sexp.Error -> (
      let msg =
        Format.sprintf "Cannot parse as S-expression at character %d"
          (Lexing.lexeme_start lexbuf)
      in
      (* workaround for CVC4 1.8 bug in printing float constants *)
      let str = fix_CVC18_bug_on_float_constants str in
      let lexbuf = Lexing.from_string str in
      try Sexp.read_list lexbuf with Sexp.Error -> raise (E msg))
end

module FromSexpToModel = struct
  open Sexp

  exception E of sexp * string

  let error sexp s = raise (E (sexp, s))
  let atom_error a s = raise (E (Atom a, s))

  let is_name_start = function
    | '_' | 'a' .. 'z' | 'A' .. 'Z' | '@' | '#' | '$' -> true
    | _ -> false

  let is_quoted s =
    String.length s > 2 && s.[0] = '|' && s.[String.length s - 1] = '|'

  let get_quoted s = String.sub s 1 (String.length s - 2)

  let is_string s =
    String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"'

  let get_string s = String.sub s 1 (String.length s - 2)

  let rec pp_sexp fmt = function
    | Atom s -> Format.pp_print_string fmt s
    | List l ->
        Format.fprintf fmt "@[@[<hv2>(%a@])@]" Pp.(print_list space pp_sexp) l

  let string_of_sexp = Format.asprintf "%a" pp_sexp
  let atom f = function Atom s -> f s | sexp -> error sexp "atom"

  let list f = function
    | List l -> List.map f l
    | Atom _ as sexp -> error sexp "list"

  let string = function
    | Atom s when is_string s -> get_string s
    | sexp -> error sexp "string"

  let bool = atom bool_of_string
  let int = atom int_of_string
  let bigint = atom BigInt.of_string

  let constant_int =
    atom @@ fun s ->
    try BigInt.of_string ("0b" ^ Strings.remove_prefix "#b" s)
    with _ -> (
      try BigInt.of_string ("0x" ^ Strings.remove_prefix "#x" s)
      with _ -> (
        try BigInt.of_string s with _ -> atom_error s "constant_int"))

  let minus_constant_int = function
    | List [ Atom "-"; i ] as sexp -> (
        try
          let i' = atom BigInt.of_string i in
          BigInt.minus i'
        with _ -> error sexp "minus_constant_int")
    | sexp -> error sexp "minus_constant_int"

  let constant_int sexp =
    try constant_int sexp
    with _ -> (
      try minus_constant_int sexp with _ -> error sexp "constant_int")

  let constant_dec =
    atom @@ fun s ->
    try
      Scanf.sscanf s "%[^.].%s" (fun s1 s2 ->
          let i1 = BigInt.of_string s1 and i2 = BigInt.of_string s2 in
          (i1, i2))
    with _ -> atom_error s "constant_dec"

  let minus_constant_dec = function
    | List [ Atom "-"; d ] ->
        let d1, d2 = constant_dec d in
        (BigInt.minus d1, d2)
    | sexp -> error sexp "minus_constant_dec"

  let constant_dec sexp =
    try constant_dec sexp
    with _ -> (
      try minus_constant_dec sexp with _ -> error sexp "constant_dec")

  let constant_fraction = function
    | List [ Atom "/"; n1; n2 ] ->
        let n1, n2 =
          try (constant_int n1, constant_int n2)
          with _ ->
            let d11, d12 = constant_dec n1 and d21, d22 = constant_dec n2 in
            assert (BigInt.(eq d12 zero && eq d22 zero));
            (d11, d21)
        in
        (n1, n2)
    | sexp -> error sexp "constant_fraction"

  let bv_int =
    atom @@ fun s ->
    try BigInt.of_string (Strings.remove_prefix "bv" s)
    with _ -> atom_error s "bv_int"

  let constant_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#b" s in
          let v = BigInt.of_string ("0b" ^ s') in
          let l = String.length s' in
          (v, l)
        with _ -> atom_error s "constant_bv_bin")
    | sexp -> error sexp "constant_bv_bin"

  let constant_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#x" s in
          let v = BigInt.of_string ("0x" ^ s') in
          let l = String.length s' * 4 in
          (v, l)
        with _ -> atom_error s "constant_bv_hex")
    | sexp -> error sexp "constant_bv_hex"

  let constant_bv_dec = function
    | List [ Atom "_"; n; l ] -> (bv_int n, int l)
    | sexp -> error sexp "constant_bv_dec"

  let constant_bv sexp =
    try constant_bv_dec sexp
    with _ -> (
      try constant_bv_hex sexp
      with _ -> (
        try constant_bv_bin sexp with _ -> error sexp "constant_bv"))

  let constant_float = function
    | List [ Atom "_"; Atom "+zero"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fpluszero
    | List [ Atom "_"; Atom "-zero"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fminuszero
    | List [ Atom "_"; Atom "+oo"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fplusinfinity
    | List [ Atom "_"; Atom "-oo"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fminusinfinity
    | List [ Atom "_"; Atom "NaN"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fnan
    | List [ Atom "fp"; sign; exp; mant ] ->
        let sign = constant_bv sign
        and exp = constant_bv exp
        and mant = constant_bv mant in
        Fnumber { sign; exp; mant }
    | sexp -> error sexp "constant_float"

  let constant sexp : term =
    let cst =
      try Cint (constant_int sexp)
      with _ -> (
        try Cdecimal (constant_dec sexp)
        with _ -> (
          try Cfraction (constant_fraction sexp)
          with _ -> (
            try Cbitvector (constant_bv sexp)
            with _ -> (
              try Cfloat (constant_float sexp)
              with _ -> (
                try Cbool (bool sexp)
                with _ -> (
                  try Cstring (string sexp) with _ -> error sexp "constant"))))))
    in
    Tconst cst

  let symbol : sexp -> symbol = function
    | Atom s when s = "" || is_name_start s.[0] -> s
    | Atom s when is_quoted s -> get_quoted s
    | sexp -> error sexp "symbol"

  let index sexp : index =
    try Idxnumeral (bigint sexp)
    with _ -> ( try Idxsymbol (symbol sexp) with _ -> error sexp "index")

  let identifier sexp : identifier =
    match sexp with
    | Atom "=" -> Isymbol "="
    | Atom _ -> Isymbol (symbol sexp)
    | List [ Atom "_"; s; List idx ] ->
        Iindexedsymbol (symbol s, List.map index idx)
    | sexp -> error sexp "identifier"

  let rec sort : sexp -> sort = function
    | Atom "String" -> Sstring
    | Atom "RegLan" -> Sreglan
    | Atom "Int" -> Sint
    | Atom "Real" -> Sreal
    | Atom "RoundingMode" -> Sroundingmode
    | Atom "Bool" -> Sbool
    | List [ Atom "_"; Atom "BitVec"; Atom n ] as sexp -> (
        try Sbitvec (int_of_string n) with _ -> error sexp "bitvector sort")
    | Atom "Float16" -> Sfloatingpoint (5, 11)
    | Atom "Float32" -> Sfloatingpoint (8, 24)
    | Atom "Float64" -> Sfloatingpoint (11, 53)
    | Atom "Float128" -> Sfloatingpoint (15, 113)
    | List [ Atom "_"; Atom "FloatingPoint"; Atom eb; Atom sb ] as sexp -> (
        try Sfloatingpoint (int_of_string eb, int_of_string sb)
        with _ -> error sexp "floatingpoint sort")
    | List [ Atom "Array"; s1; s2 ] -> Sarray (sort s1, sort s2)
    | Atom _ as sexp -> Ssimple (identifier sexp)
    | List (Atom n :: l) -> Smultiple (identifier (Atom n), List.map sort l)
    | sexp -> error sexp "sort"

  let qualified_identifier sexp : qual_identifier =
    match sexp with
    | Atom _ -> Qident (identifier sexp)
    | List [ Atom "as"; id; s ] -> Qannotident (identifier id, sort s)
    | sexp -> error sexp "qualified_identifier"

  let arg = function
    | List [ n; s ] -> (symbol n, sort s)
    | sexp -> error sexp "arg"

  let rec term sexp =
    try constant sexp
    with _ -> (
      try Tvar (qualified_identifier sexp)
      with _ -> (
        try ite sexp
        with _ -> (
          try let_term sexp
          with _ -> (
            try array sexp
            with _ -> (
              try application sexp with _ -> Tunparsed (string_of_sexp sexp))))))

  and ite = function
    | List [ Atom "ite"; t1; t2; t3 ] -> Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and let_term = function
    | List [ Atom "let"; List bs; t ] -> Tlet (List.map var_binding bs, term t)
    | sexp -> error sexp "let_term"

  and var_binding = function
    | List [ Atom s; t ] -> (symbol (Atom s), term t)
    | sexp -> error sexp "var_binding"

  and application = function
    | List (qual_id :: ts) ->
        Tapply (qualified_identifier qual_id, List.map term ts)
    | sexp -> error sexp "application"

  and array sexp = match sexp with
    | List [ List [ Atom "as"; Atom "const"; List [ Atom "Array"; s1; s2] ]; t ] ->
        Tarray (sort s1, sort s2, {
          array_indices = [];
          array_others = term t;
        })
    (* TODO_WIP *)
    (*| List [ Atom "_"; Atom "as-array"; n ] ->
        Tvar (Qannotident (identifier n, Sarray))*)
    | List [ Atom "store"; x; t1; t2 ] ->
        let a = try array x with _ -> error sexp "array" (*Tvar (Qannotident (identifier x, Sarray))*) in
        begin match a with
        | Tarray (s1, s2, elts) -> Tarray (s1, s2, {
          array_indices = (term t1, term t2) :: elts.array_indices;
          array_others = elts.array_others
        })
        | _ -> error sexp "array"
        end
    | _ -> error sexp "array"

  let rec dt_symbols = function
    | [] -> []
    | List (Atom n :: _) :: tl -> n :: dt_symbols tl
    | _ :: tl -> dt_symbols tl (* TODO_WIP print warning *)

  let dt_decl : sexp -> datatype_decl option = function
    | List [ Atom "declare-datatype"; Atom n; List [ List symbols ] ] ->
        Some (sort (Atom n), dt_symbols symbols)
    | List
        [
          Atom "declare-datatypes";
          List [ List [ Atom n; Atom _ ] ];
          List [ List symbols ];
        ] ->
        Some (sort (Atom n), dt_symbols symbols)
    | _ -> None

  let fun_def : sexp -> (string * function_def) option = function
    | List [ Atom "define-fun"; Atom n; args; res; body ] ->
        let res = sort res in
        let args = list arg args and body = term body in
        Some (n, (args, res, body))
    | _ -> None

  let is_model_decl = function Atom "define-fun" -> true | _ -> false

<<<<<<< HEAD
  let model sexp =
    if sexp = [] then None else
    let decls, rest = match sexp with
      | List (Atom "model" :: decls) :: rest -> decls, rest
      | List decls :: rest when List.exists (Sexp.exists is_model_decl) decls ->
          decls, rest
      | _ -> failwith "Cannot read S-expression as model: model not first" in
    if List.exists (Sexp.exists is_model_decl) rest then
      failwith
        "Cannot read S-expression as model: next model not separated \
         (missing separator in driver?)";
    Some (Mstr.of_list (List.filter_map decl decls))
=======
  let get_and_check_model sexps =
    if sexps = [] then []
    else
      let model, rest =
        match sexps with
        | List (Atom "model" :: model) :: rest -> (model, rest)
        | List model :: rest when List.exists (Sexp.exists is_model_decl) model
          ->
            (model, rest)
        | _ -> failwith "Cannot read S-expression as model: model not first"
      in
      if List.exists (Sexp.exists is_model_decl) rest then
        failwith
          "Cannot read S-expression as model: next model not separated \
           (missing separator in driver?)"
      else model

  let get_fun_defs model =
    let fun_defs = Lists.map_filter fun_def model in
    Mstr.of_list fun_defs

  let get_dt_decls model = Lists.map_filter dt_decl model
>>>>>>> Cleanup
end

module FromModelToTerm = struct
  exception E of string

  let error s = raise (E s)

  type env = {
    (* Bound variables in the body of a function definiton. *)
    mutable vs : vsymbol list;
    (* Datatype declarations. *)
    dt : datatype_decl list;
    (* Known type symbols. *)
    mutable tys : Ty.tysymbol list;
  }

  let get_opt_type oty = match oty with None -> Ty.ty_bool | Some ty -> ty

  let rec smt_sort_to_ty env s =
    Debug.dprintf debug "[smt_sort_to_ty] s = %a@." print_sort s;
    match s with
    | Sstring -> Ty.ty_str
    | Sint -> Ty.ty_int
    | Sreal -> Ty.ty_real
    | Sbool -> Ty.ty_bool
    | Sarray (s1, s2) ->
        Ty.ty_app Ty.ts_func [ smt_sort_to_ty env s1; smt_sort_to_ty env s2 ]
    | Ssimple (Isymbol n) ->
      begin try
        Ty.ty_app
          (List.find (fun x -> String.equal n x.Ty.ts_name.id_string) env.tys)
          []
      with Not_found -> error "TODO_WIP smt_sort_to_ty unknown Ssimple symbol"
      end
    | Smultiple (Isymbol n, sorts) ->
      begin try
        Ty.ty_app
          (List.find (fun x -> String.equal n x.Ty.ts_name.id_string) env.tys)
          (List.map (smt_sort_to_ty env) sorts)
      with Not_found -> error "TODO_WIP smt_sort_to_ty unknown Smultiple symbol"
      end
    | _ -> error "TODO_WIP smt_sort_to_ty"

  let get_type_from_var_name name =
    (* we try to infer the type from [name], for example:
        - infer the type int32 from the name @uc_int32_1
        - infer the type ref int32 from the name |@uc_(ref int32)_0| *)
    if Strings.has_prefix "@" name then
      try
        let left = String.index name '_' + 1 in
        let right = String.rindex name '_' in
        let ty = String.sub name left (right - left) in
        Some
          (try Strings.(remove_prefix "(" (remove_suffix ")" ty)) with _ -> ty)
      with _ -> Some Strings.(remove_prefix "@" name)
    else
      match String.split_on_char '!' name with
      | [ ty; _; _ ] -> Some ty
      | _ -> None

  let qual_id_to_vsymbol env qid =
    Debug.dprintf debug "[qual_id_to_vsymbol] qid = %a@."
      print_qualified_identifier qid;
    match qid with
    | Qident (Isymbol n) -> (
        try List.find (fun vs -> String.equal n vs.vs_name.id_string) env.vs
        with Not_found ->
          let search_datatype (s, symbols) =
            match List.find_opt (fun n' -> String.equal n n') symbols with
            | None -> None
            | Some n' -> Some (smt_sort_to_ty env s)
          in
          let vs_ty =
            match Lists.map_filter search_datatype env.dt with
            | [ ty ] -> ty
            | _ -> (
                match get_type_from_var_name n with
                | Some ty_str ->
                    smt_sort_to_ty env (Ssimple (Isymbol ty_str))
                | None -> error "TODO_WIP cannot infer the type of the variable"
                )
          in
          create_vsymbol (Ident.id_fresh n) vs_ty)
    | Qannotident (Isymbol n, s) -> (
        try
          let vs =
            List.find (fun vs -> String.equal n vs.vs_name.id_string) env.vs
          in
          if Ty.ty_equal vs.vs_ty (smt_sort_to_ty env s) then vs
          else error "TODO_WIP type mismatch"
        with Not_found ->
          create_vsymbol (Ident.id_fresh n) (smt_sort_to_ty env s))
    | _ -> error "TODO_WIP_qual_id_to_vsymbol"

  let constant_to_term c =
    Debug.dprintf debug "[constant_to_term] c = %a@." print_constant c;
    match c with
    | Cint bigint -> t_const (Constant.int_const bigint) Ty.ty_int
    | Cbool b -> if b then t_bool_true else t_bool_false
    | Cstring str -> t_const (Constant.string_const str) Ty.ty_str
    | _ -> error "TODO_WIP constant_to_term"

  let rec term_to_term env t =
    Debug.dprintf debug "[term_to_term] t = %a@." print_term t;
    match t with
    | Tconst c -> constant_to_term c
    | Tvar qid ->
        Debug.dprintf debug "[term_to_term] vs.vs_ty = %a@."
          Pretty.print_ty (qual_id_to_vsymbol env qid).vs_ty;
        t_var (qual_id_to_vsymbol env qid)
    | Tite (b, t1, t2) ->
        t_if (term_to_term env b) (term_to_term env t1) (term_to_term env t2)
    | Tapply (qid, ts) -> apply_to_term env qid ts
    | Tlet (vs, t) -> error "TODO_WIP Tlet"
    | Tarray (s1, s2, a) -> array_to_term env s1 s2 a
    | Tunparsed s -> error "TODO_WIP Tunparsed"

  and apply_to_term env qid ts =
    Debug.dprintf debug "[apply_to_term] qid = %a@ ts = %a@."
      print_qualified_identifier qid
      Pp.(print_list space print_term)
      ts;
    match (qid, ts) with
    | Qident (Isymbol "="), [ t1; t2 ] ->
        let t' =
          t_bool_equ (term_to_term env t1) (term_to_term env t2)
        in
        Debug.dprintf debug "[apply_to_term] t'.t_ty = %a@."
          (Pp.print_option Pretty.print_ty) t'.t_ty;
        t'
    | Qident (Isymbol "not"), [ t ] -> t_bool_not (term_to_term env t)
    | Qident (Isymbol n), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ts'_ty =
          try List.map (fun t -> Opt.get t.t_ty) ts'
          with _ ->
            error "TODO_WIP apply_to_term error with types of arguments"
        in
        let search_datatype (s, symbols) =
          match List.find_opt (fun n' -> String.equal n n') symbols with
          | None -> None
          | Some n' -> Some (smt_sort_to_ty env s)
        in
        let ls_ty =
          match Lists.map_filter search_datatype env.dt with
          | [ ty ] -> Some ty
          | _ -> error "TODO_WIP error with ls_ty"
        in
        let ls = create_lsymbol (Ident.id_fresh n) ts'_ty ls_ty in
        t_app ls ts' ls.ls_value
    | Qannotident (Isymbol n, s), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ts'_ty =
          try List.map (fun t -> Opt.get t.t_ty) ts'
          with _ ->
            error "TODO_WIP apply_to_term error with types of arguments"
        in
        let ls =
          create_lsymbol (Ident.id_fresh n) ts'_ty
            (Some (smt_sort_to_ty env s))
        in
        t_app ls ts' ls.ls_value
    | _ -> error "TODO_WIP apply_to_term"

  and array_to_term env s1 s2 elts =
    Debug.dprintf debug "[array_to_term] a = %a@." print_array elts;
    let vs_arg =
      create_vsymbol (Ident.id_fresh "x") (smt_sort_to_ty env s1)
    in
    let mk_case key value t =
      let key = term_to_term env key in
      let value = term_to_term env value in
      t_if (t_equ (t_var vs_arg) key) value t
    in
    let a = List.fold_left
      (fun t (key,value) -> mk_case key value t)
      (term_to_term env elts.array_others)
      elts.array_indices
    in
    t_lambda [ vs_arg ] [] a

  let smt_term_to_term env t s =
    let t' = term_to_term env t in
    Debug.dprintf debug "[smt_term_to_term] type of s = %a, type of t' = %a@."
      Pretty.print_ty (smt_sort_to_ty env s)
      (Pp.print_option Pretty.print_ty)
      t'.t_ty;
    if Ty.ty_equal (smt_sort_to_ty env s) (get_opt_type t'.t_ty) then t'
    else error "TODO_WIP type error"

  let interpret_fun_def_to_term env ls oloc attrs fun_def =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[interpret_fun_def_to_term] fun_def = %a@."
      print_function_def fun_def;
    Debug.dprintf debug "[interpret_fun_def_to_term] ls = %a@." Pretty.print_ls
      ls;
    Debug.dprintf debug "[interpret_fun_def_to_term] ls.ls_value = %a@."
      (Pp.print_option Pretty.print_ty)
      ls.ls_value;
    List.iter
      (Debug.dprintf debug "[interpret_fun_def_to_term] ls.ls_args = %a@."
         Pretty.print_ty)
      ls.ls_args;
    (* Compute known type symbol variables from [ls] *)
    let tys =
      let types_in_ls =
        match ls.ls_value with
        | None -> ls.ls_args
        | Some ty -> ty :: ls.ls_args
      in
      List.fold_left
        (fun acc ty ->
          let f acc' sym = sym :: acc' in
          let symbols_in_ty = Ty.ty_s_fold f [] ty in
          List.concat [ acc; symbols_in_ty ])
        [] types_in_ls
    in
    (* Update the environment with [tys] while avoiding duplicates *)
    env.tys <- List.fold_left
      (fun acc tys ->
        match List.find_opt (fun tys' -> Ty.ts_equal tys tys') acc with
        | None -> tys::acc
        | Some _ -> acc)
      env.tys tys;
    let t =
      match fun_def with
      | [], res, body when ls.ls_args = [] ->
          let res_ty = smt_sort_to_ty env res in
          Debug.dprintf debug "[interpret_fun_def_to_term] res_ty = %a@."
            Pretty.print_ty res_ty;
          if ls.ls_value != None && Ty.ty_equal (Opt.get ls.ls_value) res_ty
          then smt_term_to_term env body res
          else error "TODO_WIP type mismatch"
      | [], _, _ -> error "TODO_WIP function arity mismatch"
      | args, res, body ->
          let res_ty = smt_sort_to_ty env res in
          let args_ty_list =
            List.map (fun (_, s) -> smt_sort_to_ty env s) args
          in
          Debug.dprintf debug "[interpret_fun_def_to_term] res_ty = %a@."
            Pretty.print_ty res_ty;
          List.iter
            (Debug.dprintf debug
               "[interpret_fun_def_to_term] args_ty_list = %a@." Pretty.print_ty)
            args_ty_list;
          if (* check if type of lsymbol matches type parsed from SMT model *)
            Ty.ty_equal (get_opt_type ls.ls_value) res_ty
            && List.fold_left2
                 (fun acc ty1 ty2 -> acc && Ty.ty_equal ty1 ty2)
                 true args_ty_list ls.ls_args
          then
            let vslist =
              List.map
                (fun (symbol, sort) ->
                  let name = Ident.id_fresh symbol in
                  create_vsymbol name (smt_sort_to_ty env sort))
                args
            in
            env.vs <- vslist;
            t_lambda vslist [] (smt_term_to_term env body res)
          else error "TODO_WIP type mismatch"
    in
    Debug.dprintf debug "[interpret_fun_def_to_term] t = %a@." Pretty.print_term
      t;
    Debug.dprintf debug "-----------------------------@.";
    t

  (* [eval_var] is false if variables should not be evaluated *)
  let rec eval_term eval_var ty_coercions t =
    Debug.dprintf debug "[eval_term] eval_var = %b, t = %a@."
      eval_var
      Pretty.print_term t;
    match t.t_node with
    (* TODO_WIP *)
    | Tvar vs -> (
      if eval_var then (
        match t.t_ty with
        | Some ty -> (
          (* first search if there exists some type coercions for [ty] *)
          match Ty.Mty.find_def [] ty ty_coercions with
          | [] -> t
          | (str',(ls',t'))::_ ->
            (* TODO_WIP handle multiple type coercions for a given [ty]
               by creating a conjunction formula *)
            let vs_list, _, t' = t_open_lambda t' in
            let vs = match vs_list with
              | [vs] -> vs
              | _ ->
                  error "TODO_WIP type coercion with not exactly one argument"
            in
            (* create a fresh vsymbol for the variable bound by the epsilon term *)
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            (* substitute [vs] by this new variable in the body [t'] of the function
               defining the type coercion *)
            let t' = t_subst_single vs (t_var x) t' in
            (* construct the formula to be used in the epsilon term *)
            let f =
              t_equ
                (t_app ls' [t_var x] ls'.ls_value)
                (eval_term false ty_coercions t')
            in
            (* replace [t] by [eps x. f] *)
            t_eps_close x f)
        | _ -> t)
      else
        t
    )
    | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
      if t_equal (eval_term eval_var ty_coercions t1) (eval_term eval_var ty_coercions t2) then
        t_bool_true
      else
        t_bool_false
    | Tapp (ls, ts) ->
      let ts = List.map (eval_term eval_var ty_coercions) ts in
      t_app ls ts ls.ls_value
    | Tif (b,t1,t2) -> (
      match (eval_term eval_var ty_coercions b).t_node with
      | Ttrue -> eval_term eval_var ty_coercions t1
      | _ -> eval_term eval_var ty_coercions t2
    )
    | _ -> t

  let eval (pinfo : Printer.printing_info) terms =
    let ty_coercions =
      Ty.Mty.map (* for each set [sls] of lsymbols associated to a type *)
        (fun sls ->
          (* we construct a list of elements [(str,(ls,t))] retrieved
             from [terms] such that [ls] is in [sls]:
             for a given type [ty], it corresponds to all type coercions
             that can be applied to an object of type [ty] *)
          List.concat (List.map
            (fun ls -> Mstr.bindings (
              Mstr.mapi_filter
                (fun str ((ls',_,_), t) ->
                  if ls_equal ls ls' then Some (ls,t) else None)
                terms))
            (Sls.elements sls))
        )
      pinfo.type_coercions in
    Ty.Mty.iter
      (fun key elt ->
        List.iter
          (fun (str,(ls,t)) ->
            Debug.dprintf debug "[ty_coercions] ty = %a, str=%s, ls = %a, t=%a@."
              Pretty.print_ty key
              str
              Pretty.print_ls ls
              Pretty.print_term t)
          elt)
      ty_coercions;
    Mstr.mapi (* for each element in [terms], we try to evaluate [t]:
       - by applying type coercions for variables, when possible *)
      (fun str ((ls,oloc,attrs),t) -> ((ls,oloc,attrs), eval_term true ty_coercions t))
      terms


  let get_terms (pinfo : Printer.printing_info)
      (dt_decls : datatype_decl list)
      (fun_defs : Smtv2_model_defs.function_def Mstr.t) =
    List.iter
      (Debug.dprintf debug "[dt_decls] %a@." print_datatype_decl)
      dt_decls;
    let qterms = pinfo.queried_terms in
    Mstr.iter
      (fun key (ls, _, _) ->
        Debug.dprintf debug "[queried_terms] key = %s, ls = %a@." key
          Pretty.print_ls ls)
      qterms;
    let records = pinfo.list_records in
    Mstr.iter
      (fun key l ->
        List.iter
          (fun finfo ->
            Debug.dprintf debug "[list_records] key = %s, field_info = %s@."
              key finfo.Printer.field_name)
          l)
      records;
    let fields = pinfo.list_fields in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_fields] key = %s, field = %s@."
          key f.Ident.id_string)
      fields;
    let projections = pinfo.list_projections in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_projections] key = %s, field = %s@."
          key f.Ident.id_string)
      projections;
    let env = { vs = []; dt = dt_decls; tys = [] } in
    let terms =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | (ls, oloc, attrs) ->
            Some ((ls,oloc,attrs), interpret_fun_def_to_term env ls oloc attrs def)
          | exception Not_found -> (
            Debug.dprintf debug "No term for %s@." n; None))
        fun_defs
    in
    Mstr.iter
      (fun n ((ls,_,_), t) ->
        Debug.dprintf debug
          "[get_terms] n = %s, ls = %a, t = %a@.t.t_ty = %a@.t.t_attrs = %a@.t.t_loc = \
           %a@."
          n
          Pretty.print_ls ls Pretty.print_term t
          (Pp.print_option Pretty.print_ty)
          t.t_ty Pretty.print_attrs t.t_attrs
          (Pp.print_option Pretty.print_loc_as_attribute)
          t.t_loc)
      terms;
    eval pinfo terms
end

(*
****************************************************************
**   Parser
****************************************************************
*)

let () =
  Exn_printer.register (* TODO_WIP more info in messages *) (fun fmt exn ->
      match exn with
      | FromStringToSexp.E msg ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ string@ to@ \
             S-expression:@ %s"
            msg
      | FromSexpToModel.E (sexp, s) ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ S-expression@ to@ model@ \
             definition:@ cannot@ read@ the@ following@ S-expression@ as@ %s:@ \
             %a"
            s FromSexpToModel.pp_sexp sexp
      | FromModelToTerm.E msg ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ model@ definition@ to@ \
             term:@ %s"
            msg
      | _ -> raise exn)

let get_model_string input =
  let nr = Re.Str.regexp "^)+" in
  let res = Re.Str.search_backward nr input (String.length input) in
  String.sub input 0 (res + String.length (Re.Str.matched_string input))

let parse pinfo input =
  match get_model_string input with
  | exception Not_found -> []
  | model_string ->
      let sexps = FromStringToSexp.parse_string model_string in
      let sexps = FromSexpToModel.get_and_check_model sexps in
      let fun_defs = FromSexpToModel.get_fun_defs sexps in
      let dt_decls = FromSexpToModel.get_dt_decls sexps in
      let terms = FromModelToTerm.get_terms pinfo dt_decls fun_defs in
      List.rev
        (Mstr.values
          (Mstr.mapi
            (fun n ((ls,oloc,attrs),t) ->
              let attrs = Mstr.find_def Ident.Sattr.empty n pinfo.Printer.set_str in
              let name = ls.ls_name.id_string in
              (* TODO_WIP parameter [name] because already
                 available with [lsymbol]?
                 Or the name should be something else? *)
              Model_parser.create_model_element
                ~name ~value:t ~oloc ~lsymbol:ls ~attrs)
            terms))

let () =
  Model_parser.register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
