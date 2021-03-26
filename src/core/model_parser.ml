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
open Format
open Term
open Ident
open Printer


let debug = Debug.register_info_flag "model_parser"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ \
         the@ counter-example@ model."

(*
***************************************************************
**  Counter-example model values
****************************************************************
*)

type model_element_kind =
  | Result
  | Old
  | At of string
  | Loop_before
  | Loop_before_iteration
  | Loop_current_iteration
  | Error_message
  | Other

let print_model_kind fmt = function
  | Result -> fprintf fmt "Result"
  | Old -> fprintf fmt "Old"
  | At l -> fprintf fmt "At %s" l
  | Error_message -> fprintf fmt "Error_message"
  | Loop_before -> fprintf fmt "Loop_before"
  | Loop_before_iteration -> fprintf fmt "Loop_before_iteration"
  | Loop_current_iteration -> fprintf fmt "Loop_current_iteration"
  | Other -> fprintf fmt "Other"

type model_element_name = {
  men_id: string option; (* Unique to a state and variable *)
  men_name: string; (* Shared between states of a variable *)
  men_kind: model_element_kind; (* Attributes associated to the id of the men *)
  men_attrs: Sattr.t;
  men_display: string option;
  men_field_chain: string list;
}

let display_name men =
  let head = match men.men_display with Some s -> s | None -> men.men_name in
  String.concat "." (head :: men.men_field_chain)
  (* asprintf "@[<h>%a%t@]"
   *   Pp.(print_list (constant_string ".") string) (head :: men.men_field_chain)
   *   (fun fmt -> Opt.iter (fprintf fmt " (%s)") men.men_id) *)

let why_display_name men =
  let name = display_name men in
  match men.men_kind with
  | Result -> "result"
  | Old -> "old "^name
  | At l -> name^" at "^l
  | Loop_before_iteration -> "[before iteration] "^name
  | Loop_current_iteration | Loop_before | Error_message | Other -> name

let json_display_name men =
  let name = display_name men in
  match men.men_kind with
  | Result -> "result"
  | Old -> "old "^name
  | _ -> name

type model_int = { int_value: BigInt.t; int_verbatim: string }
type model_dec = { dec_int: BigInt.t; dec_frac: BigInt.t; dec_verbatim: string }
type model_frac = { frac_nom: BigInt.t; frac_den: BigInt.t; frac_verbatim: string }
type model_bv = { bv_value: BigInt.t; bv_length: int; bv_verbatim: string }
type model_float_binary = { sign: model_bv; exp: model_bv; mant: model_bv }
type model_float =
  | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | Not_a_number
  | Float_number of {hex: string option; binary: model_float_binary}

type model_const =
  | Boolean of bool
  | String of string
  | Integer of model_int
  | Float of model_float
  | Bitvector of model_bv
  | Decimal of model_dec
  | Fraction of model_frac

type model_value =
  | Const of model_const
  | Array of model_array
  | Record of model_record
  | Proj of model_proj
  | Apply of string * model_value list
  | Ite of model_value * model_value * model_value
  | Var of string
  | Model_var of model_element_name
  | Constrained
  | Undefined
  | Unparsed of string

and arr_index = {arr_index_key: model_value; arr_index_value: model_value}

and model_array = {arr_others: model_value; arr_indices: arr_index list}

and model_record = (field_name * model_value) list

and model_proj = proj_name * model_value

and proj_name = string

and field_name = string

type model_constraint = model_value

let bv_compare v1 v2 = BigInt.compare v1.bv_value v2.bv_value

let float_compare f1 f2 = match f1, f2 with
  | Float_number {binary= b1}, Float_number {binary= b2} -> (
      match bv_compare b1.sign b2.sign with
      | 0 -> (
          match bv_compare b1.exp b2.exp with
          | 0 -> bv_compare b1.mant b2.mant
          | n -> n )
      | n -> n )
  | Float_number _, _ -> -1
  | _, Float_number _ -> 1
  | f1, f2 -> compare f1 f2

let compare_model_const c1 c2 = match c1, c2 with
  | Boolean b1, Boolean b2 -> compare b1 b2
  | Boolean _, _ -> -1 | _, Boolean _ -> 1
  | String s1, String s2 -> String.compare s1 s2
  | String _, _ -> -1 | _, String _ -> 1
  | Integer i1, Integer i2 -> BigInt.compare i1.int_value i2.int_value
  | Integer _, _ -> -1 | _, Integer _ -> 1
  | Float f1, Float f2 -> float_compare f1 f2
  | Float _, _ -> -1 | _, Float _ -> 1
  | Bitvector v1, Bitvector v2 -> bv_compare v1 v2
  | Bitvector _, _ -> -1 | _, Bitvector _ -> 1
  | Decimal d1, Decimal d2 ->
      (match BigInt.compare d1.dec_int d2.dec_int with
       | 0 -> BigInt.compare d1.dec_frac d2.dec_frac | n -> n)
  | Decimal _, _ -> -1 | _, Decimal _ -> 1
  | Fraction f1, Fraction f2 ->
      (match BigInt.compare f1.frac_nom f2.frac_nom with
       | 0 -> BigInt.compare f1.frac_den f2.frac_den | n -> n)

let compare_model_name_ids id1 id2 =
  match id1, id2 with
  | Some id1, Some id2 -> String.compare id1 id2
  | _ -> -1

let rec compare_model_value v1 v2 = match v1, v2 with
  | Const c1, Const c2 -> compare_model_const c1 c2
  | Const _, _ -> -1 | _, Const _ -> 1
  | Apply (f1, vs1), Apply (f2, vs2) ->
      (match String.compare f1 f2 with
       | 0 -> Lists.compare compare_model_value vs1 vs2 | n -> n)
  | Apply _, _ -> -1 | _, Apply _ -> 1
  | Model_var n1, Model_var n2 -> compare_model_name_ids n1.men_id n2.men_id
  | Model_var _, _ -> -1 | _, Model_var _ -> 1
  | Var v1, Var v2 -> String.compare v1 v2
  | Var _, _ -> -1 | _, Var _ -> 1
  | Constrained, Constrained -> 0
  | Constrained, _ -> -1 | _, Constrained -> 1
  | _ -> ksprintf failwith "compare_model_value %d/%d"
           Obj.(tag (repr v1)) Obj.(tag (repr v2))

let rec model_value_size v =
  let sum = List.fold_left (+) 0 in
  1 + match v with
  | Const _ -> 0
  | Array a ->
      let aux ix =
        model_value_size ix.arr_index_key +
        model_value_size ix.arr_index_value in
      model_value_size a.arr_others +
      sum (List.map aux a.arr_indices)
  | Record fs -> sum (List.map model_value_size (List.map snd fs))
  | Proj (_, v) -> model_value_size v
  | Apply (_, vs) -> sum (List.map model_value_size vs)
  | Constrained -> 0
  | Var _ | Model_var _ -> 0
  | Ite (v1, v2, v3) ->
    model_value_size v1 + model_value_size v2 + model_value_size v3
  | Undefined -> 0
  | Unparsed _ -> 0

let array_create_constant ~value = {arr_others= value; arr_indices= []}

let array_add_element ~array ~index ~value =
  (*
     Adds the element value to the array on specified index.
  *)
  let arr_index = {arr_index_key= index; arr_index_value= value} in
  {arr_others= array.arr_others; arr_indices= arr_index :: array.arr_indices}

let pad_with_zeros width s =
  let filled =
    let len = width - String.length s in
    if len <= 0 then "" else String.make len '0' in
  filled ^ s

(* (-) integer . fractional e (-) exponent *)
(* ?%d+.%d*E-?%d+ *)
(* 0X-?%x+.%x*P-?%d+ *)

let float_of_binary binary =
  try
    let open BigInt in
    let {sign; mant; exp} = binary in
    let exp_bias = pred (pow_int_pos 2 (exp.bv_length - 1)) in
    let exp_max = pred (pow_int_pos 2 exp.bv_length) in
    let frac_len = (* Length of the hexadecimal representation (after the ".") *)
      if mant.bv_length mod 4 = 0
      then mant.bv_length / 4
      else (mant.bv_length / 4) + 1 in
    let is_neg = match to_int sign.bv_value with 0 -> false | 1 -> true | _ -> raise Exit in
    (* Compute exponent (int) and frac (string of hexa) *)
    let frac =
      (* The hex value is used after the decimal point. So we need to adjust
         it to the number of binary elements there are.
         Example in 32bits: significand is 23 bits, and the hexadecimal
         representation will have a multiple of 4 bits (ie 24). So, we need to
         multiply by two to account the difference. *)
      if Strings.has_prefix "#b" mant.bv_verbatim then
        let adjust = 4 - (mant.bv_length mod 4) in
        if adjust = 4 then
          mant.bv_value (* No adjustment needed *)
        else
          mul (pow_int_pos 2 adjust) mant.bv_value
      else
        mant.bv_value in
    let frac = pad_with_zeros frac_len (Format.sprintf "%x" (to_int frac)) in
    if eq exp.bv_value zero then (* subnormals and zero *)
      (* Case for zero *)
      if eq mant.bv_value zero then
        if is_neg then Minus_zero else Plus_zero
      else
        (* Subnormals *)
        let hex = Format.asprintf "%t0x0.%sp-%s"
            (fun fmt -> if is_neg then Pp.string fmt "-")
            frac (to_string exp_bias) in
        Float_number {hex= Some hex; binary}
    else if eq exp.bv_value exp_max (* infinities and NaN *) then
      if eq mant.bv_value zero then
        if is_neg then Minus_infinity else Plus_infinity
      else Not_a_number
    else
      let exp = sub exp.bv_value exp_bias in
      let hex = Format.asprintf "%t0x1.%sp%s"
          (fun fmt -> if is_neg then Pp.string fmt "-")
          frac (to_string exp) in
      Float_number {hex= Some hex; binary}
  with Exit ->
    Float_number {hex= None; binary}

let binary_of_bigint d =
  let open BigInt in
  if lt d zero then invalid_arg "bin_of_int";
  if eq d zero then "0" else
    let rec loop acc d =
      if eq d zero then acc else
        let d, m = computer_div_mod d (of_int 2) in
        loop (BigInt.to_string m :: acc) d in
    String.concat "" (loop [] d)

let binary_of_bv bv =
  let b = binary_of_bigint bv.bv_value in
  let p = String.make (bv.bv_length-String.length b) '0' in
  Printf.sprintf "#b%s%s" p b

let debug_force_binary_floats = Debug.register_flag "model_force_binary_floats"
    ~desc:"Print all floats using bitvectors in JSON output for models"

let convert_float_value f =
  match f with
  | Plus_infinity ->
      let m = Mstr.add "cons" (Json_base.String "Plus_infinity") Mstr.empty in
      Json_base.Record m
  | Minus_infinity ->
      let m = Mstr.add "cons" (Json_base.String "Minus_infinity") Mstr.empty in
      Json_base.Record m
  | Plus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Plus_zero") Mstr.empty in
      Json_base.Record m
  | Minus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Minus_zero") Mstr.empty in
      Json_base.Record m
  | Not_a_number ->
      let m = Mstr.add "cons" (Json_base.String "Not_a_number") Mstr.empty in
      Json_base.Record m
  | Float_number {binary= {sign; exp; mant}} when Debug.test_flag debug_force_binary_floats ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String (binary_of_bv sign)) m in
      let m = Mstr.add "exponent" (Json_base.String (binary_of_bv exp)) m in
      let m = Mstr.add "significand" (Json_base.String (binary_of_bv mant)) m in
      Json_base.Record m
  | Float_number {hex= Some hex} ->
      let m = Mstr.add "cons" (Json_base.String "Float_hexa") Mstr.empty in
      let m = Mstr.add "str_hexa" (Json_base.String hex) m in
      let m = Mstr.add "value" (Json_base.Float (float_of_string hex)) m in
      Json_base.Record m
  | Float_number {binary= {sign; exp; mant}} ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String sign.bv_verbatim) m in
      let m = Mstr.add "exponent" (Json_base.String exp.bv_verbatim) m in
      let m = Mstr.add "significand" (Json_base.String mant.bv_verbatim) m in
      Json_base.Record m

let convert_model_const = function
  | String s ->
      let m = Mstr.add "type" (Json_base.String "String") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Integer r ->
      let m = Mstr.add "type" (Json_base.String "Integer") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (BigInt.to_string r.int_value)) m in
      Json_base.Record m
  | Float f ->
      let m = Mstr.add "type" (Json_base.String "Float") Mstr.empty in
      let m = Mstr.add "val" (convert_float_value f) m in
      Json_base.Record m
  | Decimal d ->
      let m = Mstr.add "type" (Json_base.String "Decimal") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (Format.sprintf "%s.%s" (BigInt.to_string d.dec_int) (BigInt.to_string d.dec_frac))) m in
      Json_base.Record m
  | Fraction f ->
      let m = Mstr.add "type" (Json_base.String "Fraction") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (Format.sprintf "%s/%s" (BigInt.to_string f.frac_nom) (BigInt.to_string f.frac_den))) m in
      Json_base.Record m
  | Bitvector bv ->
      let m = Mstr.add "type" (Json_base.String "Integer") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (BigInt.to_string bv.bv_value)) m in
      Json_base.Record m
  | Boolean b ->
      let m = Mstr.add "type" (Json_base.String "Boolean") Mstr.empty in
      let m = Mstr.add "val" (Json_base.Bool b) m in
      Json_base.Record m

let rec convert_model_value value : Json_base.json =
  match value with
  | Const c -> convert_model_const c
  | Unparsed s ->
      let m = Mstr.add "type" (Json_base.String "Unparsed") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Array a ->
      let l = convert_array a in
      let m = Mstr.add "type" (Json_base.String "Array") Mstr.empty in
      let m = Mstr.add "val" (Json_base.List l) m in
      Json_base.Record m
  | Apply (s, lt) ->
      let lt = List.map convert_model_value lt in
      let slt =
        let m = Mstr.add "list" (Json_base.List lt) Mstr.empty in
        let m = Mstr.add "apply" (Json_base.String s) m in
        Json_base.Record m in
      let m = Mstr.add "type" (Json_base.String "Apply") Mstr.empty in
      let m = Mstr.add "val" slt m in
      Json_base.Record m
  | Model_var n ->
      let m = Mstr.add "type" (Json_base.String "Model_var") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String n.men_name) m in
      Json_base.Record m
  | Var v ->
      let m = Mstr.add "type" (Json_base.String "Var") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String v) m in
      Json_base.Record m
  | Record r -> convert_record r
  | Proj p -> convert_proj p
  | Ite _ ->
      let m = Mstr.add "type" (Json_base.String "Ite") Mstr.empty in
      Json_base.Record m
  | Constrained ->
      let m = Mstr.add "type" (Json_base.String "Constrained") Mstr.empty in
      Json_base.Record m
  | Undefined ->
      let m = Mstr.add "type" (Json_base.String "Undefined") Mstr.empty in
      Json_base.Record m

and convert_array a =
  let m_others =
    Mstr.add "others" (convert_model_value a.arr_others) Mstr.empty in
  let cmp_ix i1 i2 = compare_model_value i1.arr_index_key i2.arr_index_key in
  convert_indices (List.sort cmp_ix a.arr_indices) @ [Json_base.Record m_others]

and convert_indices indices =
  match indices with
  | [] -> []
  | index :: tail ->
      let m =
        Mstr.add "indice" (convert_model_value index.arr_index_key) Mstr.empty
      in
      let m = Mstr.add "value" (convert_model_value index.arr_index_value) m in
      Json_base.Record m :: convert_indices tail

and convert_record r =
  let m = Mstr.add "type" (Json_base.String "Record") Mstr.empty in
  let fields = convert_fields r in
  let m_field = Mstr.add "Field" fields Mstr.empty in
  let m = Mstr.add "val" (Json_base.Record m_field) m in
  Json_base.Record m

and convert_proj p =
  let proj_name, value = p in
  let m = Mstr.add "type" (Json_base.String "Proj") Mstr.empty in
  let m = Mstr.add "proj_name" (Json_base.String proj_name) m in
  let m = Mstr.add "value" (convert_model_value value) m in
  Json_base.Proj m

and convert_fields fields =
  Json_base.List
    (List.map
       (fun (f, v) ->
         let m = Mstr.add "field" (Json_base.String f) Mstr.empty in
         let m = Mstr.add "value" (convert_model_value v) m in
         Json_base.Record m)
       fields)

let print_model_value_sanit fmt v =
  let v = convert_model_value v in
  Json_base.print_json fmt v

let print_model_value = print_model_value_sanit

(********************************************)
(* Print values (as to be displayed in IDE) *)
(********************************************)
let print_float_human fmt f =
  match f with
  | Plus_infinity -> fprintf fmt "+∞"
  | Minus_infinity -> fprintf fmt "-∞"
  | Plus_zero -> fprintf fmt "+0"
  | Minus_zero -> fprintf fmt "-0"
  | Not_a_number -> fprintf fmt "NaN"
  | Float_number {hex= Some hex} ->
      fprintf fmt "%s (%g)" hex (float_of_string hex)
  | Float_number {binary= {sign; exp; mant}} ->
      fprintf fmt "float_bits(%s,%s,%s)" sign.bv_verbatim exp.bv_verbatim mant.bv_verbatim

let print_integer fmt (i: BigInt.t) =
  fprintf fmt "%s%t" (BigInt.to_string i)
    (fun fmt -> (* Print hex representation only when it isn't redundant *)
       if BigInt.(gt (abs i) (of_int 9)) then
         fprintf fmt "≡%t0X%a"
           (fun fmt -> if BigInt.sign i < 0 then pp_print_string fmt "-")
           (Number.print_in_base 16 None) (BigInt.abs i))

let print_bv fmt (bv : model_bv) =
  (* TODO Not implemented yet. Ideally, fix the differentiation made in the
     parser between Bv_int and Bv_sharp -> convert Bv_int to Bitvector not
     Integer. And print Bv_int exactly like Bv_sharp.
  *)
  fprintf fmt "%s" bv.bv_verbatim

let print_model_const_human fmt = function
  | String s -> Constant.print_string_def fmt s
  | Integer i -> print_integer fmt i.int_value
  | Decimal d -> fprintf fmt "%s.%s" (BigInt.to_string d.dec_int) (BigInt.to_string d.dec_frac)
  | Fraction f -> fprintf fmt "%s/%s" (BigInt.to_string f.frac_nom) (BigInt.to_string f.frac_den)
  | Float f -> print_float_human fmt f
  | Boolean b -> fprintf fmt "%b" b
  | Bitvector s -> print_bv fmt s

let rec print_array_human fmt (arr : model_array) =
  let print_others fmt v =
    fprintf fmt "@[others =>@ %a@]" print_model_value_human v in
  let print_key_val fmt arr =
    let {arr_index_key= key; arr_index_value= v} = arr in
    fprintf fmt "@[%a =>@ %a@]" print_model_value_human key
      print_model_value_human v in
  let sort_ix i1 i2 = compare_model_value i1.arr_index_key i2.arr_index_key in
  fprintf fmt "@[<hv3>(%a%a)@]"
    (Pp.print_list_delim ~start:Pp.nothing ~stop:Pp.comma ~sep:Pp.comma
       print_key_val)
    (List.sort sort_ix arr.arr_indices) print_others arr.arr_others

and print_record_human fmt =
  fprintf fmt "@[<hv1>{%a}@]"
    (Pp.print_list Pp.semi
       (fun fmt (f, v) ->
          fprintf fmt "@[%s =@ %a@]" f print_model_value_human v))

and print_proj_human fmt p =
  let s, v = p in
  fprintf fmt "@[{%s =>@ %a}@]" s print_model_value_human v

and print_model_value_human fmt = function
  | Const c -> print_model_const_human fmt c
  | Apply (s, []) -> fprintf fmt "%s" s
  | Apply (s, lt) ->
      fprintf fmt "@[<hv2>(%s@ %a)@]" s
        (Pp.print_list Pp.space print_model_value_human) lt
  | Array arr -> print_array_human fmt arr
  | Record r -> print_record_human fmt r
  | Proj p -> print_proj_human fmt p
  | Model_var n -> fprintf fmt "%s" (*ₘ*) (why_display_name n)
  | Var v -> fprintf fmt "%s" (*ₗ*) v
  | Constrained -> fprintf fmt "CONSTRAINED"
  | Ite (v1, v2, v3) ->
      fprintf fmt "if %a then %a else %a" print_model_value_human v1
        print_model_value_human v2 print_model_value_human v3
  | Undefined -> fprintf fmt "UNDEFINED"
  | Unparsed s -> fprintf fmt "%s" s

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element = {
  me_name: model_element_name;
  me_value: model_value;
  me_constraints: model_constraint list;
  me_equalities: model_value list;
  me_location: Loc.position option;
  me_term: Term.term option;
}

let create_model_element ?id ?display ~name ~value ~attrs =
  let me_name = {men_id= id; men_name= name; men_display= display;
                 men_kind= Other; men_attrs= attrs; men_field_chain= []} in
  {me_name; me_value= value; me_constraints= []; me_equalities= [];
   me_location= None; me_term= None}

let create_model_element_name ?(field_chain=[]) ?id name display attrs kind =
  {men_id= id; men_name= name; men_display= display; men_kind= kind;
   men_attrs= attrs; men_field_chain= field_chain}

(*
***************************************************************
**  Model definitions
***************************************************************
*)

type model_file = model_element list Mint.t
type model_files = model_file Mstr.t

type model = {
  model_files: model_files;
  model_constraints: model_constraint list;
  vc_term_loc: Loc.position option;
  vc_term_attrs: Sattr.t;
}

let map_filter_model_files f =
  let f_list elts =
    match Lists.map_filter f elts with
    | [] -> None | l -> Some l in
  let f_files mf =
    let mf = Mint.map_filter f_list mf in
    if Mint.is_empty mf then None else Some mf in
  Mstr.map_filter f_files

let map_filter_model_elements f m =
  {m with model_files= map_filter_model_files f m.model_files}

let empty_model_file = Mint.empty
let empty_model_files = Mstr.empty
let is_model_empty m = Mstr.is_empty m.model_files

let empty_model =
  {model_files=empty_model_files; model_constraints= [];
   vc_term_loc=None; vc_term_attrs=Sattr.empty}

let set_model_files model model_files =
  { model with model_files }

let get_model_elements_files files =
  List.(concat (concat (map Mint.values (Mstr.values files))))

let get_model_elements m = get_model_elements_files m.model_files

let get_model_term_loc m = m.vc_term_loc
let get_model_term_attrs m = m.vc_term_attrs

(** [search_model_element ?file ?line m p] searches a model element [me] in
    model [m], whose file is [file] and line is [line], and which fullfils
    [p me]. *)
let search_model_element ?file ?line m p =
  let iter_line f line' mes = if line = None || line = Some line' then
      List.iter f mes in
  let iter_file f file' lines = if file = None || file = Some file' then
      Mint.iter (iter_line f) lines in
  let iter_files f = Mstr.iter (iter_file f) m.model_files in
  Util.iter_first iter_files p

let trace_by_id id =
  Ident.get_model_trace_string ~name:id.id_string ~attrs:id.id_attrs

let trace_by_men men =
  Ident.get_model_trace_string ~name:men.men_name ~attrs:men.men_attrs

let search_model_element_for_id m ?loc id =
  let oloc = if loc <> None then loc else id.id_loc in
  let id_trace = trace_by_id id in
  let p me =
    if trace_by_men me.me_name = id_trace &&
       Opt.equal Loc.equal me.me_location oloc
    then Some me else None in
  search_model_element m p

(*
***************************************************************
**  Quering the model
***************************************************************
*)

let cmp_attrs a1 a2 =
  String.compare a1.attr_string a2.attr_string

let print_model_element ?(print_locs=false) ~print_attrs ~print_model_value fmt me =
  if me.me_name.men_kind = Error_message then
    let exn = Failure "Error message model element without display" in
    fprintf fmt "%s" (Opt.get_exn exn me.me_name.men_display)
  else (
    fprintf fmt "@[<hov2>%s" (why_display_name me.me_name);
    if print_attrs then
      fprintf fmt " %a" Pp.(print_list space Pretty.print_attr)
        (List.sort cmp_attrs (Sattr.elements me.me_name.men_attrs));
    if print_locs then
      fprintf fmt " (%a)" (Pp.print_option_or_default "NO LOC "Pretty.print_loc)
        me.me_location;
    Pp.(print_list_pre (constant_formatted " =@ ") print_model_value) fmt
      me.me_equalities;
    if me.me_equalities = [] || me.me_value <> Constrained then
      fprintf fmt " =@ %a" print_model_value me.me_value;
    Pp.(print_list_pre (constant_formatted "@ /\\ ") print_model_value) fmt
      me.me_constraints;
    fprintf fmt "@]" )

let similar_model_element_names n1 n2 =
  Ident.get_model_trace_string ~name:n1.men_name ~attrs:n1.men_attrs
  = Ident.get_model_trace_string ~name:n2.men_name ~attrs:n2.men_attrs &&
  n1.men_kind = n2.men_kind

(* TODO optimize *)
let rec filter_duplicated l =
  let exist_similar a l = List.exists (fun x ->
    similar_model_element_names a.me_name x.me_name) l in
  match l with
  | [] | [_] -> l
  | me :: l when exist_similar me l -> filter_duplicated l
  | me :: l -> me :: filter_duplicated l

let print_model_elements ~filter_similar ~print_attrs ?(sep = Pp.newline)
    ~print_model_value fmt m_elements =
  let m_elements =
    if filter_similar then filter_duplicated m_elements else m_elements in
  fprintf fmt "@[%a@]"
    (Pp.print_list sep
       (print_model_element ?print_locs:None ~print_attrs ~print_model_value))
    m_elements

let print_model_file ~filter_similar ~print_attrs ~print_model_value fmt (filename, model_file) =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths. *)
  let filename = Filename.basename filename in
  let pp fmt (line, m_elements) =
    let cmp {me_name= men1} {me_name= men2} =
      let n = String.compare men1.men_name men2.men_name in
      if n = 0 then Sattr.compare men1.men_attrs men2.men_attrs else n in
    let m_elements = List.sort cmp m_elements in
    fprintf fmt "  @[<v 2>Line %d:@ %a@]" line
      (print_model_elements ~filter_similar ?sep:None ~print_attrs
         ~print_model_value) m_elements in
  fprintf fmt "@[<v 0>File %s:@ %a@]" filename
    Pp.(print_list space pp) (Mint.bindings model_file)

let print_model ~filter_similar ~print_attrs ~print_model_value fmt model =
  Pp.print_list Pp.newline (print_model_file ~filter_similar ~print_attrs ~print_model_value)
    fmt (Mstr.bindings model.model_files);
  if model.model_constraints <> [] then
    Format.fprintf fmt "@\n@[<hov2>Other constraints:@ %a@]"
      Pp.(print_list (constant_formatted "@ /\\ ") print_model_value)
      model.model_constraints

let print_model_human ?(filter_similar = true) ?(print_attrs=false) fmt model =
  let print_model_value = print_model_value_human in
  print_model ~filter_similar ~print_model_value ~print_attrs fmt model

let print_model ?(filter_similar = true) ?(print_attrs=false) fmt model =
  print_model ~filter_similar ~print_attrs ~print_model_value fmt model

let get_model_file model filename =
  Mstr.find_def empty_model_file filename model

let get_elements model_file line_number =
  Mint.find_def [] line_number model_file

let get_padding line =
  try
    let r = Re.Str.regexp " *" in
    ignore (Re.Str.search_forward r line 0) ;
    Re.Str.matched_string line
  with Not_found -> ""

(* This assumes that l is sorted and split the list of locations in two:
   those that are applied on this line and the others. For those that are on
   this line, we split the locations that appear on several lines. *)
let rec partition_loc line lc l =
  match l with
  | (hd, a) :: tl ->
      let hdf, hdl, hdfc, hdlc = Loc.get hd in
      if hdl = line then
        if hdlc > lc then
          let old_sloc = Loc.user_position hdf hdl hdfc lc in
          let newlc = hdlc - lc in
          let new_sloc = Loc.user_position hdf (hdl + 1) 1 newlc in
          let rem_loc, new_loc = partition_loc line lc tl in
          ((new_sloc, a) :: rem_loc, (old_sloc, a) :: new_loc)
        else
          let rem_loc, new_loc = partition_loc line lc tl in
          (rem_loc, (hd, a) :: new_loc)
      else (l, [])
  | _ -> (l, [])

(* Change a locations so that it points to a different line number *)
let add_offset off (loc, a) =
  let f, l, fc, lc = Loc.get loc in
  (Loc.user_position f (l + off) fc lc, a)

let interleave_line ~filename:_ ~print_attrs start_comment end_comment model_file
    (source_code, line_number, offset, remaining_locs, locs) line =
  let remaining_locs, list_loc =
    partition_loc line_number (String.length line) remaining_locs in
  let list_loc = List.map (add_offset offset) list_loc in
  try
    let model_elements = Mint.find line_number model_file in
    let cntexmp_line =
      asprintf "@[<h 0>%s%s%a%s@]" (get_padding line) start_comment
        (print_model_elements ~filter_similar:true ~sep:Pp.semi
           ~print_attrs ~print_model_value:print_model_value_human)
        model_elements end_comment in
    (* We need to know how many lines will be taken by the counterexample. This
       is ad hoc as we don't really know how the lines are split in IDE. *)
    let len_cnt = 1 + (String.length cntexmp_line / 80) in
    source_code ^ line ^ cntexmp_line ^ "\n",
    line_number + 1,
    offset + len_cnt,
    remaining_locs,
    list_loc @ locs
  with Not_found ->
    source_code ^ line,
    line_number + 1,
    offset,
    remaining_locs,
    list_loc @ locs

let interleave_with_source ~print_attrs ?(start_comment = "(* ")
    ?(end_comment = " *)") model ~rel_filename
    ~source_code ~locations =
  let locations =
    List.sort
      (fun x y -> compare (fst x) (fst y))
      (List.filter
         (fun x ->
           let f, _, _, _ = Loc.get (fst x) in
           f = rel_filename)
         locations) in
  try
    (* There is no way to compare rel_filename and the locations of filename in
       the file because they contain extra ".." which cannot be reliably removed
       (because of potential symbolic link). So, we use the basename.
    *)
    let rel_filename = Filename.basename rel_filename in
    let model_files =
      Mstr.filter
        (fun k _ -> Filename.basename k = rel_filename)
        model.model_files in
    let model_file = snd (Mstr.choose model_files) in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let last_cntexmp_line, _ = Mint.max_binding model_file in
      Re.Str.bounded_split (Re.Str.regexp "^") source_code
        (last_cntexmp_line + 1) in
    let source_code, _, _, _, gen_loc =
      List.fold_left
        (interleave_line ~filename:rel_filename ~print_attrs start_comment
           end_comment model_file)
        ("", 1, 0, locations, [])
        (src_lines_up_to_last_cntexmp_el source_code model_file) in
    (source_code, gen_loc)
  with Not_found -> (source_code, locations)

let print_attrs_json (me : model_element_name) fmt =
  Json_base.list
    (fun fmt attr -> Json_base.string fmt attr.attr_string)
    fmt
    (List.sort cmp_attrs (Sattr.elements me.men_attrs))

(*
**  Quering the model - json
*)
let print_model_element_json fmt me =
  let print_value fmt = fprintf fmt "%a" print_model_value_sanit me.me_value in
  let print_kind fmt =
    (* We compute kinds using the attributes and locations *)
    match me.me_name.men_kind with
    | Result -> fprintf fmt "%a" Json_base.string "result"
    | At l -> fprintf fmt "@%s" l
    | Old -> fprintf fmt "%a" Json_base.string "old"
    | Error_message -> fprintf fmt "%a" Json_base.string "error_message"
    | Other -> fprintf fmt "%a" Json_base.string "other"
    | Loop_before -> fprintf fmt "%a" Json_base.string "before_loop"
    | Loop_before_iteration ->
        fprintf fmt "%a" Json_base.string "before_iteration"
    | Loop_current_iteration ->
        fprintf fmt "%a" Json_base.string "current_iteration" in
  let print_name fmt = Json_base.string fmt (json_display_name me.me_name) in
  let print_json_attrs fmt = print_attrs_json me.me_name fmt in
  let print_value_or_kind_or_name fmt printer = printer fmt in
  Json_base.map_bindings (fun s -> s) print_value_or_kind_or_name fmt
    [ ("name", print_name); ("attrs", print_json_attrs);
      ("value", print_value) ; ("kind", print_kind) ]

let print_model_elements_json fmt model_elements =
  let model_elements = filter_duplicated model_elements in
  Json_base.list print_model_element_json fmt model_elements

let print_model_elements_on_lines_json model vc_line_trans fmt
    (file_name, model_file) =
  Json_base.map_bindings
    (fun i ->
      match model.vc_term_loc with
      | None -> string_of_int i
      | Some pos ->
          let vc_file_name, line, _, _ = Loc.get pos in
          if file_name = vc_file_name && i = line then vc_line_trans i
          else string_of_int i)
    print_model_elements_json
    fmt
    (Mint.bindings model_file)

let print_model_json ?(vc_line_trans = fun i -> string_of_int i) fmt model =
  let model_files_bindings =
    List.fold_left
      (fun bindings (file_name, model_file) ->
        List.append bindings [(file_name, (file_name, model_file))])
      []
      (Mstr.bindings model.model_files) in
  Json_base.map_bindings
    (fun s -> s)
    (print_model_elements_on_lines_json model vc_line_trans)
    fmt model_files_bindings

(*
***************************************************************
**  Get element kinds
***************************************************************
*)

let loc_starts_le loc1 loc2 =
  loc1 <> Loc.dummy_position && loc2 <> Loc.dummy_position &&
  let f1, l1, b1, _ = Loc.get loc1 in
  let f2, l2, b2, _ = Loc.get loc2 in
  f1 = f2 && l1 <= l2 && l1 <= l2 && b1 <= b2

let while_loop_kind vc_attrs var_loc =
  let is_inv_pres a =
    a.attr_string = "expl:loop invariant preservation" ||
    a.attr_string = "expl:loop variant decrease" in
  if Sattr.exists is_inv_pres vc_attrs then
    let loop_loc =
      let is_while a = Strings.has_prefix "loop:" a.attr_string in
      let attr = Sattr.choose (Sattr.filter is_while vc_attrs) in
      Scanf.sscanf attr.attr_string "loop:%[^:]:%d:%d:%d"
        Loc.user_position in
    Some (
      if var_loc = loop_loc then
        Loop_before_iteration
      else if loc_starts_le loop_loc var_loc then
        Loop_current_iteration
      else
        Loop_before )
  else None

let get_loop_kind vc_attrs oloc () =
  Opt.bind oloc (while_loop_kind vc_attrs)

let get_loc_kind oloc attrs () =
  match oloc with
  | None -> None
  | Some loc ->
      let f,l,_,_ = Loc.get loc in
      let search a =
        try
          Scanf.sscanf a.attr_string "at:%[^:]:loc:%[^:]:%d"
            (fun label f' l' ->
               if Filename.basename f = Filename.basename f' && l = l' then
                 Some (if label = "'Old" then Old else At label)
               else
                 None)
        with _ -> None in
      try Some (Lists.first search (Sattr.elements attrs)) with
        Not_found -> None

let get_result_kind attrs () =
  match Ident.get_model_trace_attr ~attrs with
  | exception Not_found -> None
  | a ->
      match Strings.(bounded_split '@' a.attr_string 3) with
      | _ :: "result" :: _ -> Some Result
      | _ -> None

let compute_kind vc_attrs oloc attrs =
  try
    Lists.first (fun f -> f ()) [
      get_loc_kind oloc attrs;
      get_result_kind attrs;
      get_loop_kind vc_attrs oloc;
    ]
  with Not_found -> Other

(*
***************************************************************
**  Building the model from raw model
***************************************************************
*)

let insert_element_if_loc ?kind me files =
  match me.me_location with
  | None -> files
  | Some pos ->
      let filename, line_number, _, _ = Loc.get pos in
      let model_file = get_model_file files filename in
      let me = match kind with None -> me | Some men_kind ->
        {me with me_name= {me.me_name with men_kind}} in
      let elements = get_elements model_file line_number in
      (* This removes elements that are duplicated *)
      let found_elements =
        List.exists (fun x ->
            similar_model_element_names x.me_name me.me_name
            && pos = Opt.get_def Loc.dummy_position x.me_location)
          elements in
      let elements = if found_elements then elements
                     else me :: elements in
      let model_file = Mint.add line_number elements model_file in
      Mstr.add filename model_file files

let recover_name pm fields_projs raw_name =
  let name, attrs =
    try
      let t = Mstr.find raw_name pm.queried_terms in
      match t.t_node with
      | Tapp (ls, []) -> (ls.ls_name.id_string, t.t_attrs)
      | _ -> ("", t.t_attrs)
    with Not_found ->
      let id = Mstr.find raw_name fields_projs in
      (id.id_string, id.id_attrs) in
  get_model_trace_string ~name ~attrs


(** [replace_projection const_function mv] replaces record names, projections, and application callees
   in [mv] using [const_function] *)
let rec replace_projection (const_function : string -> string) =
  let const_function s = try const_function s with Not_found -> s in
  function
  | Const _ as v -> v
  | Record fs ->
      let aux (f, mv) = const_function f, replace_projection const_function mv in
      Record (List.map aux fs)
  | Proj (f, mv) ->
      Proj (const_function f, replace_projection const_function mv)
  | Array a -> Array (replace_projection_array const_function a)
  | Apply (s, l) ->
      Apply (const_function s, List.map (replace_projection const_function) l)
  | Ite (v1, v2, v3) ->
      let v1 = replace_projection const_function v1 in
      let v2 = replace_projection const_function v2 in
      let v3 = replace_projection const_function v3 in
      Ite (v1, v2, v3)
  | Constrained | Model_var _ | Var _ | Undefined | Unparsed _ as v -> v

and replace_projection_array const_function a =
  let for_index a =
    let arr_index_value = replace_projection const_function a.arr_index_value in
    {a with arr_index_value} in
  {arr_others= replace_projection const_function a.arr_others;
   arr_indices= List.map for_index a.arr_indices}

(* Elements that are of record with only one field in the source code, are
   simplified by eval_match in wp generation. So, this allows to reconstruct
   their value (using the "field" attribute that were added). *)
let field_chain attrs =
  let fields = Lists.map_filter Ident.extract_field (Sattr.elements attrs) in
  List.map snd
    (List.sort (fun (d1, _) (d2, _) -> d1 - d2) fields)

let internal_loc t =
  match t.t_node with
  | Tvar vs -> vs.vs_name.id_loc
  | Tapp (ls, []) -> ls.ls_name.id_loc
  | _ -> None

let remove_field : (Sattr.t * model_value -> Sattr.t * model_value) ref = ref (fun x -> x)
let register_remove_field f = remove_field := f

let handle_contradictory_vc vc_term_loc model_files =
  (* The VC is contradictory if the location of the term that triggers VC
     was collected, model_files is not empty, and there are no model elements
     in this location.
     If this is the case, add model element saying that VC is contradictory
     to this location. *)
  if Mstr.is_empty model_files then
    (* If the counterexample model was not collected, then model_files
       is empty and this does not mean that VC is contradictory. *)
    model_files
  else match vc_term_loc with
    | None -> model_files
    | Some pos ->
        let filename, line_number, _, _ = Loc.get pos in
        let model_file = get_model_file model_files filename in
        match get_elements model_file line_number with
        | [] ->
            (* The vc is contradictory, add special model element  *)
            let me = create_model_element ?id:None ~name:"hello"
                ~display:"the check fails with all inputs"
                ~value:(Unparsed "contradictory vc")
                ~attrs:Sattr.empty in
            let me = {me with me_location= Some pos} in
            insert_element_if_loc ~kind:Error_message me model_files
        | _ -> model_files

(*
***************************************************************
** Model cleaning
***************************************************************
*)

let opt_bind_any os f =
  f (Lists.map_filter (fun x -> x) os)

let opt_bind_all os f =
  if List.for_all Opt.inhabited os then
    f (List.map Opt.get os)
  else None

class map = object (self)
  method model m =
    {m with model_files= map_filter_model_files self#element m.model_files}
  method element me =
    if me.me_name.men_kind = Error_message then
      (* Keep unparsed values for error messages *)
      Some me
    else
      Opt.bind (self#value me.me_value) @@ fun me_value ->
      let me_constraints = Lists.map_filter self#constraint_ me.me_constraints in
      let me_equalities = Lists.map_filter self#equality me.me_equalities in
      Some {me with me_value; me_constraints; me_equalities}
  method value v = match v with
    | Const c     -> self#const c    | Ite (v1, v2, v3) -> self#ite v1 v2 v3
    | Unparsed s  -> self#unparsed s | Constrained      -> self#constrained
    | Proj (p, v) -> self#proj p v   | Apply (s, vs)    -> self#apply s vs
    | Array a     -> self#array a    | Record fs        -> self#record fs
    | Undefined   -> self#undefined  | Model_var v      -> self#model_var v
    | Var v       -> self#var v
  method const c = match c with
    | String v    -> self#string v  | Integer v  -> self#integer v
    | Decimal v   -> self#decimal v | Fraction v -> self#fraction v
    | Float v     -> self#float v   | Boolean v  -> self#boolean v
    | Bitvector v -> self#bitvector v
  method constrained = Some Constrained
  method string v = Some (Const (String v))
  method integer v = Some (Const (Integer v))
  method decimal v = Some (Const (Decimal v))
  method fraction v = Some (Const (Fraction v))
  method float v = Some (Const (Float v))
  method boolean v = Some (Const (Boolean v))
  method bitvector v = Some (Const (Bitvector v))
  method model_var v = Some (Model_var v)
  method var v = Some (Var v)
  method ite v1 v2 v3 = Some (Ite (v1, v2, v3))
  method proj p v =
    Opt.bind (self#value v) @@ fun v ->
    Some (Proj (p, v))
  method apply s vs =
    opt_bind_all (List.map self#value vs) @@ fun vs ->
    Some (Apply (s, vs))
  method array a =
    let clean_arr_index ix =
      Opt.bind (self#value ix.arr_index_key) @@ fun key ->
      Opt.bind (self#value ix.arr_index_value) @@ fun value ->
      Some {arr_index_key= key; arr_index_value= value} in
    Opt.bind (self#value a.arr_others) @@ fun others ->
    opt_bind_any (List.map clean_arr_index a.arr_indices) @@ fun indices ->
    Some (Array {arr_others= others; arr_indices= indices})
  method record fs =
    let clean_field (f, v) =
      Opt.bind (self#value v) @@ fun v ->
      Some (f, v) in
    opt_bind_all (List.map clean_field fs) @@ fun fs ->
    Some (Record fs)
  method constraint_ (c: model_constraint) = Some c
  method equality (v: model_value) = Some v
  method unparsed s = Some (Unparsed s)
  method undefined = Some Undefined
end

class clean = object
  inherit map
  method! unparsed _ = None
  method! var _ = None
end

let clean = ref (new clean)

let customize_clean c = clean := (c :> clean)

(*
***************************************************************
**  Filtering the model
***************************************************************
*)

let add_loc orig_model new_model position =
  (* Add a given location from orig_model to new_model *)
  let file_name, line_num, _, _ = Loc.get position in
  let orig_model_file = get_model_file orig_model file_name in
  let new_model_file = get_model_file new_model file_name in
  if Mint.mem line_num new_model_file then
    (* the location already is in new_model *)
    new_model
  else
    try
      (* get the location from original model *)
      let line_map = Mint.find line_num orig_model_file in
      (* add the location to new model *)
      let new_model_file = Mint.add line_num line_map new_model_file in
      Mstr.add file_name new_model_file new_model
    with Not_found -> new_model

let add_first_model_line filename model_file model =
  let line_num, cnt_info = Mint.min_binding model_file in
  let mf = get_model_file model filename in
  let mf = Mint.add line_num cnt_info mf in
  Mstr.add filename mf model

let model_for_positions_and_decls model ~positions =
  (* Start with empty model and add locations from model that
     are in locations *)
  let model_filtered =
    List.fold_left (add_loc model.model_files) empty_model_files positions in
  (* For each file add mapping corresponding to the first line of the
     counter-example from model to model_filtered.
     This corresponds to function declarations *)
  let model_filtered =
    Mstr.fold add_first_model_line model.model_files model_filtered in
  {model with model_files= model_filtered}

(******************************************************************************)
(*                            Alt-Ergo constraints                            *)
(******************************************************************************)

(** Collect the variables in a model constraint, or in a model value *)
let value_vars ~vars ~model_vars ~funcs =
  let rec aux_value sofar = function
    | Const _ | Constrained | Unparsed _ | Undefined -> sofar
    | Var v -> if vars then Sstr.add v sofar else sofar
    | Model_var n ->
        if model_vars then (match n.men_id with Some id -> Sstr.add id sofar | None -> sofar) else sofar
    | Proj (f, t) ->
        aux_value (if funcs then Sstr.add f sofar else sofar) t
    | Apply (f, vs) ->
        List.fold_left aux_value (if funcs then Sstr.add f sofar else sofar) vs
    | Array a -> aux_array sofar a
    | Ite (t1, t2, t3) -> List.fold_left aux_value sofar [t1; t2; t3]
    | Record fs -> List.fold_left aux_value sofar (List.map snd fs)
  and aux_array sofar a =
    List.fold_left aux_index (aux_value sofar a.arr_others) a.arr_indices
  and aux_index sofar ix =
    aux_value (aux_value sofar ix.arr_index_key) ix.arr_index_value in
  aux_value

let model_value_vars = value_vars ~vars:false ~model_vars:true ~funcs:false
let dcld_vars = value_vars ~vars:true ~model_vars:false ~funcs:true
let value_vars = value_vars ~vars:true ~model_vars:false ~funcs:false

module Sval =
  Extset.Make (struct type t = model_value let compare = compare_model_value end)

(** To attach equality constraints to model values we distribute the equality
    constraints [(= v1 v2)] from the model into equality classes, i.e., [Sval.t
    list], a list of classes of values, that are equal according to the
    constraints. *)
module EqCls = struct

  type cls = Sval.t (** An equality class *)

  (** [find_eqs v cls_list] returns [Some (cls, cls_list')] if there exists an
      [cls] from [cls_list] to which [v] belongs, and [cls_list'] are the
      remainig equality sets in [cls_list]. *)
  let find_cls : model_value -> cls list -> (cls * cls list) option =
    let rec aux acc v = function
      | [] -> None
      | cls :: cls_list ->
          if Sval.mem v cls then
            Some (cls, List.rev acc @ cls_list)
          else
            aux (cls :: acc) v cls_list in
    aux []

  (** [insert_equality v1 v2 cls_list] inserts the equality between [v1] and
      [v2] into the equality sets (merging equality classes in [cls_list], when
      [v1] and [v2] belong to different sets).

      TODO Use hashcons to improve performance. *)
  let rec insert_equality (v1, v2) : cls list -> cls list = function
    | [] -> [Sval.of_list [v1; v2]]
    | cls :: cls_list ->
        match Sval.mem v1 cls, Sval.mem v2 cls with
        | true, true -> cls :: cls_list
        | true, false -> (
            match find_cls v2 cls_list with
            | None -> Sval.add v2 cls :: cls_list
            | Some (cls', cls_list) -> Sval.union cls' cls :: cls_list )
        | false, true -> (
            match find_cls v1 cls_list with
            | None -> Sval.add v1 cls :: cls_list
            | Some (cls', cls_list) -> Sval.union cls' cls :: cls_list )
        | false, false -> cls :: insert_equality (v1, v2) cls_list
end

let add_constraints_to_elt (ids, cnstrs, cls_list) me =
  match me.me_name.men_id with
  | None -> (ids, cnstrs, cls_list), me
  | Some id ->
      let ids = Sstr.add id ids in
      let here (ids', _) = not (Sstr.is_empty ids') && Sstr.subset ids' ids in

      let here_cnstrs, cnstrs = List.partition here cnstrs in
      let here_cnstrs = List.map snd here_cnstrs in

      let is_mvar = function Model_var n -> n.men_id = Some id | _ -> false in
      let here_cls_list, cls_list = List.partition here cls_list in
      let here_cls_list = List.map snd here_cls_list in
      let here_cls, here_cls_list =
        List.partition (List.exists is_mvar) here_cls_list in
      let me_equalities = match here_cls with
        | [] -> [] | [vs] -> List.filter (fun v -> not (is_mvar v)) vs
        | _ -> assert false in

      let here_cnstrs_eq = List.map (fun vs -> Apply ("=", vs)) here_cls_list in
      let me_constraints = here_cnstrs @ here_cnstrs_eq in
      (ids, cnstrs, cls_list), {me with me_constraints; me_equalities}

let add_constraints_to_files files cnstrs =
  let cnstrs_eq, cnstrs =
    let aux = function
      | Apply ("=", [_; _]) -> true
      | _ -> false in
    List.partition aux cnstrs in
  let cnstrs = List.map (fun c -> model_value_vars Sstr.empty c, c) cnstrs in
  let equalities =
    let aux = function
      | Apply ("=", [v1; v2]) -> v1, v2
      | _ -> assert false in
    List.map aux cnstrs_eq in
  let cls_list = List.fold_right EqCls.insert_equality equalities [] in
  let cls_list =
    let eqs_vars = Sval.fold_left model_value_vars Sstr.empty in
    let cmp v1 v2 = model_value_size v1 - model_value_size v2 in
    let aux cls = eqs_vars cls, List.sort cmp (Sval.elements cls) in
    List.map aux cls_list in
  Debug.dprintf debug "@[<hv2>Cnstrs:%a@]@."
    Pp.(print_list_pre (constant_formatted "@\n- ")
          (print_pair_delim nothing colon nothing
             (Sstr.print string) print_model_value_human))
    cnstrs;
  Debug.dprintf debug "@[<hv2>eqs:%a@]@."
    Pp.(print_list_pre (constant_formatted "@\n- ")
          (print_pair_delim nothing colon nothing
             (Sstr.print string) (print_list equal print_model_value_human)))
    cls_list;
  let (vars, cnstrs, cls_list), files =
    Mstr.mapi_fold (fun _ ->
        Mint.mapi_fold (fun _ mel sofar ->
            Lists.map_fold_left add_constraints_to_elt sofar mel))
      files (Sstr.empty, cnstrs, cls_list) in
  Debug.dprintf debug "Vars: %a@." (Sstr.print Pp.string) vars;
  let cnstrs_eq =
    List.map (fun (_, vs) -> Apply ("=", vs)) cls_list in
  files, List.map snd cnstrs @ cnstrs_eq


(******************************************************************************)
(*                         Model from raw elements                            *)
(******************************************************************************)

let is_queried_set_term_loc queried_terms me =
  match Mstr.find me.me_name.men_name queried_terms with
  | t -> Some {me with me_location= t.t_loc; me_term= Some t}
  | exception Not_found ->
      Debug.dprintf debug "No term for element %s@." me.me_name.men_name;
      None

let to_element set_str key value =
  let attrs = Mstr.find_def Ident.Sattr.empty key set_str in
  create_model_element ~id:key ~name:key ?display:None ~value ~attrs

let process_element pm fields_projs key me =
  let t = Mstr.find me.me_name.men_name pm.queried_terms in
  let attrs = Sattr.union me.me_name.men_attrs t.t_attrs in
  let name, attrs = match t.t_node with
    | Tapp (ls, []) ->
        (* Ident [ls] is recorded as [t_app ls] in [Printer.queried_terms] *)
        ls.ls_name.id_string, Sattr.union attrs ls.ls_name.id_attrs
    | _ -> "", attrs in
  (* Replace projections with their real name *)
  let v = replace_projection
      (fun s -> recover_name pm fields_projs s)
      me.me_value in
  (* Remove some specific record field related to the front-end language.
     This function is registered. *)
  let attrs, v = !remove_field (attrs, v) in
  (* Transform value flattened by eval_match (one field record) back to records *)
  let field_chain = field_chain attrs in
  let me_name = create_model_element_name ~id:key ~field_chain name None attrs Other in
  {me with me_name; me_value= v; me_location= t.t_loc; me_term= Some t}

let insert_element vc_attrs files me =
  let add_with_loc_set_kind me loc files =
    if loc = None then files else
      let kind = compute_kind vc_attrs loc me.me_name.men_attrs in
      insert_element_if_loc ~kind {me with me_location= loc} files in
  (** Add a model element at the relevant locations *)
  let kind = compute_kind vc_attrs me.me_location me.me_name.men_attrs in
  let model = insert_element_if_loc ~kind me files in
  let oloc = internal_loc (Opt.get me.me_term) in
  let model = add_with_loc_set_kind me oloc model in
  let add_written_loc a =
    let oloc = Ident.extract_written_loc a in
    add_with_loc_set_kind me oloc in
  Sattr.fold add_written_loc me.me_name.men_attrs model

let map_replace_model_vars vars = object
  inherit map
  method! var v = Some (try Model_var (Hstr.find vars v) with Not_found -> Var v)
end

(** Replace variables in values by the values [Constrained], and variables that
    refer to model elements in constraints by the names of the model elements. *)
let pop_model_vars files cnstrs =
  let cnstr_vars = List.fold_left value_vars Sstr.empty cnstrs in
  let vars = Hstr.create 13 in
  let set_constrained_select_vars me =
    assert (me.me_constraints = [] && me.me_equalities = []);
    let me_value = match me.me_value with
    | Var v when Sstr.mem v cnstr_vars ->
        Hstr.add vars v me.me_name;
        Constrained
    | v -> v in
    Some {me with me_value} in
  let files = map_filter_model_files set_constrained_select_vars files in
  let map = map_replace_model_vars vars in
  let replace_model_vars v = Opt.get (map#value v) in
  let aux me =
    let me_constraints = List.map replace_model_vars me.me_constraints in
    let me_equalities = List.map replace_model_vars me.me_equalities in
    Some {me with me_constraints; me_equalities} in
  let files = map_filter_model_files aux files in
  let cnstrs = List.map replace_model_vars cnstrs in
  files, cnstrs

let fix_model_var_kinds_value elts ambigous vc_attrs me =
  let loc = Opt.bind me (fun me -> me.me_location) in
  let f = Opt.map (fun l -> let f,_,_,_ = Loc.get l in f) loc in
  let map = object inherit map
    method! model_var nm =
      let kind = compute_kind vc_attrs loc nm.men_attrs in
      let kind = match kind, loc, nm.men_id with
        | Other, Some loc, Some id ->
            (match (Mstr.find id elts).me_location with
            | Some loc' when not (Loc.equal loc' loc) && Mstr.find_def true (display_name nm) ambigous ->
                let f',l,_,_ = Loc.get loc' in
                if f = Some f' then At (sprintf "line %d" l) else At (sprintf "%s:%d" (Filename.basename f') l)
            | _ -> kind)
        | _ -> kind in
      Some (Model_var {nm with men_kind= kind})
  end in
  fun v -> Opt.get (map#value v)

let fix_model_var_kinds elts ambigous vc_attrs files cnstrs =
  let files = map_filter_model_files (fun me ->
      let cnstrs = List.map (fix_model_var_kinds_value elts ambigous vc_attrs (Some me)) me.me_constraints in
      let eqlts = List.map (fix_model_var_kinds_value elts ambigous vc_attrs (Some me)) me.me_equalities in
      Some {me with me_constraints= cnstrs; me_equalities= eqlts}) files in
  let cnstrs = List.map (fix_model_var_kinds_value elts ambigous vc_attrs None) cnstrs in
  files, cnstrs

let fix_display_name nm =
  if nm.men_kind = Error_message then nm else
    {nm with men_display= Some (trace_by_men nm)}

let fix_display_name_value =
  let map = object inherit map
    method! model_var nm =
      Some (Model_var (fix_display_name nm))
  end in
  fun v -> Opt.get (map#value v)

let fix_display_names files cnstrs =
  let files = map_filter_model_files (fun me ->
      let me_name = fix_display_name me.me_name in
      let me_constraints = List.map fix_display_name_value me.me_constraints in
      let me_equalities = List.map fix_display_name_value me.me_equalities in
      Some {me with me_name; me_constraints; me_equalities}) files in
  let cnstrs = List.map fix_display_name_value cnstrs in
  files, cnstrs

let fix_display_name_value_SPARK attrs field_names = (* TODO *)
  match Ident.get_model_trace_attr ~attrs with
  | mtrace -> (
      let attrs = Sattr.remove mtrace attrs in
      (* Special cases for 'Last and 'First. TODO: Should be avoided here but
         there is no simple way. *)
      try
        let new_mtrace =
          Strings.remove_suffix "'Last" mtrace.attr_string ^
          String.concat "" field_names ^
          "'Last" in
        let new_attr = create_attribute new_mtrace in
        Sattr.add new_attr attrs
      with Not_found ->
      try
        let new_mtrace =
          Strings.remove_suffix "'First" mtrace.attr_string ^
          String.concat "" field_names ^
          "'First" in
        let new_attr = create_attribute new_mtrace in
        Sattr.add new_attr attrs
      with Not_found -> (* General case *)
        attrs )
  | exception Not_found ->
      (* No model trace attribute present, same as general case *)
      attrs

let rec field_chain_record v = function
  | [] -> v
  | f :: fields ->
      Record [f, field_chain_record v fields]

let field_chains_to_record me =
  let me_name = {me.me_name with men_field_chain= []} in
  let me_value = field_chain_record me.me_value me.me_name.men_field_chain in
  Some {me with me_name; me_value}

let rm_undcld_cnstrs dcld = object (self)
  inherit map as super
  method! apply s vs =
    if s = "=" then
      match Lists.map_filter self#value vs with
      | [] -> None
      | vs -> Some (Apply ("=", vs))
    else
      super#apply s vs
  method! constraint_ c =
    let vars = dcld_vars Sstr.empty c in
    if Sstr.exists (fun s -> Sstr.mem s dcld) vars then None else Some c
  method! equality v =
    let vars = dcld_vars Sstr.empty v in
    if Sstr.exists (fun s -> Sstr.mem s dcld) vars then None else Some v
end

let model_files_from_raw pm =
  let fields_projs = fields_projs pm and vc_attrs = pm.Printer.vc_term_attrs in
  fun (vals, cnstrs, dcld) ->
    let elts = Mstr.mapi_filter (fun key value ->
        to_element pm.Printer.set_str key value |>
        is_queried_set_term_loc pm.queried_terms |>
        Opt.map (process_element pm fields_projs key)) vals in
    let files = List.fold_left (insert_element vc_attrs) Mstr.empty (Mstr.values elts) in
    (* Substitute variable values by constrained values, and variables in the
       constraints by model variables *)
    let files, cnstrs = pop_model_vars files cnstrs in
    let files, cnstrs = add_constraints_to_files files cnstrs in
    (* Transform field chains to singleton record values, but only for CE
       values, not in the constraints. *)
    let files = map_filter_model_files field_chains_to_record files in
    let cnstrs = Lists.map_filter !clean#constraint_ cnstrs in
    let files = map_filter_model_files !clean#element files in
    let files = handle_contradictory_vc pm.Printer.vc_term_loc files in
    let files, cnstrs = fix_display_names files cnstrs in
    let rm_undcld_cnstrs = rm_undcld_cnstrs dcld in
    let cnstrs = Lists.map_filter rm_undcld_cnstrs#constraint_ cnstrs in
    let files = map_filter_model_files rm_undcld_cnstrs#element files in
    let ambigous =
      let aux sofar me =
        let str = display_name me.me_name in
        Mstr.add str (Mstr.mem str sofar) sofar in
      List.fold_left aux Mstr.empty (get_model_elements_files files) in
    Debug.dprintf debug "@[<hov2>AMBIGOUS: %a@]@."
      Pp.(print_list space (print_pair_delim nothing (constant_string ":") nothing string bool))
      (Mstr.bindings ambigous);
    let files, cnstrs = fix_model_var_kinds elts ambigous vc_attrs files cnstrs in
    files, cnstrs
(*
***************************************************************
** Registering model parser
***************************************************************
*)

type model_parser = printer_mapping -> string -> model
type raw_model_parser = printer_mapping -> string -> model_value Mstr.t * model_constraint list * Sstr.t

let debug_elements ((elts, _, _) as res) =
  let print_id_value fmt (id, v) =
    fprintf fmt "@[<hv2>%s: %a@]" id print_model_value_human v in
  Debug.dprintf debug "@[<v2>Elements:%a@]@."
    Pp.(print_list_pre (constant_formatted "@\n- ") print_id_value)
    (Mstr.bindings elts);
  res

let debug_files ((files, _) as res) =
  let print_file = print_model_file ~filter_similar:false ~print_attrs:true
      ~print_model_value in
   Debug.dprintf debug "@[<v>Files:@ %a@]@."
     (Pp.print_list Pp.newline print_file) (Mstr.bindings files);
   res

let model_parser (raw: raw_model_parser) : model_parser =
  fun ({Printer.vc_term_loc; vc_term_attrs} as pm) str ->
  raw pm str |> debug_elements |> (* E.g. "smtv2" -> Smtv2_model_parser.parse *)
  model_files_from_raw pm |> debug_files |>
  fun (files, cnstrs) ->
  { model_files= files; model_constraints= cnstrs; vc_term_loc; vc_term_attrs }

exception KnownModelParser of string
exception UnknownModelParser of string

type reg_model_parser = Pp.formatted * model_parser

let model_parsers : reg_model_parser Hstr.t = Hstr.create 17

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s) ;
  Hstr.replace model_parsers s (desc, model_parser p)

let lookup_model_parser s =
  snd (Hstr.find_exn model_parsers (UnknownModelParser s) s)

let list_model_parsers () =
  Hstr.fold (fun k (desc, _) acc -> (k, desc) :: acc) model_parsers []

let () =
  register_model_parser
    ~desc:
      "Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ \
       support@ models."
    "no_model" (fun _ _ -> Mstr.empty, [], Sstr.empty)
