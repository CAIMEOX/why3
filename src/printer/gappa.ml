(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** Gappa printer *)

open Format
open Pp
open Printer
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let syntactic_transform transf =
  Trans.on_meta meta_syntax_logic (fun metas ->
    let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [MAls ls; MAstr _] -> Sls.add ls acc
      | _ -> assert false) Sls.empty metas in
    transf (fun ls -> Sls.mem ls symbols))

let () =
  Trans.register_transform "abstract_unknown_lsymbols"
    (syntactic_transform Abstraction.abstraction);
  Trans.register_transform "simplify_unknown_lsymbols"
    (syntactic_transform (fun check_ls -> Trans.goal (fun pr f ->
      [create_prop_decl Pgoal pr (Simplify_formula.fmla_cond_subst
        (fun t _ -> match t.t_node with
          | Tconst _ | Tapp(_,[]) -> false
          | Tapp(ls,_) -> not (check_ls ls)
          | _ -> true) f)
      ])))

(* Gappa pre-compilation *)

type info = {
  info_symbols : Sid.t;
  info_ops_of_rel : (string * string * string) Mls.t;
  info_syn : string Mid.t;
  info_rem : Sid.t;
}

let int_minus = ref ps_equ
let real_minus = ref ps_equ

(** lsymbol, ""/"not ", op, rev_op *)
let arith_meta = register_meta "gappa arith"
  [MTlsymbol;MTstring;MTstring;MTstring]


let find_th env file th =
  let theory = Env.find_theory env [file] th in
  fun id -> Theory.ns_find_ls theory.Theory.th_export [id]

let get_info env task =
  (* unary minus for constants *)
  int_minus := find_th env "int" "Int" "prefix -";
  real_minus := find_th env "real" "Real" "prefix -";
  (* handling of inequalities *)
  let ops = on_meta arith_meta (fun acc meta_arg ->
    match meta_arg with
    | [MAls ls; MAstr s; MAstr op; MAstr rev_op] ->
        Mls.add ls (s,op,rev_op) acc
    | _ -> assert false) Mls.empty task in
  (* sets of known symbols *)
  let syn = get_syntax_map task in
  let symb = Mid.map (Util.const ()) syn in
  let symb = Mls.fold (fun ls _ acc -> Sid.add ls.ls_name acc) ops symb in
  let symb = Sid.add ps_equ.ls_name symb in
  {
    info_symbols = symb;
    info_ops_of_rel = ops;
    info_syn = syn;
    info_rem = get_remove_set task;
  }

(* Gappa printing *)

let ident_printer =
  let bls = [
      "sqrt"; "fma";
      "float"; "fixed"; "int";
      "homogen80x"; "homogen80x_init"; "float80x";
      "add_rel"; "sub_rel"; "mul_rel"; "fma_rel";
    ] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let constant_value t =
  match t.t_node with
(*
    | Tconst (ConstInt s) -> s
    | Tconst (ConstReal r) -> sprintf "%a" Pretty.print_const r
*)
    | Tconst c ->
        fprintf str_formatter "%a" Pretty.print_const c;
        flush_str_formatter ()
    | Tapp(ls, [{ t_node = Tconst c}])
        when ls_equal ls !int_minus || ls_equal ls !real_minus ->
        fprintf str_formatter "-%a" Pretty.print_const c;
        flush_str_formatter ()
    | _ -> raise Not_found

(* terms *)

let rec print_term info fmt t =
  let term = print_term info in
  match t.t_node with
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp ( { ls_name = id } ,[] ) ->
    begin match query_syntax info.info_syn id with
      | Some s -> syntax_arguments s term fmt []
      | None -> print_ident fmt id
    end
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        | None ->
            unsupportedTerm t
              ("gappa: function '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
  | Tlet _ -> unsupportedTerm t
      "gappa: you must eliminate let in term"
  | Tif _ -> unsupportedTerm t
      "gappa: you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t
      "gappa: you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "gappa : you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)


(* predicates *)

let rec print_fmla info fmt f =
  let term = print_term info in
  let fmla = print_fmla info in
  match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
    begin match query_syntax info.info_syn id with
      | Some s -> syntax_arguments s term fmt []
      | None -> print_ident fmt id
    end
  | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
      (* TODO: distinguish between type of t1 and t2
         the following is OK only for real of integer
      *)
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%a in [%s,%s]" term t2 c1 c1
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%a in [%s,%s]" term t1 c2 c2
        with Not_found ->
          fprintf fmt "%a - %a in [0,0]" term t1 term t2
      end
  | Tapp (ls, [t1;t2]) when Mls.mem ls info.info_ops_of_rel ->
      let s,op,rev_op = try Mls.find ls info.info_ops_of_rel
        with Not_found -> assert false
      in
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%s%a %s %s" s term t2 rev_op c1
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%s%a %s %s" s term t1 op c2
        with Not_found ->
          fprintf fmt "%s%a - %a %s 0" s term t1 term t2 op
      end
  | Tapp (ls, tl) ->
      begin match query_syntax info.info_syn ls.ls_name with
        | Some s -> syntax_arguments s term fmt tl
        | None ->
            unsupportedTerm f
              ("gappa: predicate '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
  | Tquant (_q, _fq) ->
      unsupportedTerm f
        "gappa: quantifiers are not supported"
(*
      let q = match q with Tforall -> "forall" | Texists -> "exists" in
      let vl, tl, f = t_open_quant fq in
      let forall fmt v =
        fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type info) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
*)
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "(%a /\\@ %a)" fmla f1 fmla f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "(%a \\/@ %a)" fmla f1 fmla f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" fmla f1 fmla f2
  | Tbinop (Tiff, _f1, _f2) ->
      unsupportedTerm f
        "gappa: connector <-> is not supported"
  | Tnot f ->
      fprintf fmt "not %a" fmla f
  | Ttrue ->
      fprintf fmt "(0 in [0,0])"
  | Tfalse ->
      fprintf fmt "(1 in [0,0])"
  | Tif (_f1, _f2, _f3) ->
      unsupportedTerm f
        "gappa: you must eliminate if in formula"
  | Tlet _ -> unsupportedTerm f
      "gappa: you must eliminate let in formula"
  | Tcase _ -> unsupportedTerm f
      "gappa: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

(*
let print_decl (* ?old *) info fmt d =
  match d.d_node with
  | Dtype _ -> ()
(*
unsupportedDecl d
      "gappa : type declarations are not supported"
*)
  | Dlogic _ -> ()
(*
unsupportedDecl d
      "gappa : logic declarations are not supported"
*)
  | Dind _ -> unsupportedDecl d
      "gappa: inductive definitions are not supported"
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "# hypothesis '%a'@\n" print_ident pr.pr_name;
      fprintf fmt "@[<hv 2>%a ->@]@\n" (print_fmla info) f
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "# goal '%a'@\n" print_ident pr.pr_name;
(*
      fprintf fmt "@[<hv 2>{ %a@ }@]@\n" (print_fmla info) f
*)
      fprintf fmt "@[<hv 2>%a@]@\n" (print_fmla info) f
  | Dprop ((Plemma|Pskip), _, _) ->
      unsupportedDecl d
        "gappa: lemmas are not supported"
*)

(*
let print_decl ?old:_ info fmt =
  catch_unsupportedDecl (print_decl (* ?old *) info fmt)

let print_decls ?old info fmt dl =
  fprintf fmt "@[<hov>{ %a }@\n@]" (print_list nothing (print_decl ?old info)) dl
*)

exception AlreadyDefined

let filter_hyp info defs eqs hyps pr f =
  match f.t_node with
  | Tapp(ls,[t1;t2]) when ls == ps_equ ->
      let try_equality t1 t2 =
        match t1.t_node with
          | Tapp(l,[]) ->
              if Hid.mem defs l.ls_name then raise AlreadyDefined;
              Hid.add defs l.ls_name ();
              t_s_fold (fun _ _ -> ()) (fun _ ls -> Hid.replace defs ls.ls_name ()) () t2;
              ((pr,t1,t2)::eqs, hyps)
          | _ -> raise AlreadyDefined in
      begin try
        try_equality t1 t2
      with AlreadyDefined -> try
        try_equality t2 t1
      with AlreadyDefined ->
        (eqs, (pr,f)::hyps)
      end
  (* todo: support more kinds of hypotheses *)
  | Tapp(ls,_) when Sid.mem ls.ls_name info.info_symbols ->
      (eqs, (pr,f)::hyps)
  | _ -> (eqs,hyps)

type filter_goal =
  | Goal_good of Decl.prsymbol * term
  | Goal_bad of string
  | Goal_none

let filter_goal pr f =
  match f.t_node with
    | Tapp(ps,[]) -> Goal_bad ("symbol " ^ ps.ls_name.Ident.id_string ^ " unknown")
        (* todo: filter more goals *)
    | _ -> Goal_good(pr,f)

let prepare info defs ((eqs,hyps,goal) as acc) d =
  match d.d_node with
    | Dtype _ -> acc
    | Dlogic _ -> acc
    | Dind _ ->
        unsupportedDecl d
          "please remove inductive definitions before calling gappa printer"
    | Dprop (Paxiom, pr, f) ->
        let (eqs,hyps) = filter_hyp info defs eqs hyps pr f in (eqs,hyps,goal)
    | Dprop (Pgoal, pr, f) ->
        begin
          match goal with
            | Goal_none -> (eqs,hyps,filter_goal pr f)
            | _ -> assert false
        end
    | Dprop ((Plemma|Pskip), _, _) ->
        unsupportedDecl d
          "gappa: lemmas are not supported"

let print_equation info fmt (pr,t1,t2) =
  fprintf fmt "# equation '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a = %a ;@\n" (print_term info) t1 (print_term info) t2

let print_hyp info fmt (pr,f) =
  fprintf fmt "# hypothesis '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a ->@\n" (print_fmla info) f

let print_goal info fmt g =
  match g with
    | Goal_good(pr,f) ->
        fprintf fmt "# goal '%a'@\n" print_ident pr.pr_name;
        fprintf fmt "%a@\n" (print_fmla info) f
    | Goal_bad msg ->
        fprintf fmt "# (unsupported kind of goal: %s)@\n" msg;
        fprintf fmt "1 in [0,0]@\n"
    | Goal_none ->
        fprintf fmt "# (no goal at all ??)@\n";
        fprintf fmt "1 in [0,0]@\n"

let print_task env pr thpr ?old:_ fmt task =
  forget_all ident_printer;
  let info = get_info env task in
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let equations,hyps,goal =
    List.fold_left (prepare info (Hid.create 17)) ([],[],Goal_none) (Task.task_decls task)
  in
  List.iter (print_equation info fmt) (List.rev equations);
  fprintf fmt "@[<v 2>{ %a%a}@\n@]" (print_list nothing (print_hyp info)) hyps
    (print_goal info) goal
(*
  print_decls ?old info fmt (Task.task_decls task)
*)

let () = register_printer "gappa" print_task


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
