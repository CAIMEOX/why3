open Why3
open Term
open Ident
open Format

open Cert_abstract
open Cert_certificates

(* Define an elaborated type of certificate. This is usefull to have access to
   all the terms we need when printing to a Dedukti file *)

type 'a ec = (* elaborated certificate *)
  | Hole_e of 'a (* So we can fill the holes with the remaining tasks. Corresponds to Hole *)
  | Axiom_e of cterm * ident * ident
  | Trivial_hyp of ident
  | Trivial_goal of ident
  | Cut_e of cterm * ident * 'a ec * ident * 'a ec
  | Split_hyp  of (cterm * cterm * ident * 'a ec * ident * 'a ec * ident)
  | Split_goal of (cterm * cterm * ident * 'a ec * ident * 'a ec * ident)
  | Unfold_iff_hyp of (cterm * cterm * ident * 'a ec * ident)
  | Unfold_iff_goal of (cterm * cterm * ident * 'a ec * ident)
  | Unfold_arr_hyp of (cterm * cterm * ident * 'a ec * ident)
  | Unfold_arr_goal of (cterm * cterm * ident * 'a ec * ident)
  | Swap_neg_neg_hyp of (cterm * ident * 'a ec * ident)
  | Swap_neg_hyp of (cterm * ident * 'a ec * ident)
  | Swap_neg_goal of (cterm * ident * 'a ec * ident)
  | Swap_neg_neg_goal of (cterm * ident * 'a ec * ident)
  | Destruct_goal of (cterm * cterm * ident * ident * 'a ec * ident)
  | Destruct_hyp  of (cterm * cterm * ident * ident * 'a ec * ident)
  | Construct_goal of cterm * cterm * ident * 'a ec * ident * ident
  | Weakening_hyp of cterm * 'a ec * ident
  | Weakening_goal of cterm * 'a ec * ident
  | Intro_quant_hyp of (cterm * ident * ident * 'a ec * ident)
  | Intro_quant_goal of (cterm * ident * ident * 'a ec * ident)
  | Inst_quant_goal of (cterm * cterm * ident * 'a ec * ident)
  | Inst_quant_hyp of (cterm * cterm * ident * 'a ec * ident)

type certif_elab = unit ec

let find_goal cta =
  let _, (t, _) = Mid.(filter (fun _ (_, b) -> b) cta |> choose) in
  t

(* Run the certificate from the initial task to find intermediate terms.
   Also fills the holes with a predefined list.*)
let rec elab (cta : ctask) (c : core_certif) (fill : 'a list) : 'a ec * 'a list =
  match c with
  | Nc ->
      verif_failed "No certificates for this case"
  | Hole ->
      begin match fill with
      | [] -> verif_failed "Not enough to fill"
      | first::rest -> Hole_e first, rest end
  | Axiom (h, g) ->
      let t, _ = find_ident "axiom" h cta in
      Axiom_e (t, h, g), fill
  | Trivial i ->
      let t, pos = find_ident "trivial" i cta in
      begin match t, pos with
      | CTfalse, false ->
          Trivial_hyp i, fill
      | CTtrue, true ->
          Trivial_goal i, fill
      | _ -> assert false
      end
  | Cut (i, a, ce1, ce2) ->
      let cta1 = Mid.add i (a, true) cta in
      let ce1, fill = elab cta1 ce1 fill in
      let cta2 = Mid.add i (a, false) cta in
      let ce2, fill = elab cta2 ce2 fill in
      Cut_e (a, i, ce1, i, ce2), fill
  | Let _ -> verif_failed "Some Let left"
  | Split (i, c1, c2) ->
      let t, pos = find_ident "split" i cta in
      begin match t, pos with
      | CTbinop (Tor, a, b), false | CTbinop (Tand, a, b), true ->
          let cta1 = Mid.add i (a, pos) cta in
          let ce1, fill = elab cta1 c1 fill in
          let cta2 = Mid.add i (b, pos) cta in
          let ce2, fill = elab cta2 c2 fill in
          let pack = (a, b, i, ce1, i, ce2, i) in
          if pos then Split_goal pack, fill
          else Split_hyp pack, fill
      | _ -> assert false
      end
  | Unfold (i, c) ->
      let t, pos = find_ident "unfold" i cta in
      begin match t with
      | CTbinop (Tiff, a, b) ->
          let imp_pos = CTbinop (Timplies, a, b) in
          let imp_neg = CTbinop (Timplies, b, a) in
          let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
          let cta = Mid.add i unfolded_iff cta in
          let ce, fill = elab cta c fill in
          let pack = (a, b, i, ce, i) in
          if pos then Unfold_iff_goal pack, fill
          else Unfold_iff_hyp pack, fill
      | CTbinop (Timplies, a, b) ->
          let unfolded_imp = CTbinop (Tor, CTnot a, b), pos in
          let cta = Mid.add i unfolded_imp cta in
          let ce, fill = elab cta c fill in
          let pack = (a, b, i, ce, i) in
          if pos then Unfold_arr_goal pack, fill
          else Unfold_arr_hyp pack, fill
      | _ -> verif_failed "Nothing to unfold" end
  | Swap_neg (i, c) ->
      let a, pos = find_ident "swap_neg" i cta in
      let underlying_a, neg_a, is_neg_a = match a with
        | CTnot t -> t, t, true
        | t -> t, CTnot t, false in
      let cta = Mid.add i (neg_a, not pos) cta in
      let ce, fill = elab cta c fill in
      let pack = (underlying_a, i, ce, i) in
      if is_neg_a
      then if pos
           then Swap_neg_neg_goal pack, fill
           else Swap_neg_neg_hyp  pack, fill
      else if pos
           then Swap_neg_goal pack, fill
           else Swap_neg_hyp  pack, fill
  | Destruct (i, j1, j2, c) ->
      let t, pos = find_ident "destruct" i cta in
      begin match t, pos with
      | CTbinop (Tand, a, b), false | CTbinop (Tor, a, b), true ->
          let cta = Mid.remove i cta
                    |> Mid.add j1 (a, pos)
                    |> Mid.add j2 (b, pos) in
          let ce, fill = elab cta c fill in
          let pack = (a, b, j1, j2, ce, i) in
          if pos then Destruct_goal pack, fill
          else Destruct_hyp pack, fill
      | _ -> assert false
      end
  (* | Construct (i1, i2, j, c) ->
   *     let a, pos1 = find_ident "construct1" i1 cta in
   *     let b, pos2 = find_ident "construct2" i2 cta in
   *     if pos1 = pos2
   *     then
   *       let t = if pos1 then CTbinop (Tor, a, b) else CTbinop (Tand, a, b) in
   *       let cta = Mid.remove i1 cta
   *                 |> Mid.remove i2
   *                 |> Mid.add j (t, pos1) in
   *       let ce, fill = elab cta c fill in
   *       Construct_goal (a, b, j, ce, i1, i2), fill
   *     else verif_failed "Can't construct" *)
  | Weakening (i, c) ->
      let a, pos = find_ident "weakening" i cta in
      let cta = Mid.remove i cta in
      let c, fill = elab cta c fill in
      if pos
      then Weakening_goal (a, c, i), fill
      else Weakening_hyp  (a, c, i), fill
  | Intro_quant (i, y, c) ->
      let t, pos = find_ident "intro_quant" i cta in
      begin match t, pos with
      | CTquant (CTexists, p), false | CTquant (CTforall, p), true ->
          if mem y t then verif_failed "non-free variable" else
            let cta = Mid.add i (ct_open p (CTfvar y), pos) cta in
            let ce, fill = elab cta c fill in
            let p' = CTquant (CTlambda, p) in
            if pos then Intro_quant_goal (p', y, i, ce, i), fill
            else Intro_quant_hyp (p', y, i, ce, i), fill
      | _ -> verif_failed "Nothing to introduce" end
  | Inst_quant (i, j, t_inst, c) ->
      let p, pos = find_ident "inst_quant" i cta in
      begin match p, pos with
      | CTquant (CTforall, p), false | CTquant (CTexists, p), true ->
          let cta = Mid.add j (ct_open p t_inst, pos) cta in
          let ce, fill = elab cta c fill in
          let p' = CTquant (CTlambda, p) in
          if pos then Inst_quant_goal (p', t_inst, j, ce, i), fill
          else Inst_quant_hyp (p', t_inst, j, ce, i), fill
      | _ -> verif_failed "trying to instantiate a non-quantified hypothesis"
      end
  | Rewrite _ -> verif_failed "rewriting is not supported in Dedukti verification"


(* We represent a ctask <H₁ : A₁, ..., Hₘ : Aₘ ⊢ G₁ : B₁, ..., Gₘ : Bₘ >
   by the formula <A₁ → ... → Aₘ → ¬B₁ → ... → ¬Bₙ → ⊥ >
   As an intermediate data structure, we use a list in order to :
     • fix the order
     • remember the idents which are used to construct the proof term
 *)
type ctask_simple = (ident * cterm) list

let gen_sym s =
  let r = ref 0 in fun () ->
                   incr r;
                   s ^ string_of_int !r

let ip = create_ident_printer []
let san = sanitizer char_to_alnum char_to_alnum
let str i = id_unique ip ~sanitizer:san i

let print_op fmt = function
  | Tand -> fprintf fmt "and"
  | Tor -> fprintf fmt "or"
  | Timplies -> fprintf fmt "imp"
  | Tiff -> fprintf fmt "iff"

let rec print_term fmt = function
  | CTbvar _ -> assert false
  | CTfvar id -> fprintf fmt "%s" (str id)
  | CTbinop (op, ct1, ct2) ->
      fprintf fmt "(%a (%a) (%a))"
        print_op op
        print_term ct1
        print_term ct2
  | CTnot ct ->
      fprintf fmt "(not (%a))"
        print_term ct
  | CTfalse -> fprintf fmt "false"
  | CTtrue -> fprintf fmt "true"
  | CTapp (ct1, ct2) ->
      fprintf fmt "(%a) (%a)"
        print_term ct1
        print_term ct2
  | CTquant ((CTforall | CTexists) as q, t) ->
      let x = id_register (id_fresh "x") in
      let q_str = match q with CTforall -> "forall"
                             | CTexists -> "exists"
                             | CTlambda -> assert false in
      fprintf fmt "(%s (%s => %a))"
        q_str
        (str x)
        print_term (ct_open t (CTfvar x))
  | CTquant (CTlambda, t) ->
      let x = id_register (id_fresh "x") in
      fprintf fmt "%s => %a"
        (str x)
        print_term (ct_open t (CTfvar x))

(* on [e1; ...; en], print_list gives :
   e1 sep ... en sep
 *)
let print_list sep pe fmt l =
  List.iter (fun h -> fprintf fmt "%a%s" pe h sep) l

let print_list_inter sep pe fmt l =
  pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "%s" sep)
    pe fmt l

(* on [e1; ...; en], print_list_pre gives :
   sep (e1) (sep (e2) ...)
 *)
let rec print_list_pre sep pe fmt = function
  | [] -> failwith "cannot print empty list with preorder"
  | [x] -> pe fmt x
  | h::t -> fprintf fmt "%s (%a) (%a)"
              sep
              pe h
              (print_list_pre sep pe) t



type typ =
  | Term
  | Prop
  | Arrow of typ * typ

let rec print_type fmt = function
  | Term -> fprintf fmt "Term"
  | Prop -> fprintf fmt "Prop"
  | Arrow (t1, t2) -> fprintf fmt "%a -> %a"
                        print_type t1
                        print_type t2

let rec collect typ = function
  | CTbvar _  -> Mid.empty
  | CTfvar id -> Mid.singleton id typ
  | CTapp (ct1, ct2) -> Mid.set_union (collect (Arrow (Term, typ)) ct1) (collect Term ct2)
  | CTbinop (_, ct1, ct2) -> Mid.set_union (collect typ ct1) (collect typ ct2)
  | CTquant (_, ct)
  | CTnot ct -> collect typ ct
  | CTtrue | CTfalse -> Mid.empty

let collect_stask (ta : ctask_simple) =
  List.fold_left (fun acc (_, ct) -> Mid.set_union acc (collect Prop ct))
    Mid.empty ta

let print_task fmt (fv, ts) =
  fprintf fmt "(";
  print_list " -> " (fun fmt (id, typ) ->
      fprintf fmt "%s : (%a)"
        (str id)
        print_type typ) fmt fv;
  let tp = snd (List.split ts) @ [CTfalse] in
  fprintf fmt "prf (%a)"
    (print_list_pre "imp" print_term) tp;
  fprintf fmt ")"

let nopt = function
  | Some x -> x
  | None -> failwith "not an option"

let rec print_certif fmt = function
  | Hole_e s ->
      fprintf fmt "%s" s
  | Axiom_e (t, h, g) ->
      fprintf fmt "axiom (%a) %s %s"
        print_term t
        (str h)
        (str g)
  | Trivial_hyp g ->
      fprintf fmt "trivial_hyp %s" (str g)
  | Trivial_goal g ->
      fprintf fmt "trivial_goal %s" (str g)
  | Cut_e (a, g1, ce1, g2, ce2) ->
      fprintf fmt "cut (%a) (%s => %a) (%s => %a)"
        print_term a
        (str g1) print_certif ce1
        (str g2) print_certif ce2
  | Split_hyp (a, b, h1, c1, h2, c2, g) ->
      fprintf fmt "split_hyp (%a) (%a) (%s => %a) (%s => %a) %s"
        print_term a
        print_term b
        (str h1) print_certif c1
        (str h2) print_certif c2
        (str g)
  | Split_goal (a, b, h1, c1, h2, c2, g) ->
      fprintf fmt "split_goal (%a) (%a) (%s => %a) (%s => %a) %s"
        print_term a
        print_term b
        (str h1) print_certif c1
        (str h2) print_certif c2
        (str g)
  | Unfold_iff_hyp (a, b, h, c, g) ->
      fprintf fmt "unfold_iff_hyp (%a) (%a) (%s => %a) %s"
        print_term a
        print_term b
        (str h) print_certif c
        (str g)
  | Unfold_iff_goal (a, b, h, c, g) ->
      fprintf fmt "unfold_iff_goal (%a) (%a) (%s => %a) %s"
        print_term a
        print_term b
        (str h) print_certif c
        (str g)
  | Unfold_arr_hyp (a, b, h, c, g) ->
      fprintf fmt "unfold_arr_hyp (%a) (%a) (%s => %a) %s"
        print_term a
        print_term b
        (str h) print_certif c
        (str g)
  | Unfold_arr_goal (a, b, h, c, g) ->
      fprintf fmt "unfold_arr_goal (%a) (%a) (%s => %a) %s"
        print_term a
        print_term b
        (str h) print_certif c
        (str g)
  | Swap_neg_neg_hyp (a, h, c, g) ->
      fprintf fmt "swap_neg_neg_hyp (%a) (%s => %a) %s"
        print_term a
        (str h) print_certif c
        (str g)
  | Swap_neg_hyp (a, h, c, g) ->
      fprintf fmt "swap_neg_hyp (%a) (%s => %a) %s"
        print_term a
        (str h) print_certif c
        (str g)
  | Swap_neg_goal (a, h, c, g) ->
      fprintf fmt "swap_neg_goal (%a) (%s => %a) %s"
        print_term a
        (str h) print_certif c
        (str g)
  | Swap_neg_neg_goal (a, h, c, g) ->
      fprintf fmt "swap_neg_neg_goal (%a) (%s => %a) %s"
        print_term a
        (str h) print_certif c
        (str g)
  | Destruct_hyp (a, b, h1, h2, c, g) ->
      fprintf fmt "destruct_hyp (%a) (%a) (%s => %s => %a) %s"
        print_term a
        print_term b
        (str h1) (str h2) print_certif c
        (str g)
  | Destruct_goal (a, b, h1, h2, c, g) ->
      fprintf fmt "destruct_goal (%a) (%a) (%s => %s => %a) %s"
        print_term a
        print_term b
        (str h1) (str h2) print_certif c
        (str g)
  | Construct_goal (a, b, j, c, i1, i2) ->
      fprintf fmt "construct_goal (%a) (%a) (%s => %a) %s %s"
        print_term a
        print_term b
        (str j) print_certif c
        (str i1)
        (str i2)
  | Weakening_hyp (a, c, g) ->
      fprintf fmt "weakening_hyp (%a) (%a) %s"
        print_term a
        print_certif c
        (str g)
  | Weakening_goal (a, c, g) ->
      fprintf fmt "weakening_goal (%a) (%a) %s"
        print_term a
        print_certif c
        (str g)
  | Intro_quant_hyp (p, y, h, c, g) ->
      fprintf fmt "intro_quant_hyp (%a) (%s => %s => %a) %s"
        print_term p
        (str y) (str h) print_certif c
        (str g)
  | Intro_quant_goal (p, y, h, c, g) ->
      fprintf fmt "intro_quant_goal (%a) (%s => %s => %a) %s"
        print_term p
        (str y) (str h) print_certif c
        (str g)
  | Inst_quant_goal (p, t, h, c, g) ->
      fprintf fmt "inst_quant_goal (%a) (%a) (%s => %s => %a) %s"
        print_term p
        print_term t
        (str g) (str h) print_certif c
        (str g)
  | Inst_quant_hyp (p, t, h, c, g) ->
      fprintf fmt "inst_quant_hyp (%a) (%a) (%s => %s => %a) %s"
        print_term p
        print_term t
        (str g) (str h) print_certif c
        (str g)


let fv_ts (ct : ctask) =
  let encode_neg (k, (ct, pos)) = k, if pos then CTnot ct else ct in
  let ts = Mid.bindings ct
           |> List.map encode_neg in
  let fv = collect_stask ts in
  fv, ts

let print fmt init_ct res_ct certif =
  let resm  = List.map fv_ts res_ct in
  let res = List.map (fun (fv, ts) -> Mid.bindings fv, ts) resm in
  let fvi, tsi = fv_ts init_ct in
  let fv = List.fold_left (fun acc (fv, _) -> Mid.set_union acc fv) fvi resm in
  let init = Mid.bindings fv, tsi in
  (* The type we need to check is inhabited *)
  let p_type fmt () =
    print_list_inter " -> "
      print_task
      fmt
      (res @ [init]) in
  let task_syms = let gs = gen_sym "task" in
                  List.map (fun _ -> gs ()) res in
  (* applied_tasks are used to fill the holes *)
  let applied_tasks =
    List.map2 (fun s (fv_t, t) ->
        let fv, _ = List.split fv_t in
        let hyp, _ = List.split t in
        let res_str = s :: List.map str (fv @ hyp) in
        print_list " " (fun fmt -> fprintf fmt "%s") str_formatter res_str;
        flush_str_formatter ())
      task_syms
      res in
  let cert, _ = elab init_ct certif applied_tasks in
  (* The term that has the correct type *)
  let p_term fmt () =
    let fv, ts = init in
    let fv_ids, _ = List.split fv in
    let hyp_ids, _ = List.split ts in
    let vars = task_syms @ List.map str (fv_ids @ hyp_ids) in
    print_list " => " (fun fmt -> fprintf fmt "%s") fmt vars;
    print_certif fmt cert in
  fprintf fmt "#CHECK (%a) :\n       (%a).@."
    p_term ()
    p_type ()

let checker_dedukti certif init_ct res_ct =
  try
    let oc = open_out "/tmp/check_line.dk" in
    let fmt = formatter_of_out_channel oc in
    let fo = Filename.(concat Config.datadir (concat "dedukti" "FO.dk")) in
    print fmt init_ct res_ct certif;
    close_out oc;
    Sys.command ("cat " ^ fo ^ " > /tmp/check_all.dk") |> ignore;
    Sys.command "cat /tmp/check_line.dk >> /tmp/check_all.dk" |> ignore;
    Sys.command "dkcheck /tmp/check_all.dk 2> /dev/null | head -n 1 > /tmp/result.log" |> ignore;
    let ic = Scanf.Scanning.open_in "/tmp/result.log" in
    Scanf.bscanf ic "%s" (fun s -> if s <> "YES" then verif_failed ("Dedukti returns : " ^ s))
  with e -> raise (Trans.TransFailure ("Cert_verif_dedukti.checker_dedukti", e))
