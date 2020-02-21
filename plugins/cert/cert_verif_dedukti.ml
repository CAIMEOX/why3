open Why3
open Term
open Ident
open Format

open Cert_abstract
open Cert_certificates

let find_goal cta =
  let _, (t, _) = Mid.(filter (fun _ (_, b) -> b) cta |> choose) in
  t

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

(* on [e1; ...; en], print_list sep gives :
   e1 sep e2 sep ... en sep
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

let rstr goal = if goal then "_goal" else "_hyp"

let print_certif at fmt c =
  let s = Stream.of_list at in
  let rec pc fmt = function
  | ELet _ | EConstruct _ -> verif_failed "Construct/Let left"
  | EHole _ ->
      fprintf fmt "%s" (Stream.next s)
  | EAxiom (t, h, g) ->
      fprintf fmt "axiom (%a) %s %s"
        print_term t
        (str h)
        (str g)
  | ETrivial (goal, g) ->
      fprintf fmt "trivial%s %s" (rstr goal)
        (str g)
  | ECut (i, a, ce1, ce2) ->
      fprintf fmt "cut (%a) (%s => %a) (%s => %a)"
        print_term a
        (str i) pc ce1
        (str i) pc ce2
  | ESplit (goal, a, b, i, c1, c2) ->
      fprintf fmt "split%s (%a) (%a) (%s => %a) (%s => %a) %s" (rstr goal)
        print_term a
        print_term b
        (str i) pc c1
        (str i) pc c2
        (str i)
  | EUnfoldIff (goal, a, b, i, c) ->
      fprintf fmt "unfold_iff%s (%a) (%a) (%s => %a) %s" (rstr goal)
        print_term a
        print_term b
        (str i) pc c
        (str i)
  | EUnfoldArr (goal, a, b, i, c) ->
      fprintf fmt "unfold_arr%s (%a) (%a) (%s => %a) %s" (rstr goal)
        print_term a
        print_term b
        (str i) pc c
        (str i)
  | ESwapNeg (goal, a, i, c) ->
      fprintf fmt "swap_neg%s (%a) (%s => %a) %s" (rstr goal)
        print_term a
        (str i) pc c
        (str i)
  | ESwap (goal, a, i, c) ->
      fprintf fmt "swap%s (%a) (%s => %a) %s" (rstr goal)
        print_term a
        (str i) pc c
        (str i)
  | EDestruct (goal, a, b, i, j1, j2, c) ->
      fprintf fmt "destruct%s (%a) (%a) (%s => %s => %a) %s" (rstr goal)
        print_term a
        print_term b
        (str j1) (str j2) pc c
        (str i)
  | EWeakening (goal, a, i, c) ->
      fprintf fmt "weakening%s (%a) (%a) %s" (rstr goal)
        print_term a
        pc c
        (str i)
  | EIntroQuant (goal, p, i, y, c) ->
      fprintf fmt "intro_quant%s (%a) (%s => %s => %a) %s" (rstr goal)
        print_term p
        (str y) (str i) pc c
        (str i)
  | EInstQuant (goal, p, i, j, t, c) ->
      fprintf fmt "inst_quant%s (%a) (%a) (%s => %s => %a) %s" (rstr goal)
        print_term p
        print_term t
        (str i) (str j) pc c
        (str i)
  | ERewrite _ -> verif_failed "Rewrite is not yet supported by the Dedukti checker" in
  pc fmt c

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
  (* The term that has the correct type *)
  let p_term fmt () =
    let fv, ts = init in
    let fv_ids, _ = List.split fv in
    let hyp_ids, _ = List.split ts in
    let vars = task_syms @ List.map str (fv_ids @ hyp_ids) in
    print_list " => " (fun fmt -> fprintf fmt "%s") fmt vars;
    print_certif applied_tasks fmt certif in
  fprintf fmt "#CHECK (%a) :\n\
                      (%a).@."
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
