open Why3
open Term
open Ident
open Format

open Cert_syntax

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
  | Weakening_hyp of cterm * 'a ec * ident
  | Weakening_goal of cterm * 'a ec * ident

type certif_elab = unit ec

let find_ident h cta =
  match Mid.find_opt h cta with
  | Some x -> x
  | None -> verif_failed "Can't find ident in the task"

let find_goal cta =
  let _, (t, _) = Mid.(filter (fun _ (_, b) -> b) cta |> choose) in
  t


(* Run the certificate from the initial task to find intermediate terms.
   Also fills the holes with a predefined list.*)
let rec elab (cta : ctask) (r, g : certif) (fill : 'a list) : 'a ec * 'a list =
  match r with
  | Hole ->
      begin match fill with
      | [] -> failwith "Not enough to fill"
      | first::rest -> Hole_e first, rest end
  | Axiom h ->
      let t, _ = find_ident h cta in
      Axiom_e (t, h, g), fill
  | Trivial ->
      let t, pos = find_ident g cta in
      begin match t, pos with
      | CTfalse, false ->
          Trivial_hyp g, fill
      | CTtrue, true ->
          Trivial_goal g, fill
      | _ -> assert false
      end
  | Cut (a, ce1, ce2) ->
      let cta1 = Mid.add g (a, true) cta in
      let ce1, fill = elab cta1 ce1 fill in
      let cta2 = Mid.add g (a, false) cta in
      let ce2, fill = elab cta2 ce2 fill in
      Cut_e (a, g, ce1, g, ce2), fill
  | Split (c1, c2) ->
      let t, pos = find_ident g cta in
      begin match t, pos with
      | CTbinop (Tor, a, b), false | CTbinop (Tand, a, b), true ->
          let cta1 = Mid.add g (a, pos) cta in
          let ce1, fill = elab cta1 c1 fill in
          let cta2 = Mid.add g (b, pos) cta in
          let ce2, fill = elab cta2 c2 fill in
          let pack = (a, b, g, ce1, g, ce2, g) in
          if pos then Split_hyp pack, fill
          else Split_goal pack, fill
      | _ -> assert false
      end
  | Unfold c ->
      let t, pos = find_ident g cta in
      begin match t with
      | CTbinop (Tiff, a, b) ->
          let imp_pos = CTbinop (Timplies, a, b) in
          let imp_neg = CTbinop (Timplies, b, a) in
          let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
          let cta = Mid.add g unfolded_iff cta in
          let ce, fill = elab cta c fill in
          let pack = (a, b, g, ce, g) in
          if pos then Unfold_iff_goal pack, fill
          else Unfold_iff_hyp pack, fill
      | CTbinop (Timplies, a, b) ->
          let unfolded_imp = CTbinop (Tor, CTnot a, b), pos in
          let cta = Mid.add g unfolded_imp cta in
          let ce, fill = elab cta c fill in
          let pack = (a, b, g, ce, g) in
          if pos then Unfold_arr_goal pack, fill
          else Unfold_arr_hyp pack, fill
      | _ -> verif_failed "Nothing to unfold" end
  | Swap_neg c ->
      let a, pos = find_ident g cta in
      let neg_a = match a with CTnot t -> t | t -> CTnot t in
      let cta = Mid.add g (neg_a, not pos) cta in
      let ce, fill = elab cta c fill in
      let pack = (a, g, ce, g) in
      let is_neg_a = match a with CTnot _ -> true | _ -> false in
      if is_neg_a
      then if pos
           then Swap_neg_neg_goal pack, fill
           else Swap_neg_neg_hyp  pack, fill
      else if pos
           then Swap_neg_goal pack, fill
           else Swap_neg_hyp  pack, fill
  | Destruct (h1, h2, c) ->
      let t, pos = find_ident g cta in
      begin match t, pos with
      | CTbinop (Tand, a, b), false | CTbinop (Tor, a, b), true ->
          let cta = Mid.remove g cta
                    |> Mid.add h1 (a, pos)
                    |> Mid.add h2 (b, pos) in
          let ce, fill = elab cta c fill in
          let pack = (a, b, h1, h2, ce, g) in
          if pos then Destruct_goal pack, fill
          else Destruct_hyp pack, fill
      | _ -> assert false
      end
  | Weakening c ->
      let a, pos = find_ident g cta in
      let cta = Mid.remove g cta in
      let c, fill = elab cta c fill in
      if pos
      then Weakening_goal (a, c, g), fill
      else Weakening_hyp  (a, c, g), fill
  | _ -> assert false


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
let str i = id_unique ip i

let print_op fmt = function
  | Tand -> fprintf fmt "and"
  | Tor -> fprintf fmt "or"
  | Timplies -> fprintf fmt "imp"
  | Tiff -> failwith "iff not supported"


let rec print_term fmt = function
  | CTfvar i -> fprintf fmt "%s" (str i)
  | CTbinop (op, ct1, ct2) ->
      fprintf fmt "(%a %a %a)"
        print_op op
        print_term ct1
        print_term ct2
  | CTnot ct -> fprintf fmt "(not %a)"
                  print_term ct
  | CTfalse -> fprintf fmt "false"
  | CTtrue -> fprintf fmt "true"
  | _ -> assert false

(* on [e1; ...; en], print_list gives :
   e1 sep ... en sep
 *)
let print_list sep pe fmt l =
  List.iter (fun h -> fprintf fmt "%a%s" pe h sep) l

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

let print_task fmt cts =
  let tp = snd (List.split cts) @ [CTfalse] in
  print_list_pre "imp" print_term fmt tp

let rec fvars_term = function
  | CTfvar i -> Sid.singleton i
  | CTbinop (_, ct1, ct2) -> Sid.union (fvars_term ct1) (fvars_term ct2)
  | CTfalse | CTtrue -> Sid.empty
  | CTnot ct -> fvars_term ct
  | _ -> assert false

let fvars_task cts =
  List.fold_left (fun acc (_, t) -> Sid.union acc (fvars_term t))
    Sid.empty cts

let fvars_str init_t res_t =
  List.fold_left (fun acc t -> Sid.union acc (fvars_task t))
    (fvars_task init_t) res_t
  |> Sid.elements
  |> List.map str


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


let ts (ct : ctask) =
  Mid.bindings ct
  |> List.map (fun (k, (cte, pos)) -> (k, if pos then CTnot cte else cte))

let print fmt init_t res_t certif =
  let init_ts = ts init_t in
  let res_ts = List.map ts res_t in
  let fv = fvars_str init_ts res_ts in
  (* The type we need to check is inhabited *)
  let p_type fmt () =
    print_list " -> " (fun _ -> fprintf fmt "(%s : Prop)") fmt fv;
    fprintf fmt "prf (%a)"
      (print_list_pre "imp" print_task) (res_ts @ [init_ts]) in
  let task_syms = let gs = gen_sym "task" in
                  List.map (fun _ -> gs ()) res_ts in
  (* applied_tasks are used to fill the holes *)
  let applied_tasks =
    List.map2 (fun s t ->
        let res_str = s::List.map (fun (i, _) -> str i) t in
        print_list " " (fun fmt -> fprintf fmt "%s") str_formatter res_str;
        flush_str_formatter ())
      task_syms
      res_ts in
  let cert, _ = elab init_t certif applied_tasks in
  (* The term that has the correct type *)
  let p_term fmt () =
    let vars = fv @ task_syms @ List.map (fun (i, _) -> str i) init_ts in
    print_list " => " (fun fmt -> fprintf fmt "%s") fmt vars;
    print_certif fmt cert in
  fprintf fmt "#CHECK (%a) :\n       (%a).@."
    p_term ()
    p_type ()

let checker_dedukti certif init_t res_t =
  let oc = open_out "/tmp/check_line.dk" in
  let fmt = formatter_of_out_channel oc in
  print fmt (translate_task init_t) (List.map translate_task res_t) certif;
  close_out oc;
  Sys.command "cat FO.dk > /tmp/check_all.dk" |> ignore;
  Sys.command "cat /tmp/check_line.dk >> /tmp/check_all.dk" |> ignore;
  Sys.command "dkcheck /tmp/check_all.dk 2> /dev/null | head -n 1 > /tmp/result.log" |> ignore;
  let ic = Scanf.Scanning.open_in "/tmp/result.log" in
  Scanf.bscanf ic "%s" (fun s -> if s <> "YES" then verif_failed ("Dedukti returns : " ^ s));
  res_t



