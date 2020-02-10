open Format

open Why3
open Term
open Ident
open Cert_syntax


(** Printing of <cterm> and <ctask> : for debugging purposes *)

let ip = create_ident_printer []

let pri fmt i =
  fprintf fmt "%s" (id_unique ip i)
and prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"
and prle sep pre fmt le =
  let prl = pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt sep) pre in
  fprintf fmt "[%a]" prl le

let rec pcte fmt = function
  | CTbvar lvl -> pp_print_int fmt lvl
  | CTfvar i -> pri fmt i
  | CTapp (f, arg) -> fprintf fmt "%a@ %a" pcte f pcte arg
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
  | CTquant (q, ct) -> begin match q with
                       | CTforall -> fprintf fmt "∀. %a" pcte ct
                       | CTexists -> fprintf fmt "∃. %a" pcte ct
                       | CTlambda -> fprintf fmt "λ. %a" pcte ct
                       end
  | CTnot t -> fprintf fmt "(not %a)" pcte t
  | CTtrue -> fprintf fmt "true"
  | CTfalse -> fprintf fmt "false"
and pro fmt = function
  | Tor -> fprintf fmt "\\/"
  | Tand -> fprintf fmt "/\\"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

let pte = Pretty.print_term

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prc fmt = function
  | Nc -> fprintf fmt "No_certif"
  | Hole -> fprintf fmt "Hole"
  | Axiom (h, g) -> fprintf fmt "Axiom @[(%a,@ %a)@]" pri h pri g
  | Trivial i -> fprintf fmt "Trivial %a" pri i
  | Cut (i, a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a,@ %a)@]" pri i pte a prc c1 prc c2
  | Split (i, c1, c2) -> fprintf fmt "Split @[(%a,@ %a,@ %a)@]" pri i prc c1 prc c2
  | Unfold (i, c) -> fprintf fmt "Unfold @[(%a,@ %a)@]" pri i prc c
  | Swap_neg (i, c) -> fprintf fmt "Swap_neg @[(%a,@ %a)@]" pri i prc c
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct @[(%a,@ %a,@ %a,@ %a)@]" pri i pri j1 pri j2 prc c
  | Construct (i1, i2, j, c) ->
      fprintf fmt "Construct @[(%a,@ %a,@ %a,@ %a)@]" pri i1 pri i2 pri j prc c
  | Weakening (i, c) -> fprintf fmt "Weakening@ @[(%a,@ %a)@]" pri i prc c
  | Intro_quant (i, y, c) -> fprintf fmt "Intro_quant @[(%a,@ %a,@ %a)@]" pri i pri y prc c
  | Inst_quant (i, j, t, c) -> fprintf fmt "Inst_quant @[(%a,@ %a,@ %a,@ %a)@]" pri i pri j pte t prc c
  | Rewrite (i, j, path, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %a,@ %b,@ %a)@]"
        pri i pri j (prle "; " prd) path rev (prle "; " prc) lc


let prpos fmt = function
  | true  -> fprintf fmt "GOAL| "
  | false -> fprintf fmt "HYP | "

let prmid fmt mid =
  Mid.iter (fun h (cte, pos) -> fprintf fmt "%a%a : %a\n" prpos pos pri h pcte cte) mid

let pcta fmt cta =
  fprintf fmt "%a\n" prmid cta

let print_ctasks filename lcta =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." (prle "==========\n" pcta) lcta;
  close_out oc

let find_ident s h cta =
  match Mid.find_opt h cta with
  | Some x -> x
  | None ->
      fprintf str_formatter "%s : Can't find ident %a in the task" s pri h;
      verif_failed (flush_str_formatter ())

(** Utility functions of Cert_syntax types *)

(* Structural functions on certificates *)
let rec map_cert fid fct c =
  let m = map_cert fid fct in
  match c with
  | Nc | Hole -> c
  | Trivial i -> Trivial (fid i)
  | Axiom (h, g) -> Axiom (fid h, fid g)
  | Cut (i, a, c1, c2) -> Cut (fid i, fct a, m c1, m c2)
  | Split (i, c1, c2) -> Split (fid i, m c1, m c2)
  | Unfold (i, c) -> Unfold (fid i, m c)
  | Swap_neg (i, c) -> Swap_neg (fid i, m c)
  | Destruct (i, j1, j2, c) -> Destruct (fid i, fid j1, fid j2, m c)
  | Construct (i1, i2, j, c) -> Construct (fid i1, fid i2, fid j, m c)
  | Weakening (i, c) -> Weakening (fid i, m c)
  | Intro_quant (i, y, c) -> Intro_quant (fid i, fid y, m c)
  | Inst_quant (i, j, ct, c) -> Inst_quant (fid i, fid j, fct ct, m c)
  | Rewrite (i, j, p, b, cl) -> Rewrite (fid i, fid j, p, b, List.map m cl)

let propagate f g (c : 'a cert) = match c with
  | (Hole | Nc | Axiom _ | Trivial _) as c -> c
  | Unfold (i, c) -> Unfold (i, f c)
  | Cut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Cut (i, g a, f1, f2)
  | Split (i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Split (i, f1, f2)
  | Swap_neg (i, c) -> Swap_neg (i, f c)
  | Destruct (i, j1, j2, c) -> Destruct (i, j1, j2, f c)
  | Construct (i1, i2, j, c) -> Construct (i1, i2, j, f c)
  | Weakening (i, c) -> Weakening (i, f c)
  | Intro_quant (i, y, c) -> Intro_quant (i, y, f c)
  | Inst_quant (i, j, t, c) -> Inst_quant (i, j, g t, f c)
  | Rewrite (i, j, path, rev, lc) -> Rewrite (i, j, path, rev, List.map f lc)

let rec fill stream = function
  | Hole -> Stream.next stream
  | c -> propagate (fill stream) (fun t -> t) c

let (|>>) c1 c2 =
  let c2_stream = Stream.from (fun _ -> Some c2) in
  fill c2_stream c1

let (|>>>) c1 lc2 =
  let lc2_stream = Stream.of_list lc2 in
  fill lc2_stream c1


(* Equality *)
let rec cterm_equal t1 t2 = match t1, t2 with
  | CTbvar lvl1, CTbvar lvl2 -> lvl1 = lvl2
  | CTfvar i1, CTfvar i2 -> id_equal i1 i2
  | CTapp (tl1, tr1), CTapp (tl2, tr2) ->
      cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTbinop (op1, tl1, tr1), CTbinop (op2, tl2, tr2) ->
      op1 = op2 && cterm_equal tl1 tl2 && cterm_equal tr1 tr2
  | CTquant (q1, t1), CTquant (q2, t2) when q1 = q2 -> cterm_equal t1 t2
  | CTtrue, CTtrue | CTfalse, CTfalse -> true
  | CTnot t1, CTnot t2 -> cterm_equal t1 t2
  | _ -> false

let cterm_pos_equal (t1, p1) (t2, p2) =
  cterm_equal t1 t2 && p1 = p2

let ctask_equal cta1 cta2 = Mid.equal cterm_pos_equal cta1 cta2

(* Bound variable substitution *)
let rec ct_bv_subst k u t = match t with
  | CTbvar i -> if i = k then u else t
  | CTfvar _ -> t
  | CTapp (t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_bv_subst k u t1 in
      let nt2 = ct_bv_subst k u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_bv_subst (k+1) u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_bv_subst k u t)
  | CTtrue -> CTtrue
  | CTfalse -> CTfalse

let ct_open t u = ct_bv_subst 0 u t

(* Checks if the term is locally closed *)
let locally_closed =
  let di = id_register (id_fresh "dummy_locally_closed_ident") in
  let rec term = function
    | CTbvar _ -> false
    | CTapp (t1, t2)
    | CTbinop (_, t1, t2) -> term t1 && term t2
    | CTquant (_, t) -> term (ct_open t (CTfvar di))
    | CTnot t -> term t
    | CTfvar _ | CTtrue | CTfalse -> true
  in
  term

(* Free variable substitution *)
let rec ct_fv_subst z u t = match t with
  | CTfvar x -> if id_equal z x then u else t
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_subst z u t1 in
      let nt2 = ct_fv_subst z u t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) ->
      let nt = ct_fv_subst z u t in
      CTquant (q, nt)
  | CTnot t -> CTnot (ct_fv_subst z u t)
  | CTbvar _ | CTtrue | CTfalse -> t

(* Variable closing *)
let rec ct_fv_close x k t = match t with
  | CTbvar _ | CTtrue | CTfalse-> t
  | CTfvar y -> if id_equal x y then CTbvar k else t
  | CTnot t -> CTnot (ct_fv_close x k t)
  | CTapp (t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTapp (nt1, nt2)
  | CTbinop (op, t1, t2) ->
      let nt1 = ct_fv_close x k t1 in
      let nt2 = ct_fv_close x k t2 in
      CTbinop (op, nt1, nt2)
  | CTquant (q, t) -> CTquant (q, ct_fv_close x (k+1) t)

let ct_close x t = ct_fv_close x 0 t

(* Find free variable with respect to a term *)
let rec mem_cont x t cont = match t with
  | CTfvar y -> cont (id_equal x y)
  | CTapp (t1, t2)
  | CTbinop (_, t1, t2) ->
      mem_cont x t1 (fun m1 ->
      mem_cont x t2 (fun m2 ->
      cont (m1 || m2)))
  | CTquant (_, t)
  | CTnot t -> mem_cont x t cont
  | CTbvar _ | CTtrue | CTfalse -> cont false

let mem x t = mem_cont x t (fun x -> x)

(* Separates hypotheses and goals *)
let split_cta cta =
  let open Mid in
  fold (fun h (ct, pos) (mh, mg) ->
      if pos then mh, add h (ct, pos) mg
      else add h (ct, pos) mh, mg)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let mh, mg = split_cta cta in
  let hg, _ = Mid.choose mg in
  fun ct -> Mid.add hg (ct, true) mh

let rec make_core init_t res_t c =
  propagate (make_core init_t res_t) translate_term c
