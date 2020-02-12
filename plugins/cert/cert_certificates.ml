open Format

open Why3
open Decl
open Term
open Ident

open Cert_abstract

type dir = Left | Right
type path = dir list

(** We equip existing transformations with a certificate <certif> *)

type ('a, 'b) cert = (* 'a is used to designate an hypothesis, 'b is used for terms *)
(* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>.
   For more details, take a look at the OCaml implementation <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole
  (* Hole ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | Cut of 'a * 'b * ('a, 'b) cert * ('a, 'b) cert
  (* Cut (I, A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ, I : A ⊢ Δ)) *)
  | Let of 'b * 'a * ('a, 'b) cert
  | Axiom of 'a * 'a
  (* Axiom (H, G) ⇓ (Γ, H : A ⊢ Δ, G : A) ≜  [] *)
  | Trivial of 'a
  (* Trivial I ⇓ (Γ, I : false ⊢ Δ) ≜  [] *)
  (* Trivial I ⇓ (Γ ⊢ Δ, I : true ) ≜  [] *)
  | Split of 'a * ('a, 'b) cert * ('a, 'b) cert
  (* Split (I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, I : A ⊢ Δ))  @  (c₂ ⇓ (Γ, I : B ⊢ Δ)) *)
  (* Split (I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ ⊢ Δ, I : B)) *)
  | Unfold of 'a * ('a, 'b) cert
  (* Unfold (I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  (* Unfold (I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | Swap_neg of 'a * ('a, 'b) cert
  (* Swap_neg (I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* Swap_neg (I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* Swap_neg (I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  (* Swap_neg (I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | Destruct of 'a * 'a * 'a * ('a, 'b) cert
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  (* | Construct of ident * ident * ident * 'a cert (\* should be derivable from Cut and Split *\)
   * (\* Construct (I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜ c ⇓ (Γ ⊢ Δ, J : A ∧ B) *\)
   * (\* Construct (I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜ c ⇓ (Γ, J : A ∧ B ⊢ Δ) *\) *)
  | Weakening of 'a * ('a, 'b) cert
  (* Weakening (I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening (I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Intro_quant of 'a * ident * ('a, 'b) cert
  (* Intro_quant (I, y, c) ⇓ (Γ, I : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : P y ⊢ Δ) (y fresh) *)
  (* Intro_quant (I, y, c) ⇓ (Γ ⊢ Δ, I : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : P y) (y fresh) *)
  | Inst_quant of 'a * 'a * 'b * ('a, 'b) cert
  (* Inst_quant (I, J, t, c) ⇓ (Γ, I : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : ∀ x. P x, J : P t ⊢ Δ) *)
  (* Inst_quant (I, J, t, c) ⇓ (Γ ⊢ Δ, I : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : ∃ x. P x, J : P t) *)
  | Rewrite of 'a * 'a * path * bool * ('a, 'b) cert list
  (* Rewrite (I, J, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <I> an equality that is in <J>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)


type certif = (prsymbol, term) cert
type core_certif = (ident, cterm) cert

type ctrans = certif ctransformation


(** Printing of <cterm> and <ctask> : for debugging purposes *)

let ip = create_ident_printer []

let pri fmt i =
  fprintf fmt "%s" (id_unique ip i)

let prpr fmt pr =
  pri fmt pr.pr_name

let prd fmt = function
  | Left -> fprintf fmt "Left"
  | Right -> fprintf fmt "Right"

let prle sep pre fmt le =
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
  | Cut (i, a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a,@ %a)@]" prpr i pte a prc c1 prc c2
  | Let (x, i, c) -> fprintf fmt "Let @[(%a,@ %a,@ %a)@]" pte x prpr i prc c
  | Axiom (h, g) -> fprintf fmt "Axiom @[(%a,@ %a)@]" prpr h prpr g
  | Trivial i -> fprintf fmt "Trivial %a" prpr i
  | Split (i, c1, c2) -> fprintf fmt "Split @[(%a,@ %a,@ %a)@]" prpr i prc c1 prc c2
  | Unfold (i, c) -> fprintf fmt "Unfold @[(%a,@ %a)@]" prpr i prc c
  | Swap_neg (i, c) -> fprintf fmt "Swap_neg @[(%a,@ %a)@]" prpr i prc c
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct @[(%a,@ %a,@ %a,@ %a)@]" prpr i prpr j1 prpr j2 prc c
  (* | Construct (i1, i2, j, c) ->
   *     fprintf fmt "Construct @[(%a,@ %a,@ %a,@ %a)@]" pri i1 pri i2 pri j prc c *)
  | Weakening (i, c) -> fprintf fmt "Weakening@ @[(%a,@ %a)@]" prpr i prc c
  | Intro_quant (i, y, c) -> fprintf fmt "Intro_quant @[(%a,@ %a,@ %a)@]" prpr i pri y prc c
  | Inst_quant (i, j, t, c) -> fprintf fmt "Inst_quant @[(%a,@ %a,@ %a,@ %a)@]" prpr i prpr j pte t prc c
  | Rewrite (i, j, path, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %a,@ %b,@ %a)@]"
        prpr i prpr j (prle "; " prd) path rev (prle "; " prc) lc


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

(** Utility functions on certificate, cterm and ctask *)

(* Structural functions on certificates *)
let propagate f fid fte = function
  | (Hole | Nc)  as c -> c
  | Axiom (h, g) -> Axiom (fid h, fid g)
  | Trivial i -> Trivial (fid i)
  | Cut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Cut (fid i, fte a, f1, f2)
  | Let (x, i, c) -> Let (fte x, fid i, f c)
  | Unfold (i, c) -> Unfold (fid i, f c)
  | Split (i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Split (fid i, f1, f2)
  | Swap_neg (i, c) -> Swap_neg (fid i, f c)
  | Destruct (i, j1, j2, c) -> Destruct (fid i, fid j1, fid j2, f c)
  | Weakening (i, c) -> Weakening (fid i, f c)
  | Intro_quant (i, y, c) -> Intro_quant (fid i, y, f c)
  | Inst_quant (i, j, t, c) -> Inst_quant (fid i, fid j, fte t, f c)
  | Rewrite (i, j, path, rev, lc) -> Rewrite (fid i, fid j, path, rev, List.map f lc)

let rec fill stream = function
  | Hole -> Stream.next stream
  | c -> propagate (fill stream) (fun t -> t) (fun t -> t) c

let (|>>) c1 c2 =
  let c2_stream = Stream.from (fun _ -> Some c2) in
  fill c2_stream c1

let (|>>>) c1 lc2 =
  let lc2_stream = Stream.of_list lc2 in
  fill lc2_stream c1

let new_let_var str =
  let ls = create_lsymbol (id_fresh str) [] None in
  t_app ls [] None

let construct i1 i2 j c =
  let ti1 = new_let_var "i1" in
  let ti2 = new_let_var "i2" in
  Let (ti1, i1, Hole)
  |>> Let (ti2, i2, Hole)
  |>> Cut (j, t_and ti1 ti2, c, Hole)



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

let ct_subst ct m =
  Mid.fold ct_fv_subst ct m

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

let rec abstract_types c =
    propagate abstract_types (fun pr -> pr.pr_name) abstract_term c

let rec eliminate_let (cta : ctask) (m : cterm Mid.t) = function
    | (Nc | Hole | Axiom _ | Trivial _) as c -> c
    | Cut (i, a, c1, c2) ->
        let cta1 = Mid.add i (a, true) cta in
        let cta2 = Mid.add i (a, false) cta in
        let c1 = eliminate_let cta1 m c1 in
        let c2 = eliminate_let cta2 m c2 in
        let a = ct_subst m a in
        Cut (i, a, c1, c2)
    | Let (x, i, c) ->
        let x = match x with
                | CTfvar i -> i
                | _ -> failwith "" in
        let a, _ = Mid.find i cta in
        let m = Mid.add x a m in
        eliminate_let cta m c
    | Split (i, c1, c2) ->
        let t, pos = find_ident "split" i cta in
        let cta1, cta2 = match t, pos with
          | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false ->
              let cta1 = Mid.add i (t1, pos) cta in
              let cta2 = Mid.add i (t2, pos) cta in
              cta1, cta2
          | _ -> verif_failed "Not splittable" in
        let c1 = eliminate_let cta1 m c1 in
        let c2 = eliminate_let cta2 m c2 in
        Split (i, c1, c2)
    | Unfold (i, c) ->
        let t, pos = find_ident "unfold" i cta in
        let cta =  match t with
          | CTbinop (Tiff, t1, t2) ->
              let imp_pos = CTbinop (Timplies, t1, t2) in
              let imp_neg = CTbinop (Timplies, t2, t1) in
              let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
              Mid.add i unfolded_iff cta
          | CTbinop (Timplies, t1, t2) ->
              let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
              Mid.add i unfolded_imp cta
          | _ -> verif_failed "Nothing to unfold" in
        let c = eliminate_let cta m c in
        Unfold (i, c)
    | Swap_neg (i, c) ->
        let t, pos = find_ident "swap_neg" i cta in
        let neg_t = match t with CTnot t -> t | t -> CTnot t in
        let cta = Mid.add i (neg_t, not pos) cta in
        let c = eliminate_let cta m c in
        Swap_neg (i, c)
    | Destruct (i, j1, j2, c) ->
        let t, pos = find_ident "destruct" i cta in
        let cta = match t, pos with
          | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true ->
              Mid.remove i cta
              |> Mid.add j1 (t1, pos)
              |> Mid.add j2 (t2, pos)
          | _ -> verif_failed "Nothing to destruct" in
        let c = eliminate_let cta m c in
        Destruct (i, j1, j2, c)
    | Weakening (i, c) ->
        let cta = Mid.remove i cta in
        let c = eliminate_let cta m c in
        Weakening (i, c)
    | Intro_quant (i, y, c) ->
        let t, pos = find_ident "intro_quant" i cta in
        let cta = match t, pos with
          | CTquant (CTforall, t), true | CTquant (CTexists, t), false ->
              if mem y t then verif_failed "non-free variable" else
                Mid.add i (ct_open t (CTfvar y), pos) cta
          | _ -> verif_failed "Nothing to introduce" in
        let c = eliminate_let cta m c in
        Intro_quant (i, y, c)
    | Inst_quant (i, j, t_inst, c) ->
        let t, pos = find_ident "inst_quant" i cta in
        let cta = match t, pos with
          | CTquant (CTforall, t), false | CTquant (CTexists, t), true ->
              Mid.add j (ct_open t t_inst, pos) cta
          | _ -> verif_failed "trying to instantiate a non-quantified hypothesis" in
        let c = eliminate_let cta m c in
        Inst_quant (i, j, t_inst, c)
    | Rewrite (i, j, path, rev, lc) as c -> c
                                         (* TODO *)
        (* let lcta = check_rewrite cta rev j i [] path in
         * List.map2 ccheck lc lcta |> List.concat *)

let make_core init_ct _ c =
  eliminate_let init_ct Mid.empty (abstract_types c)
