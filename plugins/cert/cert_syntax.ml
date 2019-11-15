open Why3

open Term
open Ident
open Decl
open Theory
open Task
open Format


(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cquant = CTforall | CTexists | CTlambda

type cterm =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTapp of cterm * cterm
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of cquant * cterm (* quantifier binding *)
  | CTnot of cterm
  | CTtrue
  | CTfalse

type ctask = (cterm * bool) Mid.t
(* We will denote a ctask <M> by <Γ ⊢ Δ> where :
   • <Γ> contains all the declarations <H : P> where <H> is mapped to <(P, false)> in <M>
   • <Δ> contains all the declarations <H : P> where <H> is mapped to <(P, true)> in <M>
*)

type dir = Left | Right
type path = dir list

type certif = rule * ident
(* The ident indicates where to apply the rule.
   In the following rules, we will call it <G> *)

(* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>,
   it is defined as the function <Cert_verif.check_certif> *)
and rule =
  | Hole
  (* Hole ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | Axiom of ident
  (* Axiom H ⇓ (Γ, H : P ⊢ Δ, G : P) ≜  [] *)
  | Trivial
  (* Trivial ⇓ (Γ, G : false ⊢ Δ) ≜  [] *)
  (* Trivial ⇓ (Γ ⊢ Δ, G : true ) ≜  [] *)
  | Cut of cterm * certif * certif
  (* Cut (A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ, G : A ⊢ Δ)) *)
  | Split of certif * certif
  (* Split (c₁, c₂) ⇓ (Γ, G : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, G : A ⊢ Δ))  @  (c₂ ⇓ (Γ, G : B ⊢ Δ)) *)
  (* Split (c₁, c₂) ⇓ (Γ ⊢ Δ, G : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ ⊢ Δ, G : B)) *)
  | Unfold of certif
  (* Unfold c ⇓ (Γ, G : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, G : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, G : (A → B) ∧ (B → A)) *)
  (* Unfold c ⇓ (Γ, G : A → B ⊢ Δ) ≜  c ⇓ (Γ, G : ¬A ∨ B ⊢ Δ)*)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A → B) ≜  c ⇓ (Γ ⊢ Δ, G : ¬A ∨ B)*)
  | Swap_neg of certif
  (* Swap_neg c ⇓ (Γ, G : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, G : A)  *)
  (* Swap_neg c ⇓ (Γ, G : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, G : ¬A) *)
  (* Swap_neg c ⇓ (Γ ⊢ Δ, G : A ) ≜  c ⇓ (Γ, G : ¬A ⊢ Δ) *)
  (* Swap_neg c ⇓ (Γ ⊢ Δ, G : ¬A) ≜  c ⇓ (Γ, G : A ⊢ Δ)  *)
  | Destruct of ident * ident * certif
  (* Destruct (H₁, H₂, c) ⇓ (Γ, G : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, H₁ : A, H₂ : B ⊢ Δ) *)
  (* Destruct (H₁, H₂, c) ⇓ (Γ ⊢ Δ, G : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, H₁ : A, H₂ : B) *)
  | Weakening of certif
  (* Weakening c ⇓ (Γ ⊢ Δ, G : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening c ⇓ (Γ, G : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Intro_quant of ident * certif
  (* Intro_quant (y, c) ⇓ (Γ, G : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : P y ⊢ Δ) (y fresh) *)
  (* Intro_quant (y, c) ⇓ (Γ ⊢ Δ, G : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : P y) (y fresh) *)
  | Inst_quant of ident * cterm * certif
  (* Inst_quant (H, t, c) ⇓ (Γ, G : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : ∀ x. P x, H : P t ⊢ Δ) *)
  (* Inst_quant (H, t, c) ⇓ (Γ ⊢ Δ, G : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : ∃ x. P x, H : P t) *)
  | Rewrite of ident * path * bool * certif list
  (* Rewrite (H, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <G> an equality that is in <H>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)

let hole = Hole, id_register (id_fresh "dummy_hole_ident")

(** Translating a Why3 <task> into a <ctask> *)

let translate_quant = function
  | Tforall -> CTforall
  | Texists -> CTexists

let rec translate_term_rec bv_lvl lvl t =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  match t.t_node with
  | Tvar v ->
      let ids = v.vs_name in
      begin match Mid.find_opt ids bv_lvl with
        | None -> CTfvar ids
        | Some lvl_s ->
            assert (lvl_s <= lvl); (* a variable should not be above its definition *)
            CTbvar (lvl - lvl_s)
      end
  | Tapp (ls, lt) ->
      let ids = ls.ls_name in
      let vs = match Mid.find_opt ids bv_lvl with
        | None -> CTfvar ids
        | Some lvl_s ->
            assert (lvl_s <= lvl); (* a variable should not be above its definition *)
            CTbvar (lvl - lvl_s) in
      List.fold_left (fun acc t -> CTapp (acc, translate_term_rec bv_lvl lvl t))
        vs lt
  | Tbinop (op, t1, t2) ->
      let ct1 = translate_term_rec bv_lvl lvl t1 in
      let ct2 = translate_term_rec bv_lvl lvl t2 in
      CTbinop (op, ct1, ct2)
  | Tquant (q, tq) ->
      let vs, _, t = t_open_quant tq in
      assert (List.length vs = 1);
      let ids = (List.hd vs).vs_name in
      let lvl = lvl + 1 in
      let ctq = translate_term_rec (Mid.add ids lvl bv_lvl) lvl t in
      CTquant (translate_quant q, ctq)
  | Tnot t -> CTnot (translate_term_rec bv_lvl lvl t)
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | Tconst _ -> invalid_arg "Cert_syntax.translate_term Tconst"
  | Tif _ -> invalid_arg "Cert_syntax.translate_term Tif"
  | Tlet _ -> invalid_arg "Cert_syntax.translate_term Tlet"
  | Tcase _ -> invalid_arg "Cert_syntax.translate_term Tcase"
  | Teps _ -> invalid_arg "Cert_syntax.translate_term Teps"


let translate_term t =
  translate_term_rec Mid.empty 0 t

let translate_decl decl =
  match decl.d_node with
  | Dprop (Pgoal, pr, t) ->
       Mid.singleton pr.pr_name (translate_term t, true)
  | Dprop (_, pr, t) ->
      Mid.singleton pr.pr_name (translate_term t, false)
  | _ -> Mid.empty

let translate_tdecl td =
  match td.td_node with
  | Decl decl -> translate_decl decl
  | _ -> Mid.empty

let rec translate_task_acc acc = function
  | Some {task_decl = td; task_prev = task} ->
      let new_acc = Mid.set_union acc (translate_tdecl td) in
      translate_task_acc new_acc task
  | None -> acc

let translate_task task =
  translate_task_acc Mid.empty task


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

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prr fmt = function
  | Hole -> fprintf fmt "Hole"
  | Axiom h -> fprintf fmt "Axiom@ %a" pri h
  | Trivial -> fprintf fmt "Trivial"
  | Cut (a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a)@]" pcte a prc c1 prc c2
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Unfold c -> fprintf fmt "Unfold@ %a" prc c
  | Swap_neg c -> fprintf fmt "Swap_neg@ %a" prc c
  | Destruct (h1, h2, c) -> fprintf fmt "Destruct @[(%a,@ %a,@ %a)@]"
                              pri h1 pri h2 prc c
  | Weakening c -> fprintf fmt "Weakening@ %a" prc c
  | Intro_quant (name, c) -> fprintf fmt "Intro_quant @[(%a,@ %a)@]" pri name prc c
  | Inst_quant (i, t, c) -> fprintf fmt "Inst_quant @[(%a,@ %a,@ %a)@]" pri i pcte t prc c
  | Rewrite (h, p, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %b,@ %a)@]"
        pri h (prle "; " prd) p rev (prle "; " prc) lc
and prc fmt (r, g) =
  fprintf fmt "(%a, %a)" prr r pri g


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


(** We equip existing transformations with a certificate <certif> *)

type ctrans = task -> task list * certif

exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)
(** Utility functions on <cterm> and <ctask> *)

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

(* bound variable substitution *)
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

(* checks if the term is locally closed *)
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

(* free variable substitution *)
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

(* variable closing *)
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

(* free variable with respect to a term *)
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

(* checks if the transformation closes the task *)
let rec nohole (r, _) =
  match r with
  | Hole -> false
  | Axiom _ | Trivial -> true
  | Cut (_, c1, c2)
  | Split (c1, c2) -> nohole c1 && nohole c2
  | Unfold c
  | Swap_neg c
  | Destruct (_, _, c)
  | Weakening c
  | Intro_quant (_, c)
  | Inst_quant (_, _, c) -> nohole c
  | Rewrite (_, _, _, lc) -> List.for_all nohole lc

(* separates hypotheses and goals *)
let split_cta cta =
  let open Mid in
  fold (fun h (ct, pos) (mh, mg) ->
      if pos then mh, add h (ct, pos) mg
      else add h (ct, pos) mh, mg)
    cta (empty, empty)

(* creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let mh, mg = split_cta cta in
  let hg, _ = Mid.choose mg in
  fun ct -> Mid.add hg (ct, true) mh

(** Create a certified transformation from a transformation with a certificate *)

let checker_ctrans checker (ctr : ctrans) init_t =
  let t1 = Unix.gettimeofday () in
  let res_t, certif = ctr init_t in
  let t2 = Unix.gettimeofday () in
  let res = checker certif init_t res_t in
  let t3 = Unix.gettimeofday () in
  let open Format in
  let out = open_out "/tmp/time_transfo.log" in
  let fmt = formatter_of_out_channel out in
  fprintf fmt "temps de la transformation : %f\ntemps de la vérification : %f@."
    (t2 -. t1) (t3 -. t2);
  close_out out;
  res

