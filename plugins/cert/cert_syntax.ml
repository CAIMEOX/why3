open Why3

open Term
open Ident
open Decl
open Theory
open Task
open Format


(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip transformations with a certificate <certif> *)

type cterm =
  | CTbvar of int (* bound variables use De Bruijn indices *)
  | CTfvar of ident (* free variables use a name *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)
  | CTquant of quant * cterm (* forall binding *)
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
  | Skip
  (* Skip ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | Axiom of ident
  (* Axiom H ⇓ (Γ, H : P ⊢ Δ, G : P) ≜  [] *)
  | Trivial
  (* Trivial ⇓ (Γ, G : false ⊢ Δ) ≜  [] *)
  (* Trivial ⇓ (Γ ⊢ Δ, G : true ) ≜  [] *)
  | Cut of ident * cterm * certif * certif
  (* Cut (H, A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, H : A))  @  (c₂ ⇓ (Γ, H : A ⊢ Δ)) *)
  | Split of certif * certif
  (* Split (c₁, c₂) ⇓ (Γ, G : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, G : A ⊢ Δ))  @  (c₂ ⇓ (Γ, G : B ⊢ Δ)) *)
  (* Split (c₁, c₂) ⇓ (Γ ⊢ Δ, G : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ ⊢ Δ, G : B)) *)
  (* Split (c₁, c₂) ⇓ (Γ, G : A → B ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ, G : B ⊢ Δ)) *)
  | Unfold of certif
  (* Unfold c ⇓ (Γ, G : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, G : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, G : (A → B) ∧ (B → A)) *)
  | Destruct of ident * ident * certif
  (* Destruct (H₁, H₂, c) ⇓ (Γ, G : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, H₁ : A, H₂ : B ⊢ Δ) *)
  (* Destruct (H₁, H₂, c) ⇓ (Γ ⊢ Δ, G : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, H₁ : A, H₂ : B) *)
  (* Destruct (H₁, H₂, c) ⇓ (Γ ⊢ Δ, G : A → B) ≜  c ⇓ (Γ, H₁ : A ⊢ Δ, H₂ : B) *)
  | Dir of dir * certif
  (* Dir (Left, c) ⇓ (Γ ⊢ Δ, G : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, G : A) *)
  (* Dir (Left, c) ⇓ (Γ, G : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, G : A ⊢ Δ) *)
  (* and similar definition for Right instead of Left *)
  | Intro of ident * certif
  (* Intro (y, c) ⇓ (Γ, G : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : P y ⊢ Δ) (y fresh) *)
  (* Intro (y, c) ⇓ (Γ ⊢ Δ, G : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : P y) (y fresh) *)
  | Weakening of certif
  (* Weakening c ⇓ (Γ ⊢ Δ, G : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening c ⇓ (Γ, G : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Inst of ident * cterm * certif
  (* Inst (H, t, c) ⇓ (Γ, G : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, G : ∀ x. P x, H : P t ⊢ Δ) *)
  (* Inst (H, t, c) ⇓ (Γ ⊢ Δ, G : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, G : ∃ x. P x, H : P t) *)
  | Rewrite of ident * path * bool * certif list
  (* Rewrite (H, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <G> an equality that is in <H>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)

let skip = Skip, id_register (id_fresh "dummy_skip_ident")

(** Translating a Why3 <task> into a <ctask> *)

let rec translate_term_rec bv_lvl lvl t =
  (* level <lvl> is the number of forall above in the whole term *)
  (* <bv_lvl> is mapping bound variables to their respective level *)
  match t.t_node with
  | Tapp (ls, []) ->
      let ids = ls.ls_name in
      begin match Mid.find_opt ids bv_lvl with
      | None -> CTfvar ids
      | Some lvl_s ->
          assert (lvl_s <= lvl); (* a variable should not be above its definition *)
          CTbvar (lvl - lvl_s) end
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
      CTquant (q, ctq)
  | Tnot t -> CTnot (translate_term_rec bv_lvl lvl t)
  | Ttrue -> CTtrue
  | Tfalse -> CTfalse
  | _ -> invalid_arg "Cert_syntax.translate_term"

let translate_term t = translate_term_rec Mid.empty 0 t

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
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
  | CTquant (q, ct) -> begin match q with
                       | Tforall -> fprintf fmt "∀. %a" pcte ct
                       | Texists -> fprintf fmt "∃. %a" pcte ct
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
  | Skip -> fprintf fmt "Skip"
  | Axiom h -> fprintf fmt "Axiom@ %a" pri h
  | Trivial -> fprintf fmt "Trivial"
  | Cut (h, a, c1, c2) -> fprintf fmt "Cut @[(%a,@ %a,@ %a,@ %a)@]" pri h pcte a prc c1 prc c2
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Unfold c -> fprintf fmt "Unfold@ %a" prc c
  | Destruct (h1, h2, c) -> fprintf fmt "Destruct @[(%a,@ %a,@ %a)@]"
                              pri h1 pri h2 prc c
  | Dir (d, c) -> fprintf fmt "Dir @[(%a,@ %a)@]" prd d prc c
  | Intro (name, c) -> fprintf fmt "Intro @[(%a,@ %a)@]" pri name prc c
  | Weakening c -> fprintf fmt "Weakening@ %a" prc c
  | Inst (i, t, c) -> fprintf fmt "Inst @[(%a,@ %a,@ %a)@]" pri i pcte t prc c
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

(** Create a certified transformation from a transformation with a certificate *)

let checker_ctrans check_certif ctask_equal (ctr : ctrans) task =
  try let (ltask, c) : task list * certif = ctr task in
      let cta = translate_task task in
      print_certif "/tmp/certif.log" c;
      print_ctasks "/tmp/init_ctask.log" [cta];
      let lcta : ctask list = check_certif cta c in
      if Lists.equal ctask_equal lcta (List.map translate_task ltask)
      then ltask
      else begin
          print_ctasks "/tmp/from_trans.log" (List.map translate_task ltask);
          print_ctasks "/tmp/from_cert.log" lcta;
          verif_failed "Replaying certif gives different result, log available" end
  with e -> raise (Trans.TransFailure ("Cert_syntax.checker_ctrans", e))

