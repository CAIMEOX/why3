open Why3
open Term
open Ident
open Theory
open Decl
open Task


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

type 'a cert =
(* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>.
   For more details, take a look at the OCaml implementation <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole
  (* Hole ⇓ (Γ ⊢ Δ) ≜  [Γ ⊢ Δ] *)
  | Axiom of ident * ident
  (* Axiom (H, G) ⇓ (Γ, H : A ⊢ Δ, G : A) ≜  [] *)
  | Trivial of ident
  (* Trivial I ⇓ (Γ, I : false ⊢ Δ) ≜  [] *)
  (* Trivial I ⇓ (Γ ⊢ Δ, I : true ) ≜  [] *)
  | Cut of ident * 'a * 'a cert * 'a cert
  (* Cut (I, A, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ, I : A ⊢ Δ)) *)
  | Split of ident * 'a cert * 'a cert
  (* Split (I, c₁, c₂) ⇓ (Γ, I : A ∨ B ⊢ Δ) ≜  (c₁ ⇓ (Γ, I : A ⊢ Δ))  @  (c₂ ⇓ (Γ, I : B ⊢ Δ)) *)
  (* Split (I, c₁, c₂) ⇓ (Γ ⊢ Δ, I : A ∧ B) ≜  (c₁ ⇓ (Γ ⊢ Δ, I : A))  @  (c₂ ⇓ (Γ ⊢ Δ, I : B)) *)
  | Unfold of ident * 'a cert
  (* Unfold (I, c) ⇓ (Γ, I : A ↔ B ⊢ Δ) ≜  c ⇓ (Γ, I : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A ↔ B) ≜  c ⇓ (Γ ⊢ Δ, I : (A → B) ∧ (B → A)) *)
  (* Unfold (I, c) ⇓ (Γ, I : A → B ⊢ Δ) ≜  c ⇓ (Γ, I : ¬A ∨ B ⊢ Δ)*)
  (* Unfold (I, c) ⇓ (Γ ⊢ Δ, I : A → B) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A ∨ B)*)
  | Swap_neg of ident * 'a cert
  (* Swap_neg (I, c) ⇓ (Γ, I : ¬A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, I : A)  *)
  (* Swap_neg (I, c) ⇓ (Γ, I : A ⊢ Δ ) ≜  c ⇓ (Γ ⊢ Δ, I : ¬A) *)
  (* Swap_neg (I, c) ⇓ (Γ ⊢ Δ, I : A ) ≜  c ⇓ (Γ, I : ¬A ⊢ Δ) *)
  (* Swap_neg (I, c) ⇓ (Γ ⊢ Δ, I : ¬A) ≜  c ⇓ (Γ, I : A ⊢ Δ)  *)
  | Destruct of ident * ident * ident * 'a cert
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ, I : A ∧ B ⊢ Δ) ≜  c ⇓ (Γ, J₁ : A, J₂ : B ⊢ Δ) *)
  (* Destruct (I, J₁, J₂, c) ⇓ (Γ ⊢ Δ, I : A ∨ B) ≜  c ⇓ (Γ ⊢ Δ, J₁ : A, J₂ : B) *)
  | Construct of ident * ident * ident * 'a cert (* should be derivable from Cut and Split *)
  (* Construct (I₁, I₂, J, c) ⇓ (Γ ⊢ Δ, I₁ : A, I₂ : B) ≜ c ⇓ (Γ ⊢ Δ, J : A ∧ B) *)
  (* Construct (I₁, I₂, J, c) ⇓ (Γ, I₁ : A, I₂ : B ⊢ Δ) ≜ c ⇓ (Γ, J : A ∧ B ⊢ Δ) *)
  | Weakening of ident * 'a cert
  (* Weakening (I, c) ⇓ (Γ ⊢ Δ, I : A) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening (I, c) ⇓ (Γ, I : A ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Intro_quant of ident * ident * 'a cert
  (* Intro_quant (I, y, c) ⇓ (Γ, I : ∃ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : P y ⊢ Δ) (y fresh) *)
  (* Intro_quant (I, y, c) ⇓ (Γ ⊢ Δ, I : ∀ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : P y) (y fresh) *)
  | Inst_quant of ident * ident * 'a * 'a cert
  (* Inst_quant (I, J, t, c) ⇓ (Γ, I : ∀ x. P x ⊢ Δ) ≜  c ⇓ (Γ, I : ∀ x. P x, J : P t ⊢ Δ) *)
  (* Inst_quant (I, J, t, c) ⇓ (Γ ⊢ Δ, I : ∃ x. P x) ≜  c ⇓ (Γ ⊢ Δ, I : ∃ x. P x, J : P t) *)
  | Rewrite of ident * ident * path * bool * 'a cert list
  (* Rewrite (I, J, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <I> an equality that is in <J>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premises, those are then matched against the certificates <lc> *)

type certif = term cert
type core_certif = cterm cert



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

(** We equip existing transformations with a certificate <certif> *)

type ctrans = task -> task list * certif
(* = (task list * certif) trans *)
exception Certif_verification_failed of string
let verif_failed s = raise (Certif_verification_failed s)


(** Create a certified transformation from a transformation with a certificate *)

let checker_ctrans
      (make_core : task -> task list -> certif -> core_certif)
      (checker : core_certif -> task -> task list -> unit)
      (ctr : ctrans)
      (init_t : task) =
  (* let t1 = Unix.gettimeofday () in *)
  let res_t, certif = ctr init_t in
  let core_certif = make_core init_t res_t certif in
  (* let t2 = Unix.gettimeofday () in *)
  checker core_certif init_t res_t;
  (* let t3 = Unix.gettimeofday () in
   * Format.eprintf "temps de la transformation : %f\ntemps de la vérification : %f@."
   *   (t2 -. t1) (t3 -. t2); *)
  res_t
