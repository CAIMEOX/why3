open Why3
open Term
open Ident
open Decl
open Theory
open Task
open Format


(** To certify transformations, we will represent Why3 tasks by the type <ctask>
    and we equip existing transformations with a certificate <certif> *)

type ident = Ident.ident

type binop = CTand | CTor | CTiff | CTimplies
type cterm =
  | CTapp of ident (* atomic formulas *)
  | CTbinop of binop * cterm * cterm (* application of a binary operator *)

type ctask = (cterm * bool) Mid.t
(* We will represent a ctask <M> by <Γ ⊢ Δ> where :
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
  (* Axiom H ⇓ (Γ, H : P ⊢ Δ, G : P)  ≜  [] *)
  | Split of certif * certif
  (* Split (c₁, c₂) ⇓ (Γ, G : A ∨ B ⊢ Δ)  ≜  (c₁ ⇓ (Γ, G : A ⊢ Δ))  @  (c₂ ⇓ (Γ, G : B ⊢ Δ)) *)
  (* Split (c₁, c₂) ⇓ (Γ ⊢ Δ, G : A ∧ B)  ≜  (c₁ ⇓ (Γ ⊢ Δ, G : A))  @  (c₂ ⇓ (Γ ⊢ Δ, G : B)) *)
  | Unfold of certif
  (* Unfold c ⇓ (Γ, G : A ↔ B ⊢ Δ)  ≜  c ⇓ (Γ, G : (A → B) ∧ (B → A) ⊢ Δ) *)
  (* Unfold c ⇓ (Γ ⊢ Δ, G : A ↔ B)  ≜  c ⇓ (Γ ⊢ Δ, G : (A → B) ∧ (B → A)) *)
  | Destruct of ident * ident * certif
  (* Destruct (H₁, H₂, c) ⇓ (Γ, G : A ∧ B ⊢ Δ)  ≜  c ⇓ (Γ, H₁ : A, H₂ : B ⊢ Δ) *)
  (* Destruct (H₁, H₂, c) ⇓ (Γ ⊢ Δ, G : A ∨ B)  ≜  c ⇓ (Γ ⊢ Δ, H₁ : A, H₂ : B) *)
  | Dir of dir * certif
  (* Dir (Left, c) ⇓ (Γ ⊢ Δ, G : A ∧ B)  ≜  c ⇓ (Γ ⊢ Δ, G : A) *)
  (* Dir (Left, c) ⇓ (Γ, G : A ∨ B ⊢ Δ)  ≜  c ⇓ (Γ, G : A ⊢ Δ) *)
  (* and similar definition for Right instead of Left *)
  | Intro of ident * certif
  (* Intro (H, c) ⇓ (Γ ⊢ Δ, H : A → B)  ≜  c ⇓ (Γ, H : A ⊢ Δ, G : B)  *)
  | Weakening of certif
  (* Weakening c ⇓ (Γ ⊢ Δ, G : A)  ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening c ⇓ (Γ, G : A ⊢ Δ)  ≜  c ⇓ (Γ ⊢ Δ) *)
  | Rewrite of ident * path * bool * certif list
  (* Rewrite (H, path, rev, lc) ⇓ Seq is defined as follows :
     it tries to rewrite in <G> an equality that is in <H>, following the path <path>,
     <rev> indicates if it rewrites from left to right or from right to left.
     Since <H> can have premisses, those are then matched against the certificates <lc> *)

let skip = Skip, id_register (id_fresh "dummy_skip_ident")

(** Translating a Why3 <task> to a <ctask> *)

let translate_op = function
  | Tand -> CTand
  | Tor -> CTor
  | Timplies -> CTimplies
  | Tiff -> CTiff

let rec translate_term t =
  match t.t_node with
  | Tapp (ls, []) -> CTapp ls.ls_name
  | Tbinop (op, t1, t2) -> CTbinop (translate_op op, translate_term t1, translate_term t2)
  | _ -> invalid_arg "Cert_syntax.translate_term"

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

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prc cert;
  close_out oc
and prr fmt = function
  | Skip -> fprintf fmt "Skip"
  | Axiom h -> fprintf fmt "Axiom@ %a" pri h
  | Split (c1, c2) -> fprintf fmt "Split @[(%a,@ %a)@]" prc c1 prc c2
  | Unfold c -> fprintf fmt "Unfold@ %a" prc c
  | Destruct (h1, h2, c) -> fprintf fmt "Destruct @[(%a,@ %a,@ %a)@]"
                              pri h1 pri h2 prc c
  | Dir (d, c) -> fprintf fmt "Dir @[(%a,@ %a)@]" prd d prc c
  | Intro (name, c) -> fprintf fmt "Intro @[(%a,@ %a)@]" pri name prc c
  | Weakening c -> fprintf fmt "Weakening@ %a" prc c
  | Rewrite (h, p, rev, lc) ->
      fprintf fmt "Rewrite @[(%a,@ %a,@ %b,@ %a)@]"
        pri h (prle "; " prd) p rev (prle "; " prc) lc
and prc fmt (r, g) =
  fprintf fmt "(%a, %a)" prr r pri g

let rec pcte fmt = function
  | CTapp i -> pri fmt i
  | CTbinop (op, t1, t2) ->
      fprintf fmt "(%a %a %a)" pcte t1 pro op pcte t2
and pro fmt = function
  | CTor -> fprintf fmt "\\/"
  | CTand -> fprintf fmt "/\\"
  | CTimplies -> fprintf fmt "->"
  | CTiff -> fprintf fmt "<->"

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
