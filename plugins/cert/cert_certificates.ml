open Why3
open Decl
open Term
open Ty
open Ident
open Format

open Cert_syntax
open Cert_abstract

(** We equip each transformation application with a certificate indicating
    why the resulting list of tasks is implying the initial task *)

(* We will denote a ctask <{sigma; gamma_delta}> by <Σ | Γ ⊢ Δ>
   We sometimes omit signature (when it's not confusing) and write <Γ ⊢ Δ> *)

type ('a, 'v, 'h, 't) scert =
  (* 'v is used to designate variables, 'h is used to designate an hypothesis,
     't is used for terms *)
  (* Replaying a certif cert against a ctask cta will be denoted <cert ⇓ cta>.
     For more details, take a look at the OCaml implementation
     <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole of 'a
  (* Hole ct ⇓ (Γ ⊢ Δ) stands iff ct refers to <Γ ⊢ Δ> *)
  | Assert of 'h * ('t Mid.t -> 't) * ('a, 'v, 'h, 't) scert * ('a, 'v, 'h, 't) scert
  (* Assert (i, t, c₁, c₂) ⇓ (Σ | Γ ⊢ Δ) ≜
         c₁ ⇓ (Σ | Γ ⊢ Δ, i : t)
     and c₂ ⇓ (Σ | Γ, i : t ⊢ Δ)
     and Σ ⊩ t : prop *)
  | Let of 't * 'h * ('a, 'v, 'h, 't) scert
  (* Let (x, i, c) ⇓ t ≜  c[x → i(t)] ⇓ t *)
  (* Meaning : in c, x is mapped to the formula identified by i in task t *)
  | Axiom of 'h * 'h
  (* Axiom (i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  (* Axiom (i1, i2) ⇓ (Γ, i2 : t ⊢ Δ, i1 : t) stands *)
  | Trivial of 'h
  (* Trivial i ⇓ (Γ, i : false ⊢ Δ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : true ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : t = t) stands *)
  | EqSym of 'h * ('a, 'v, 'h, 't) scert
  (* EqSym (i, c) ⇓ (Γ ⊢ Δ, i : t₁ = t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂ = t₁) *)
  (* EqSym (i, c) ⇓ (Γ, i : t₁ = t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ = t₁ ⊢ Δ) *)
  | EqTrans of 'h * 'h * 'h * ('a, 'v, 'h, 't) scert
  (* EqTrans (i₁, i₂, i₃, c) ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃, i₃ : t₁ = t₃ ⊢ Δ) *)
  | Unfold of 'h * ('a, 'v, 'h, 't) scert
  (* Unfold (i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  (* Unfold (i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | Fold of 'h * ('a, 'v, 'h, 't) scert
  (* Fold (i, c) ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) *)
  (* Fold (i, c) ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) *)
  (* Fold (i, c) ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) *)
  (* Fold (i, c) ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁ → t₂) *)
  | Split of 'h * ('a, 'v, 'h, 't) scert * ('a, 'v, 'h, 't) scert
  (* Split (i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
     c₁ ⇓ (Γ, i : t₁ ⊢ Δ)
     and c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* Split (i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t₁)
     and c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | Destruct of 'h * 'h * 'h * ('a, 'v, 'h, 't) scert
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | Construct of 'h * 'h * 'h * ('a, 'v, 'h, 't) scert
  (* Construct (i₁, i₂, i, c) ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) *)
  (* Construct (i₁, i₂, i, c) ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) *)
  | Swap of 'h * ('a, 'v, 'h, 't) scert
  (* Swap (i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : t) *)
  (* Swap (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜  c ⇓ (Γ, i : t ⊢ Δ) *)
  | Clear of 'h * ('a, 'v, 'h, 't) scert
  (* Clear (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Clear (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Forget of 'v * ('a, 'v, 'h, 't) scert
  (* Forget (i, c) ⇓ (Σ, i | Γ ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Duplicate of 'h * 'h * ('a, 'v, 'h, 't) scert
  (* Duplicate (i₁, i₂, c) ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₁ : t, i₂ : t) *)
  (* Duplicate (i₁, i₂, c) ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₁ : t, i₂ : t ⊢ Δ) *)
  | IntroQuant of 'h * 't * ('a, 'v, 'h, 't) scert
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ, y : τ | Γ, i : p[x ↦ y] ⊢ Δ)
     and y ∉  Σ *)
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. p) ≜
     c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : p[x ↦ y])
     and y ∉  Σ *)
  | InstQuant of 'h * 'h * 't * ('a, 'v, 'h, 't) scert
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ | Γ, i₁ : ∀ x : τ. p x, i₂ : p[x ↦ t] ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p) ≜
     c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p x, i₂ : p[x ↦ t])
     and Σ ⊩ t : τ *)
  | Rewrite of 'h * 'h * ('a, 'v, 'h, 't) scert
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, H : t₁ = t₂, i₁ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, H : t₁ = t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  | Induction of 'h * 'h * 'h * 'h * 't * ('t Mid.t -> 't)
                 * ('a, 'v, 'h, 't) scert * ('a, 'v, 'h, 't) scert
(* Induction (G, Hi₁, Hi₂, Hr, x, a, c₁, c₂) ⇓ (Γ ⊢ Δ, G : ctxt[x]) ≜
   c₁ ⇓ (Γ, Hi₁ : i ≤ a ⊢ Δ, G : ctxt[x])
   and c₂ ⇓ (Γ, Hi₂ : a < i, Hr: ∀ n : int. n < i → ctxt[n] ⊢ ctxt[x])
   and i does not appear in Γ, Δ or C
   and x and a are of type int
 *)
(* In the induction and rewrite rules ctxt is a context and the notation ctxt[t]
   stands for this context where the holes have been replaced with t *)

type 'a wscert = ('a, lsymbol, prsymbol, term) scert

type 'a sc = int * ('a wscert list -> 'a wscert)

let fail_arg () = verif_failed "Argument arity mismatch when composing certificates"

let lambda0 c = 0, fun _ -> c
let lambda1 f = 1, (fun l -> match l with [u] -> f u | _ -> fail_arg ())
let lambda2 f = 2, (fun l -> match l with [u1; u2] -> f u1 u2 | _ -> fail_arg ())
let lambdan n f = n, f

(* type ('a, 'b) args =
 *   | Z : ('a, 'a wscert) args
 *   | Succ : ('a, 'b) args -> ('a, 'a wscert -> 'b) args
 *   | List : int -> ('a, 'a wscert list -> 'a wscert) args
 * 
 * let one = Succ Z
 * let two = Succ one
 * 
 * let rec lambda : type a b. (a, b) args -> b -> a sc = fun args f ->
 *   match args with
 *   | Z -> 0, fun _ -> f
 *   | Succ args ->
 *       let i1 = create_prsymbol (id_fresh "i1") in
 *       let i2 = create_prsymbol (id_fresh "i2") in
 *       let dummy_cert = Axiom (i1, i2) in
 *       let n, _ = lambda args (f dummy_cert) in
 *       n, (fun l -> let i, l = List.hd l, List.tl l in
 *                    let _, c = lambda args (f i) in
 *                    c l)
 *   | List n -> n, f *)

let rec cut n = function
  | h::t when n > 0 ->
      let l1, l2 = cut (n-1) t in
      h::l1, l2
  | l -> [], l

let rec dispatch lu lc = match lc with
  | (n2, f2)::lc ->
      let lu2, lu = cut n2 lu in
      f2 lu2 :: dispatch lu lc
  | [] -> []

let ( *** ) (n1, f1) lc2 =
  assert (List.length lc2 = n1);
  let n = List.fold_left (fun acc (n, _) -> acc + n) 0 lc2 in
  n, fun lu -> f1 (dispatch lu lc2)

let ( ** ) (n1, f1) c2 : 'a sc =
  let lc2 = List.init n1 (fun _ -> c2) in
  (n1, f1) *** lc2

let idc : 'a sc = 1, (fun l -> List.hd l)
(* let id = lambda1 (fun a -> a) *)
let assertion h t = lambda2 (fun a1 a2 -> Assert (h, t, a1, a2))
let axiom i1 i2 = lambda0 (Axiom (i1, i2))
let trivial i = lambda0 (Trivial i)
let eqsym i = lambda1 (fun a -> EqSym (i, a))
let eqtrans i1 i2 i3 = lambda1 (fun a -> EqTrans (i1, i2, i3, a))
let unfold i = lambda1 (fun a -> Unfold (i, a))
let fold i = lambda1 (fun a -> Fold (i, a))
let split i = lambda2 (fun a1 a2 -> Split (i, a1, a2))
let destruct i i1 i2 = lambda1 (fun a -> Destruct (i, i1, i2, a))
let construct i1 i2 i = lambda1 (fun a -> Construct (i1, i2, i, a))
let swap i = lambda1 (fun a -> Swap (i, a))
let clear i = lambda1 (fun a -> Clear (i, a))
let forget i = lambda1 (fun a -> Forget (i, a))
let duplicate i1 i2 = lambda1 (fun a -> Duplicate (i1, i2, a))
let introquant i t = lambda1 (fun a -> IntroQuant (i, t, a))
let instquant i1 i2 t = lambda1 (fun a -> InstQuant (i1, i2, t, a))
let rewrite i1 i2 = lambda1 (fun a -> Rewrite (i1, i2, a))
let induction g hi1 hi2 hr x a =
  lambda2 (fun a1 a2 -> Induction (g, hi1, hi2, hr, x, a, a1, a2))

let llet pr (cont : ident -> 'a sc) : 'a sc =
  let ls = create_psymbol (id_fresh "Let_var") [] in
  let t = t_app ls [] None in
  lambda1 (fun u -> Let (t, pr, u)) ** cont ls.ls_name
  (* n, Let (t, pr, cont ls.ls_name) *)

let eqrefl i = trivial i
(* eqrefl i ⇓ (Γ ⊢ Δ, i : t = t) stands *)

let create_eqrefl i (t : term) c =
  assertion i (fun _ -> t_app_infer ps_equ [t; t]) *** [eqrefl i; c]
(* create_eqrefl i t c ⇓ (Γ ⊢ Δ) ≜  c ⇓ (Γ, i : t = t ⊢ Δ) *)

let rename i1 i2 =
  duplicate i1 i2 ** clear i1
(* rename i₁ i₂ c ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₂ : t) *)
(* rename i₁ i₂ c ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₂ : t ⊢ Δ) *)

let dir d i =
  let j = create_prsymbol (id_fresh "dir") in
  let left, right = if d then j, i else i, j in
  destruct i left right ** clear j
(* dir false i c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ ⊢ Δ) *)
(* dir true i c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ ⊢ Δ) *)
(* dir false i c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁) *)
(* dir true i c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂) *)

let iffsym_hyp i c =
  let i1 = pr_clone i in
  let i2 = pr_clone i in
  Unfold (i,
          Destruct (i, i1, i2,
                    Construct (i2, i1, i,
                               Fold (i, c))))
(* iffsym_hyp i c ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ ↔ t₁ ⊢ Δ) *)

let nc = [], Nc

type 'a ctrans = 'a sc ctransformation

type ('a, 'v, 'h, 't, 'ty) ecert =
  (* 'v is used to designate a variable, 'h is used to designate an hypothesis,
     't is used for terms and 'ty is used for types *)
  | EHole of 'a
  (* EHole ct ⇓ (Γ ⊢ Δ) stands iff ct refers to <Γ ⊢ Δ> *)
  | EAssert of 'h * 't * ('a, 'v, 'h, 't, 'ty) ecert * ('a, 'v, 'h, 't, 'ty) ecert
  (* EAssert (i, t, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t)
     and c₂ ⇓ (Γ, i : t ⊢ Δ) *)
  | EAxiom of 't * 'h * 'h
  (* EAxiom (t, i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  (* Notice that there is only one rule. *)
  | ETrivial of bool * 'h
  (* ETrivial (false, i) ⇓ (Γ, i : false ⊢ Δ) stands *)
  (* ETrivial (true, i) ⇓ (Γ ⊢ Δ, i : true ) stands *)
  (* Notice that trivial equalities use the following certificate. *)
  | EEqRefl of 'ty * 't * 'h
  (* EEqRefl (τ, t, i) ⇓ (Γ ⊢ Δ, i : t = t) stands if t is of type τ *)
  | EEqSym of bool * 'ty * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert (* not kernel *)
  (* not kernel *)
  (* EEqSym (true, τ, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ = t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : t₂ = t₁) *)
  (* EEqSym (false, τ, t₁, t₂, i, c) ⇓ (Γ, i : t₁ = t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : t₂ = t₁ ⊢ Δ) *)
  | EEqTrans of 'ty * 't * 't * 't * 'h * 'h * 'h * ('a, 'v, 'h, 't, 'ty) ecert
  (* not kernel *)
  (* EEqTrans (τ, t₁, t₂, t₃, i₁, i₂, i₃, c) ⇓
     (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃, i₃ : t₁ = t₃ ⊢ Δ) *)
  | EUnfoldIff of (bool * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert)
  (* EUnfoldIff (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* EUnfoldIff (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  | EUnfoldArr of (bool * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert)
  (* EUnfoldArr (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* EUnfoldArr (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | EFoldIff of (bool * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert) (* not kernel *)
  (* EFoldIff (false, t₁, t₂, i, c) ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) *)
  (* EFoldIff (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) *)
  | EFoldArr of (bool * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert) (* not kernel *)
  (* EFoldArr (false, t₁, t₂, i, c) ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ → t₂ ⊢ Δ)*)
  (* EFoldArr (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ → t₂)*)
  | ESplit of bool * 't * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert * ('a, 'v, 'h, 't, 'ty) ecert
  (* ESplit (false, t₁, t₂, i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
     c₁ ⇓ (Γ, i : t₁ ⊢ Δ)
     and c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* ESplit (true, t₁, t₂, i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
     c₁ ⇓ (Γ ⊢ Δ, i : t₁)
     and c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | EDestruct of bool * 't * 't * 'h * 'h * 'h * ('a, 'v, 'h, 't, 'ty) ecert
  (* EDestruct (false, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* EDestruct (true, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜
     c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | EConstruct of bool * 't * 't * 'h * 'h * 'h * ('a, 'v, 'h, 't, 'ty) ecert
  (* not kernel *)
  (* EConstruct (false, t₁, t₂, i₁, i₂, i, c) ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) ≜
     c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) *)
  (* EConstruct (true, t₁, t₂, i₁, i₂, i, c) ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) ≜
     c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) *)
  | ESwap of (bool * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert)
  (* ESwap (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* ESwap (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  | ESwapNeg of (bool * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert)
  (* ESwap_neg (false, t, i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : t)  *)
  (* ESwap_neg (true, t, i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜  c ⇓ (Γ, i : t ⊢ Δ)  *)
  | EClear of bool * 't * 'h * ('a, 'v, 'h, 't, 'ty) ecert
  (* EClear (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* EClear (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | EForget of 'h * ('a, 'v, 'h, 't, 'ty) ecert
  (* EForget (i, c) ⇓ (Σ, i : τ | Γ ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | EDuplicate of bool * 't * 'h * 'h * ('a, 'v, 'h, 't, 'ty) ecert (* not kernel *)
  (* EDuplicate (true, t, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i₁ : t) ≜
     c ⇓ (Γ ⊢ Δ, i₁ : t, i₂ : t) *)
  (* EDuplicate (false, t, i₁, i₂, c) ⇓ (Γ, i₁ : t ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t, i₂ : t ⊢ Δ) *)
  | EIntroQuant of bool * 'ty * 't * 'h * 't * ('a, 'v, 'h, 't, 'ty) ecert
  (* EIntroQuant (false, τ, p, i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ, y : τ | Γ, i : p[x ↦ y] ⊢ Δ)
     and y ∉  Σ *)
  (* EIntroQuant (true, τ, p, i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. p) ≜
     c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : p[x ↦ y])
     and y ∉  Σ *)
  | EInstQuant of bool * 'ty * 't * 'h * 'h * 't * ('a, 'v, 'h, 't, 'ty) ecert
  (* EInstQuant (false, τ, p, i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. p ⊢ Δ) ≜
     c ⇓ (Σ | Γ, i₁ : ∀ x : τ. p, i₂ : p[x ↦ t] ⊢ Δ)
     and Σ ⊩ t : τ *)
  (* EInstQuant (true, τ, p, i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p) ≜
     c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. p x, i₂ : p[x ↦ t])
     and Σ ⊩ t : τ *)
  | ERewrite of bool * 't option * 'ty * 't * 't * 't * 'h * 'h
                * ('a, 'v, 'h, 't, 'ty) ecert
  (* ERewrite (true, None, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* ERewrite (false, None, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ = t₂, i₂ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  (* ERewrite (true, _, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ ↔ t₂ ⊢ Δ, i₂ : ctxt[t₁]) ≜
     c ⇓ (Γ, i₁ : t₁ ↔ t₂ ⊢ Δ, i₂ : ctxt[t₂]) *)
  (* ERewrite (false, _, τ, t₁, t₂, ctxt, i₁, i₂, c) ⇓
     (Γ, i₁ : t₁ ↔ t₂, i₂ : ctxt[t₁] ⊢ Δ) ≜
     c ⇓ (Γ, i₁ : t₁ ↔ t₂, i₂ : ctxt[t₂] ⊢ Δ) *)
  (* Second argument is None when working with an equality, and Some ls when
     working with an equivalence. The lsymbol ls is used to bind the ctxt (which
     is not possible in Why3) *)
  | EInduction of 'h * 'h * 'h * 'h * 't * 't * 't
                  * ('a, 'v, 'h, 't, 'ty) ecert * ('a, 'v, 'h, 't, 'ty) ecert
(* EInduction (G, Hi₁, Hi₂, Hr, x, a, ctxt, c₁, c₂) ⇓ (Γ ⊢ Δ, G : ctxt[x]) ≜
   c₁ ⇓ (Γ, Hi₁ : i ≤ a ⊢ Δ, G : ctxt[x])
   and c₂ ⇓ (Γ, Hi₂ : a < i, Hr: ∀ n : int. n < i → ctxt[n] ⊢ ctxt[x])
   and i does not appear in Γ, Δ or C
   and x and a are of type int *)
(* In the induction and rewrite rules ctxt is a context and the notation ctxt[t]
   stands for this context where the holes have been replaced with t *)

type 'a kc = ('a, ident, ident, cterm, ctype) ecert

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prcertif cert;
  close_out oc

and prcvit : type a v i t. (formatter -> v -> unit) ->
                 (formatter -> i -> unit) ->
                 (formatter -> t -> unit) ->
                 formatter -> (a, v, i, t) scert -> unit
  = fun prv pri prt fmt c ->
  let prc = prcvit prv pri prt in
  match c with
  | Nc -> fprintf fmt "No_certif"
  | Hole _ -> fprintf fmt "Hole"
  | Assert (i, _, c1, c2) ->
      fprintf fmt "Assert (@[%a, <fun>,@ @[<4>%a@],@ @[<4>%a@])@]"
        pri i prc c1 prc c2
  | Let (x, i, c) -> fprintf fmt "Let (%a, %a,@ %a)" prt x pri i prc c
  | Axiom (i1, i2) -> fprintf fmt "Axiom (%a, %a)" pri i1 pri i2
  | Trivial i -> fprintf fmt "Trivial %a" pri i
  | EqSym (i, c) -> fprintf fmt "EqSym (%a,@ %a)" pri i prc c
  | EqTrans (i1, i2, i3, c) -> fprintf fmt "EqTrans (%a, %a, %a, @ %a)"
                                 pri i1 pri i2 pri i3 prc c
  | Unfold (i, c) -> fprintf fmt "Unfold (%a,@ %a)" pri i prc c
  | Fold (i, c) -> fprintf fmt "Fold (%a,@ %a)" pri i prc c
  | Split (i, c1, c2) -> fprintf fmt "Split (@[%a,@ @[<4>%a@],@ @[<4>%a@])@]"
                           pri i prc c1 prc c2
  | Destruct (i, j1, j2, c) ->
      fprintf fmt "Destruct (%a, %a, %a,@ %a)" pri i pri j1 pri j2 prc c
  | Construct (i1, i2, j, c) ->
      fprintf fmt "Construct (%a, %a, %a,@ %a)" pri i1 pri i2 pri j prc c
  | Swap (i, c) -> fprintf fmt "Swap (%a,@ %a)" pri i prc c
  | Clear (i, c) -> fprintf fmt "Clear@ (%a,@ %a)" pri i prc c
  | Forget (v, c) -> fprintf fmt "Forget@ (%a,@ %a)" prv v prc c
  | Duplicate (i1, i2, c) -> fprintf fmt "Duplicate@ (%a, %a, @ %a)"
                               pri i1 pri i2 prc c
  | IntroQuant (i, y, c) -> fprintf fmt "IntroQuant (%a, %a,@ %a)"
                              pri i prt y prc c
  | InstQuant (i, j, t, c) -> fprintf fmt "InstQuant (%a, %a, %a,@ %a)"
                                pri i pri j prt t prc c
  | Rewrite (i, h, c) -> fprintf fmt "Rewrite (%a, %a,@ %a)" pri i pri h prc c
  | Induction (i1, i2, i3, i4, x, _, c1, c2) ->
      fprintf fmt "Induction (%a, %a, %a, %a, %a, <fun>,@ %a,@ %a)"
        pri i1 pri i2 pri i3 pri i4 prt x prc c1 prc c2

and prlid = pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "; ") prid
and prcertif fmt (vs, c) = fprintf fmt "@[<v>[%a],@ @[%a@]@]"
                            prlid vs (prcvit prls prpr Pretty.print_term) c
(* and prcore_certif fmt (v, c) = fprintf fmt "@[<v>[%a],@ @[%a@]@]"
 *                                  prlid v (prcvit prid prhyp pcte) c *)

let eprcertif c = eprintf "%a@." prcertif c



(** Utility functions on certificates *)

(* Use propagate to define recursive functions on elements of type cert *)
let propagate_cert fc fv fi = function
  | (Hole _ | Nc) as c -> c
  | Axiom (h, g) -> Axiom (fi h, fi g)
  | Trivial i -> Trivial (fi i)
  | EqSym (i, c) -> EqSym (fi i, fc c)
  | EqTrans (i1, i2, i3, c) -> EqTrans (fi i1, fi i2, fi i3, fc c)
  | Assert (i, a, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      Assert (fi i, a, f1, f2)
  | Let (x, i, c) -> Let (x, fi i, fc c)
  | Unfold (i, c) -> Unfold (fi i, fc c)
  | Fold (i, c) -> Fold (fi i, fc c)
  | Split (i, c1, c2) ->
      let f1 = fc c1 in let f2 = fc c2 in
                        Split (fi i, f1, f2)
  | Destruct (i, j1, j2, c) -> Destruct (fi i, fi j1, fi j2, fc c)
  | Construct (i1, i2, j, c) -> Construct (fi i1, fi i2, fi j, fc c)
  | Swap (i, c) -> Swap (fi i, fc c)
  | Clear (i, c) -> Clear (fi i, fc c)
  | Forget (v, c) -> Forget (fv v, fc c)
  | Duplicate (i1, i2, c) -> Duplicate (fi i1, fi i2, fc c)
  | IntroQuant (i, y, c) -> IntroQuant (fi i, y, fc c)
  | InstQuant (i, j, t, c) -> InstQuant (fi i, fi j, t, fc c)
  | Rewrite (i, h, c) -> Rewrite (fi i, fi h, fc c)
  | Induction (i1, i2, i3, i4, n, t, c1, c2) ->
      Induction (fi i1, fi i2, fi i3, fi i4, n, t, fc c1, fc c2)

let rec elab_abstract c =
  propagate_cert elab_abstract
    (fun ls -> ls.ls_name) (fun pr -> pr.pr_name) c

(* Use propagate to define recursive functions on elements of type ecert *)
let propagate_ecert fc fi ft fty = function
  | EHole _ as c -> c
  | EAssert (i, a, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      EAssert (fi i, ft a, f1, f2)
  | EAxiom (a, i1, i2) -> EAxiom (ft a, fi i1, fi i2)
  | ETrivial (pos, i) -> ETrivial (pos, fi i)
  | EEqRefl (ty, t, i) -> EEqRefl (fty ty, ft t, fi i)
  | EEqSym (pos, ty, t1, t2, i, c) ->
      EEqSym (pos, fty ty, ft t1, ft t2, fi i, fc c)
  | EEqTrans (ty, t1, t2, t3, i1, i2, i3, c) ->
      EEqTrans (fty ty, ft t1, ft t2, ft t3, fi i1, fi i2, fi i3, fc c)
  | ESplit (pos, a, b, i, c1, c2) ->
      let f1 = fc c1 in
      let f2 = fc c2 in
      ESplit (pos, ft a, ft b, fi i, f1, f2)
  | EUnfoldIff (pos, a, b, i, c) -> EUnfoldIff (pos, ft a, ft b, fi i, fc c)
  | EUnfoldArr (pos, a, b, i, c) -> EUnfoldArr (pos, ft a, ft b, fi i, fc c)
  | EFoldIff (pos, a, b, i, c) -> EFoldIff (pos, ft a, ft b, fi i, fc c)
  | EFoldArr (pos, a, b, i, c) -> EFoldArr (pos, ft a, ft b, fi i, fc c)
  | EDestruct (pos, a, b, i, j1, j2, c) ->
      EDestruct (pos, ft a, ft b, fi i, fi j1, fi j2, fc c)
  | EConstruct (pos, a, b, i1, i2, j, c) ->
      EConstruct (pos, ft a, ft b, fi i1, fi i2, fi j, fc c)
  | ESwap (pos, a, i, c) -> ESwap (pos, ft a, fi i, fc c)
  | ESwapNeg (pos, a, i, c) -> ESwapNeg (pos, ft a, fi i, fc c)
  | EClear (pos, a, i, c) -> EClear (pos, ft a, fi i, fc c)
  | EForget (i, c) -> EForget (fi i, fc c)
  | EDuplicate (pos, a, i1, i2, c) -> EDuplicate (pos, ft a, fi i1, fi i2, fc c)
  | EIntroQuant (pos, ty, p, i, y, c) ->
      EIntroQuant (pos, fty ty, ft p, fi i, ft y, fc c)
  | EInstQuant (pos, ty, p, i, j, t, c) ->
      EInstQuant (pos, fty ty, ft p, fi i, fi j, ft t, fc c)
  | ERewrite (pos, topt, ty, a, b, ctxt, i, h, c) ->
      ERewrite (pos, Opt.map ft topt, fty ty, ft a, ft b, ft ctxt, fi i, fi h, fc c)
  | EInduction (i1, i2, i3, i4, n, t, ctxt, c1, c2) ->
      EInduction (fi i1, fi i2, fi i3, fi i4, ft n, ft t, ft ctxt, fc c1, fc c2)

let rec elab_lambda_prop = function
  | ERewrite (pos, Some {t_node = Tapp (ls, [])}, None, a, b, ctxt, i, h, c) ->
      let ntls = CTfvar (ls.ls_name, []) in
      let cctxt = abstract_term ctxt in
      let nctxt = CTquant (CTlambda, CTprop, ct_close ls.ls_name cctxt) in
      let na = abstract_term a in
      let nb = abstract_term b in
      let nc = elab_lambda_prop c in
      ERewrite (pos, Some ntls, CTprop, na, nb, nctxt, i, h, nc)
  | c -> propagate_ecert elab_lambda_prop
           (fun id -> id) abstract_term abstract_otype c

(** Compile chain.
    1. surface certificates (sc)
       The certificates given by certifying transformations.
       Many constructors and few parameters to ease making certifying
       a transformation.
    2. applied certificates (sc)
       Result of the function <elab_apply>. Holes replaced by their corresponding
       resulting task
    3. abstracted certificates (sc)
       Result of the function <elab_abstract>. Same as before but with simpler types
       that can be used by our checkers.
    3. elaborated certificates (kc)
       Result of the main elaboration function <elaborate> and as such contains
       many additional information such as the current formula and whether the focus
       is on a goal or on an hypothesis. Knowing those additional informations,
       Let-variables can be substituted
    4. trimmed certificates (kc)
       The result of applying the <elab_lambda_prop> and the <elab_trim> functions.
       The first function is specific to rewriting in formulas where we could
       not define an abstraction for a function from formulas to formulas. The
       second trims the certificate of rules that are derivable with other core
       rules (Duplicate, Construct).
       Few constructors and many parameters to ease formal verification of
       checkers.
 *)

exception Elaboration_failed

let elab_apply (n, f) res_ct =
  if List.length res_ct = n
  then f (List.map (fun u -> Hole u) res_ct)
  else verif_failed "Wrong number of holes in certificate"

let t_open_quant_one q tq = match t_open_quant tq with
  | vs::vsl, trg, t_open ->
      let nt = t_quant q (t_close_quant vsl trg t_open) in
      vs, nt
  | _ -> raise Elaboration_failed

let elaborate init_ct c =
  let rec elaborate (map : term Mid.t)
            (cta : (term, ctype) ctask)
            (c : ('a, ident, ident, term) scert)
    : ('a, ident, ident, term, ty option) ecert
    =
    (* the map argument registers Let-defined variables and is used
       to substitute user-provided terms that appear in certificates *)
    let elab = elaborate map in
    match c with
    | Nc -> eprintf "No certificates@.";
            raise Elaboration_failed
    | Hole task -> EHole task
    | Axiom (i1, i2) ->
        let t1, pos1 = try find_formula "Axiom1" i1 cta
                       with e -> pcta err_formatter cta; raise e
        in
        let t2, pos2 = try find_formula "Axiom2" i2 cta
                       with e -> pcta err_formatter cta; raise e
        in
        assert (pos1 <> pos2);
        assert (t_equal t1 t2);
        let i1, i2 = if pos2 then i1, i2 else i2, i1 in
        EAxiom (t1, i1, i2)
    | Trivial i ->
        let t, pos = find_formula "Trivial" i cta in
        begin match t.t_node, pos with
        | Tapp (e, [t1; t2]), _ when t_equal t1 t2 && ls_equal e ps_equ ->
            EEqRefl (t1.t_ty, t1, i)
        | Tfalse, false | Ttrue, true ->
            ETrivial (pos, i)
        | _ -> eprintf "not an equality or not same terms in eqrefl";
               raise Elaboration_failed end
    | EqSym (i, c) ->
        let t, pos = find_formula "EqSym" i cta in
        begin match t.t_node with
        | Tapp (e, [t1; t2]) when ls_equal e ps_equ ->
            let rev_eq = t_app ps_equ [t2; t1] t.t_ty in
            let cta = add i (rev_eq, pos) cta in
            EEqSym (pos, t1.t_ty, t1, t2, i, elab cta c)
        | _ -> eprintf "not an equality"; raise Elaboration_failed end
    | EqTrans (i1, i2, i3, c) ->
        let t1, pos1 = find_formula "EqTrans" i1 cta in
        let t2, pos2 = find_formula "EqTrans" i2 cta in
        begin match t1.t_node, t2.t_node, pos1, pos2 with
        | Tapp (e1, [t11; t12]),
          Tapp (e2, [t21; t22]), false, false
            when t_equal t12 t21 && ls_equal e1 ps_equ && ls_equal e2 ps_equ ->
            let new_eq = t_app ps_equ [t11; t22] t1.t_ty in
            let cta = add i3 (new_eq, false) cta in
            EEqTrans (t11.t_ty, t11, t12, t22, i1, i2, i3, elab cta c)
        | _ -> eprintf "wrong hyps form in eqtrans";
               raise Elaboration_failed end
    | Assert (i, a, c1, c2) ->
        let a = a map in
        let cta1 = add i (a, true) cta in
        let cta2 = add i (a, false) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        EAssert (i, a, c1, c2)
    | Let (x, i, c) ->
        let y, _ = find_formula "Let" i cta in
        let ix = match x.t_node with
          | Tapp (ls, []) -> ls.ls_name
          | _ -> assert false in
        let map = Mid.add ix y map in
        elaborate map cta c
    | Unfold (i, c) ->
        let t, pos = find_formula "Unfold" i cta in
        begin match t.t_node with
        | Tbinop (Tiff, t1, t2) ->
            let unfolded_iff = t_binary Tand
                                 (t_binary Timplies t1 t2)
                                 (t_binary Timplies t2 t1), pos in
            let cta = add i unfolded_iff cta in
            EUnfoldIff (pos, t1, t2, i, elab cta c)
        | Tbinop (Timplies, t1, t2) ->
            let unfolded_imp = t_binary Tor (t_not t1) t2, pos in
            let cta = add i unfolded_imp cta in
            EUnfoldArr (pos, t1, t2, i, elab cta c)
        | _ -> eprintf "Nothing to unfold";
               raise Elaboration_failed end
    | Fold (i, c) ->
        let t, pos = find_formula "Fold" i cta in
        begin match t.t_node with
        | Tbinop (Tand, {t_node = Tbinop (Timplies, t1, t2)},
                  {t_node = Tbinop (Timplies, t2', t1')})
            when t_equal t1 t1' && t_equal t2 t2' ->
            let folded_iff = t_binary Tiff t1 t2, pos in
            let cta = add i folded_iff cta in
            EFoldIff (pos, t1, t2, i, elab cta c)
        | Tbinop (Tor, {t_node = Tnot t1}, t2) ->
            let cta = add i (t_binary Timplies t1 t2, pos) cta in
            EFoldArr (pos, t1, t2, i, elab cta c)
        | _ -> eprintf "Nothing to fold";
               raise Elaboration_failed end
    | Split (i, c1, c2) ->
        let t, pos = find_formula "Split" i cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), true
          | Tbinop (Tor, t1, t2), false -> t1, t2
          | _ -> eprintf "Not splittable@.";
                 raise Elaboration_failed in
        let cta1 = add i (t1, pos) cta in
        let cta2 = add i (t2, pos) cta in
        let c1 = elab cta1 c1 in
        let c2 = elab cta2 c2 in
        ESplit (pos, t1, t2, i, c1, c2)
    | Destruct (i, i1, i2, c) ->
        let t, pos = find_formula "Destruct" i cta in
        let t1, t2 = match t.t_node, pos with
          | Tbinop (Tand, t1, t2), false
          | Tbinop (Tor, t1, t2), true -> t1, t2
          | _ -> eprintf "Nothing to destruct@.";
                 raise Elaboration_failed in
        let cta = remove i cta
                  |> add i1 (t1, pos)
                  |> add i2 (t2, pos) in
        EDestruct (pos, t1, t2, i, i1, i2, elab cta c)
    | Construct (i1, i2, i, c) ->
        let t1, pos1 = find_formula "Construct1" i1 cta in
        let t2, pos2 = find_formula "Construct2" i2 cta in
        assert (pos1 = pos2);
        let t = if pos1
                then t_binary Tor t1 t2
                else t_binary Tand t1 t2 in
        let cta = remove i1 cta
                  |> remove i2
                  |> add i (t, pos1) in
        EConstruct (pos1, t1, t2, i1, i2, i, elab cta c)
    | Swap (i, c) ->
        let t, pos = find_formula "Swap" i cta in
        let neg, underlying_t, neg_t = match t.t_node with
          | Tnot t -> true, t, t
          | _ -> false, t, t_not t in
        let cta = add i (neg_t, not pos) cta in
        let pack = pos, underlying_t, i, elab cta c in
        if neg
        then ESwapNeg pack
        else ESwap pack
    | Clear (i, c) ->
        let t, pos = find_formula "Clear" i cta in
        let cta = remove i cta in
        EClear (pos, t, i, elab cta c)
    | Forget (i, c) ->
        let cta = remove_var i cta in
        EForget (i, elab cta c)
    | Duplicate (i1, i2, c) ->
        let t, pos = find_formula "Duplicate" i1 cta in
        let cta = add i2 (t, pos) cta in
        EDuplicate (pos, t, i1, i2, elab cta c)
    | IntroQuant (i, y, c) ->
        let t, pos = find_formula "IntroQuant" i cta in
        begin match t.t_node, y.t_node with
          | Tquant (q, tq), Tapp (ls, []) ->
              let ty_opt = ls.ls_value in
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs y t_open in
              let t_fun = t_eps (t_close_bound vs t_open) in
              let cta = add i (t_applied, pos) cta
                        |> add_var ls.ls_name (abstract_otype ty_opt) in
              EIntroQuant (pos, ty_opt, t_fun, i, y, elab cta c)
          | _ -> raise Elaboration_failed end
    | InstQuant (i1, i2, t_inst, c) ->
        let t, pos = find_formula "InstQuant" i1 cta in
        begin match t.t_node with
          | Tquant (q, tq) ->
              let vs, t_open = t_open_quant_one q tq in
              let t_applied = t_subst_single vs t_inst t_open in
              let t = t_eps (t_close_bound vs t_open) in
              let cta = add i2 (t_applied, pos) cta in
              EInstQuant (pos, Some vs.vs_ty, t, i1, i2, t_inst, elab cta c)
          | _ -> eprintf "trying to instantiate a non-quantified hypothesis@.";
                 raise Elaboration_failed end
    | Rewrite (i1, i2, c) ->
        let rew_hyp, _ = find_formula "Finding rewrite hypothesis" i1 cta in
        let a, b, is_eq = match rew_hyp.t_node with
          | Tbinop (Tiff, a, b) -> a, b, false
          | Tapp (f, [a; b]) when ls_equal f ps_equ && a.t_ty <> None ->
              a, b, true
          | _ -> eprintf "Bad rewrite hypothesis@.";
                 raise Elaboration_failed in
        let t, pos = find_formula "Finding to be rewritten goal" i2 cta in
        let cta = add i2 (t_replace a b t, pos) cta in
        let c = elab cta c in
        let id = id_fresh "ctxt_var" in
        if is_eq
        then
          let ty = Opt.get a.t_ty in
          let vs = create_vsymbol id ty in
          let vst = t_var vs in
          let ctxt = t_eps (t_close_bound vs (t_replace a vst t)) in
          ERewrite (pos, None, Some ty, a, b, ctxt, i1, i2, c)
        else
          let t_r = t_app (create_psymbol id []) [] None in
          let ctxt = t_replace a t_r t in
          ERewrite (pos, Some t_r, None, a, b, ctxt, i1, i2, c)

    | Induction (g, hi1, hi2, hr, x, a, c1, c2) ->
        let a = a map in
        let le = cta.get_ls le_str in
        let lt = cta.get_ls lt_str in
        let t, _ = find_formula "induction" g cta in
        let vsx = create_vsymbol (id_fresh "ctxt_var_induction") ty_int in
        let ctxt = t_eps (t_close_bound vsx (t_replace x (t_var vsx) t)) in
        let cta1 = add hi1 (t_app le [x; a] None, false) cta in
        let vsn = create_vsymbol (id_fresh "ctxt_var") ty_int in
        let n = t_var vsn in
        let cta2 = add hi2 (t_app lt [a; x] None, false) cta
                   |> add hr (t_quant Tforall
                                (t_close_quant [vsn] []
                                   (t_binary Timplies
                                      (t_app lt [n; a] None)
                                      (t_replace x n t))),
                              false) in
        EInduction (g, hi1, hi2, hr, x, a, ctxt, elab cta1 c1, elab cta2 c2)
  in
  elaborate Mid.empty init_ct c

let eaxiom pos t i1 i2 =
  if pos then EAxiom (t, i1, i2)
  else EAxiom (t, i2, i1)
(* eaxiom true t i1 i2 ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
(* eaxiom false t i1 i2 ⇓ (Γ, i2 : t ⊢ Δ, i1 : t) stands *)

let eduplicate pos t i1 i2 c =
  let c_closed = eaxiom (not pos) t i1 i2 in
  let c1, c2 = if pos
               then c, c_closed
               else c_closed, c in
  EAssert (i2, t, c1, c2)

let erename pos a i1 i2 c =
  eduplicate pos a i1 i2 (EClear (pos, a, i1, c))

let rec elab_trim c =
  match c with
  | EDuplicate (pos, t, i1, i2, c) ->
      let c = elab_trim c in
      eduplicate pos t i1 i2 c
  | EConstruct (pos, t1, t2, i1, i2, i, c) ->
      let c = elab_trim c in
      let i1' = id_register (id_fresh "i1") in
      let i2' = id_register (id_fresh "i2") in
      let c_open = EClear (pos, t1, i1', EClear (pos, t2, i2', c)) in
      let c_closed = ESplit (not pos, t1, t2, i,
                             eaxiom (not pos) t1 i1' i,
                             eaxiom (not pos) t2 i2' i) in
      let c1, c2, cut = if pos
                        then c_open, c_closed, CTbinop (Tor, t1, t2)
                        else c_closed, c_open, CTbinop (Tand, t1, t2) in
      erename pos t1 i1 i1' @@
        erename pos t2 i2 i2' @@
          EAssert (i, cut, c1, c2)
  | EFoldArr (pos, t1, t2, i, c') | EFoldIff (pos, t1, t2, i, c') ->
      let is_arr = match c with EFoldArr _ -> true | _ -> false in
      let c = elab_trim c' in
      let j = id_register (id_fresh "fold_temp") in
      let pre, post = if is_arr
                      then CTbinop (Tor, CTnot t1, t2),
                           CTbinop (Timplies, t1, t2)
                      else CTbinop (Tand, CTbinop (Timplies, t1, t2),
                                    CTbinop (Timplies, t2, t1)),
                           CTbinop (Tiff, t1, t2) in
      let unfold pack = if is_arr then EUnfoldArr pack else EUnfoldIff pack in
      let c_open = EClear (pos, pre, j, c) in
      let c_closed = unfold (not pos, t1, t2, i, eaxiom pos pre i j) in
      let c1, c2 = if pos then c_open, c_closed else c_closed, c_open in
      erename pos pre i j @@
        EAssert (i, post, c1, c2)
  | EEqSym (pos, cty, t1, t2, i, c) ->
      let c = elab_trim c in
      let j = id_register (id_fresh "eqsym_temp") in
      let pre = CTapp (CTapp (eq cty, t1), t2) in
      let post = CTapp (CTapp (eq cty, t2), t1) in
      let c_open = EClear (pos, pre, j, c) in
      let h, g, a, b = if pos then i, j, t2, t1 else j, i, t1, t2 in
      (* We want to close a task of the form <Γ, h : a = b ⊢ Δ, g : b = a> *)
      let ctxt = CTquant (CTlambda, cty, CTapp (CTapp (eq cty, b), CTbvar 0)) in
      let c_closed = ERewrite (not pos, None, cty, a, b, ctxt, h, g,
                               EEqRefl (cty, b, g)) in
      let c1, c2 = if pos then c_open, c_closed else c_closed, c_open in
      erename pos pre i j @@
        EAssert (i, post, c1, c2)
  | EEqTrans (cty, t1, t2, t3, i1, i2, i3, c) ->
      let c = elab_trim c in
      let ctxt = CTquant (CTlambda, cty, CTapp (CTapp (eq cty, t1), CTbvar 0)) in
      eduplicate false (CTapp (CTapp (eq cty, t1), t2)) i1 i3 @@
        ERewrite (false, None, cty, t2, t3, ctxt, i2, i3, c)
  | _ -> propagate_ecert elab_trim (fun t -> t) (fun i -> i) (fun ty -> ty) c

let make_kernel_cert init_ct res_ct (c : 'a sc) : 'a kc =
  elab_apply c res_ct
  |> elab_abstract
  |> elaborate init_ct
  |> elab_lambda_prop
  |> elab_trim

