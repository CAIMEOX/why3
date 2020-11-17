open Why3
open Decl
open Term
open Ident
open Format

open Cert_abstract

(** We equip each transformation application with a certificate indicating
    why the resulting list of tasks is implying the initial task *)

type ('i, 't) cert =
  (* 'i is used to designate an hypothesis, 't is used for terms *)
  (* Replaying a certif <cert> against a ctask <cta> will be denoted <cert ⇓ cta>.
     For more details, take a look at the OCaml implementation <Cert_verif_caml.ccheck>. *)
  | Nc
  (* Makes verification fail : use it as a placeholder *)
  | Hole of ident
  (* Hole ct ⇓ (Γ ⊢ Δ) stands iff <ct> refers to <Γ ⊢ Δ> *)
  | Cut of 'i * 't * ('i, 't) cert * ('i, 't) cert
  (* Cut (i, t, c₁, c₂) ⇓ (Σ | Γ ⊢ Δ) ≜
                     c₁ ⇓ (Σ | Γ ⊢ Δ, i : t)
                 and c₂ ⇓ (Σ | Γ, i : t ⊢ Δ)
                 and Σ ⊩ t : prop *)
  | Let of 't * 'i * ('i, 't) cert
  (* Let (x, i, c) ⇓ t ≜  c ⇓ t[x ← i(t)] *)
  (* Meaning : <x> can be used in <c> as the formula identified by <i> in task <t> *)
  | Axiom of 'i * 'i
  (* Axiom (i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  (* Axiom (i1, i2) ⇓ (Γ, i2 : t ⊢ Δ, i1 : t) stands *)
  | Trivial of 'i
  (* Trivial i ⇓ (Γ, i : false ⊢ Δ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : true ) stands *)
  (* Trivial i ⇓ (Γ ⊢ Δ, i : t = t) stands *)
  | EqSym of 'i * ('i, 't) cert
  (* EqSym (i, c) ⇓ (Γ ⊢ Δ, i : t₁ = t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂ = t₁) *)
  (* EqSym (i, c) ⇓ (Γ, i : t₁ = t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ = t₁ ⊢ Δ) *)
  | EqTrans of 'i * 'i * 'i * ('i, 't) cert
  (* EqTrans (i₁, i₂, i₃, c) ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃ ⊢ Δ) ≜
                           c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃, i₃ : t₁ = t₃ ⊢ Δ) *)
  | Unfold of 'i * ('i, 't) cert
  (* Unfold (i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  (* Unfold (i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* Unfold (i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | Fold of 'i * ('i, 't) cert
  (* Fold (i, c) ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) *)
  (* Fold (i, c) ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁ → t₂) *)
  | Split of 'i * ('i, 't) cert * ('i, 't) cert
  (* Split (i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
                       c₁ ⇓ (Γ, i : t₁ ⊢ Δ)
                   and c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* Split (i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
                    c₁ ⇓ (Γ ⊢ Δ, i : t₁)
                and c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | Destruct of 'i * 'i * 'i * ('i, 't) cert
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* Destruct (i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜  c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | Construct of 'i * 'i * 'i * ('i, 't) cert
  (* Construct (i₁, i₂, i, c) ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) *)
  (* Construct (i₁, i₂, i, c) ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) *)
  | Swap of 'i * ('i, 't) cert
  (* Swap (i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : t) *)
  (* Swap (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  (* Swap (i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜  c ⇓ (Γ, i : t ⊢ Δ) *)
  | Weakening of 'i * ('i, 't) cert
  (* Weakening (i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* Weakening (i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | Duplicate of 'i * 'i * ('i, 't) cert
  (* Duplicate (i₁, i₂, c) ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₁ : t, i₂ : t) *)
  (* Duplicate (i₁, i₂, c) ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₁ : t, i₂ : t ⊢ Δ) *)
  | IntroQuant of 'i * ident * ('i, 't) cert
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. p x ⊢ Δ) ≜
                        c ⇓ (Σ, y : τ | Γ, i : p y ⊢ Δ)
                    and y ∉  Σ *)
  (* IntroQuant (i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. p x) ≜
                        c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : p y)
                    and y ∉  Σ *)
  | InstQuant of 'i * 'i * 't * ('i, 't) cert
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. P x ⊢ Δ) ≜
                            c ⇓ (Σ | Γ, i₁ : ∀ x : τ. P x, i₂ : P t ⊢ Δ)
                      and Σ ⊩ t : τ *)
  (* InstQuant (i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. P x) ≜
                            c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. P x, i₂ : P t)
                        and Σ ⊩ t : τ *)
  | Rewrite of 'i * 'i * ('i, 't) cert
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, i₁ : a = b ⊢ Δ, i₂ : ctxt[a]) ≜
                       c ⇓ (Γ, i₁ : a = b ⊢ Δ, i₂ : ctxt[b]) *)
  (* Rewrite (i₁, i₂, c) ⇓ (Γ, H : a = b, i₁ : ctxt[a] ⊢ Δ) ≜
                       c ⇓ (Γ, H : a = b, i₂ : ctxt[b] ⊢ Δ) *)
  (* In the previous rules <ctxt> stands for the context obtained by taking
     the formula contained in <i₁> and replacing each occurrence of <a> by a
     hole. *)

let eqrefl i = Trivial i
(* eqrefl i ⇓ (Γ ⊢ Δ, i : t = t) stands *)

let create_eqrefl i t c =
  Cut (i, CTapp (CTapp (eq, t), t), eqrefl i, c)
(* create_eqrefl i t c ⇓ (Γ ⊢ Δ) ≜  c ⇓ (Γ, i : t = t ⊢ Δ) *)

(* TODO : fix this when the equivalence is in delta *)
let iffsym pr c =
  let pr1 = pr_clone pr in
  let pr2 = pr_clone pr in
  Unfold (pr,
  Destruct (pr, pr1, pr2,
  Construct (pr2, pr1, pr,
  Fold (pr, c))))

let rename i1 i2 c =
  Duplicate (i1, i2, Weakening (i1, c))
(* rename i₁ i₂ c ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₂ : t) *)
(* rename i₁ i₂ c ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₂ : t ⊢ Δ) *)

let dir d pr c =
  let prh = create_prsymbol (id_fresh "Weaken") in
  let left, right = if d then prh, pr else pr, prh in
  Destruct (pr, left, right, Weakening (prh, c))
(* dir false i c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ ⊢ Δ) *)
(* dir true i c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ ⊢ Δ) *)
(* dir false i c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁) *)
(* dir true i c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂) *)

type vcert = (prsymbol, term) cert

type visible_cert = ident list * (prsymbol, term) cert

let nc = [], Nc

type 'a args =
  | Z : vcert args
  | One : (ident -> vcert) args
  | Two : (ident -> ident -> vcert) args
  | List : int -> (ident list -> vcert) args

let rec new_idents n =
  if n = 0 then [] else
    let i = id_register (id_fresh "s") in
    i:: new_idents (n-1)

let lambda : type a. a args -> a -> visible_cert  = fun args f ->
  match args with
  | Z -> [], f
  | One -> let i = id_register (id_fresh "s") in
           [i], f i
  | Two -> let i1 = id_register (id_fresh "s") in
           let i2 = id_register (id_fresh "s") in
           [i1; i2], f i1 i2
  | List n ->
      let il = new_idents n in
      il, f il

let hole () : visible_cert =
  lambda One (fun i -> Hole i)

type abstract_cert = ident list * (ident, cterm) cert

type ctrans = visible_cert ctransformation

type ('i, 't) ecert =
  (* 'i is used to designate an hypothesis, 't is used for terms *)
  | EHole of ident
  (* EHole ct ⇓ (Γ ⊢ Δ) stands iff <ct> refers to <Γ ⊢ Δ> *)
  | ECut of 'i * 't * ('i, 't) ecert * ('i, 't) ecert
  (* ECut (i, t, c₁, c₂) ⇓ (Γ ⊢ Δ) ≜
                      c₁ ⇓ (Γ ⊢ Δ, i : t)
                  and c₂ ⇓ (Γ, i : t ⊢ Δ) *)
  | ELet of 't * 't * ('i, 't) ecert
  (* ELet (x, y, c) ⇓ t ≜  c ⇓ t[x ←  y] *)
  | EAxiom of 't * 'i * 'i
  (* EAxiom (t, i1, i2) ⇓ (Γ, i1 : t ⊢ Δ, i2 : t) stands *)
  (* Notice that there is only one rule. *)
  | ETrivial of bool * 'i
  (* ETrivial (false, i) ⇓ (Γ, i : false ⊢ Δ) stands *)
  (* ETrivial (true, i) ⇓ (Γ ⊢ Δ, i : true ) stands *)
  (* Notice that trivial equalities use the following certificate. *)
  | EEqRefl of ctype * 't * 'i
  (* EEqRefl (τ, t, i) ⇓ (Γ ⊢ Δ, i : t = t) stands *)
  | EEqSym of bool * ctype * 't * 't * 'i * ('i, 't) ecert
  (* EEqSym (true, τ, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ = t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₂ = t₁) *)
  (* EEqSym (false, τ, t₁, t₂, i, c) ⇓ (Γ, i : t₁ = t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₂ = t₁ ⊢ Δ) *)
  | EEqTrans of ctype * 't * 't * 't * 'i * 'i * 'i * ('i, 't) ecert
  (* EEqTrans (τ, t₁, t₂, t₃, i₁, i₂, i₃, c) ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃ ⊢ Δ) ≜
                                           c ⇓ (Γ, i₁ : t₁ = t₂, i₂ : t₂ = t₃, i₃ : t₁ = t₃ ⊢ Δ) *)
  | EUnfoldIff of (bool * 't * 't * 'i * ('i, 't) ecert)
  (* EUnfoldIff (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ ↔ t₂ ⊢ Δ) ≜
                                    c ⇓ (Γ, i : (t₁ → t₂) ∧ (t₂ → t₁) ⊢ Δ) *)
  (* EUnfoldIff (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ ↔ t₂) ≜
                                   c ⇓ (Γ ⊢ Δ, i : (t₁ → t₂) ∧ (t₂ → t₁)) *)
  | EUnfoldArr of (bool * 't * 't * 'i * ('i, 't) ecert)
  (* EUnfoldArr (false, t₁, t₂, i, c) ⇓ (Γ, i : t₁ → t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ)*)
  (* EUnfoldArr (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : t₁ → t₂) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂)*)
  | EFoldArr of (bool * 't * 't * 'i * ('i, 't) ecert)
  (* EFoldArr (false, t₁, t₂, i, c) ⇓ (Γ, i : ¬t₁ ∨ t₂ ⊢ Δ) ≜  c ⇓ (Γ, i : t₁ → t₂ ⊢ Δ)*)
  (* EFoldArr (true, t₁, t₂, i, c) ⇓ (Γ ⊢ Δ, i : ¬t₁ ∨ t₂) ≜  c ⇓ (Γ ⊢ Δ, i : t₁ → t₂)*)
  | ESplit of bool * 't * 't * 'i * ('i, 't) ecert * ('i, 't) ecert
  (* ESplit (false, t₁, t₂, i, c₁, c₂) ⇓ (Γ, i : t₁ ∨ t₂ ⊢ Δ) ≜
                                    c₁ ⇓ (Γ, i : t₁ ⊢ Δ)
                                and c₂ ⇓ (Γ, i : t₂ ⊢ Δ) *)
  (* ESplit (true, t₁, t₂, i, c₁, c₂) ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) ≜
                                   c₁ ⇓ (Γ ⊢ Δ, i : t₁)
                               and c₂ ⇓ (Γ ⊢ Δ, i : t₂) *)
  | EDestruct of bool * 't * 't * 'i * 'i * 'i * ('i, 't) ecert
  (* EDestruct (false, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) ≜
                                           c ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) *)
  (* EDestruct (true, t₁, t₂, i, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i : t₁ ∨ t₂) ≜
                                          c ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) *)
  | EConstruct of bool * 't * 't * 'i * 'i * 'i * ('i, 't) ecert
  (* EConstruct (false, t₁, t₂, i₁, i₂, i, c) ⇓ (Γ, i₁ : t₁, i₂ : t₂ ⊢ Δ) ≜
                                            c ⇓ (Γ, i : t₁ ∧ t₂ ⊢ Δ) *)
  (* EConstruct (true, t₁, t₂, i₁, i₂, i, c) ⇓ (Γ ⊢ Δ, i₁ : t₁, i₂ : t₂) ≜
                                           c ⇓ (Γ ⊢ Δ, i : t₁ ∧ t₂) *)
  | ESwap of (bool * 't * 'i * ('i, 't) ecert)
  (* ESwap (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : ¬t) *)
  (* ESwap (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ, i : ¬t ⊢ Δ) *)
  | ESwapNeg of (bool * 't * 'i * ('i, 't) ecert)
  (* ESwap_neg (false, t, i, c) ⇓ (Γ, i : ¬t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ, i : t)  *)
  (* ESwap_neg (true, t, i, c) ⇓ (Γ ⊢ Δ, i : ¬t) ≜  c ⇓ (Γ, i : t ⊢ Δ)  *)
  | EWeakening of bool * 't * 'i * ('i, 't) ecert
  (* EWeakening (true, t, i, c) ⇓ (Γ ⊢ Δ, i : t) ≜  c ⇓ (Γ ⊢ Δ) *)
  (* EWeakening (false, t, i, c) ⇓ (Γ, i : t ⊢ Δ) ≜  c ⇓ (Γ ⊢ Δ) *)
  | EDuplicate of bool * 't * 'i * 'i * ('i, 't) ecert
  (* EDuplicate (true, t, i₁, i₂, c) ⇓ (Γ ⊢ Δ, i₁ : t) ≜  c ⇓ (Γ ⊢ Δ, i₁ : t, i₂ : t) *)
  (* EDuplicate (false, t, i₁, i₂, c) ⇓ (Γ, i₁ : t ⊢ Δ) ≜  c ⇓ (Γ, i₁ : t, i₂ : t ⊢ Δ) *)
  | EIntroQuant of bool * 't * 'i * ident * ('i, 't) ecert
  (* EIntroQuant (false, P, i, y, c) ⇓ (Σ | Γ, i : ∃ x : τ. P x ⊢ Δ) ≜
                                   c ⇓ (Σ, y : τ | Γ, i : P y ⊢ Δ)
                               and y ∉  Σ *)
  (* EIntroQuant (true, P, i, y, c) ⇓ (Σ | Γ ⊢ Δ, i : ∀ x : τ. P x) ≜
                                  c ⇓ (Σ, y : τ | Γ ⊢ Δ, i : P y)
                              and y ∉  Σ *)
  | EInstQuant of bool * 't * 'i * 'i * 't * ('i, 't) ecert
  (* EInstQuant (false, P, i₁, i₂, t, c) ⇓ (Σ | Γ, i₁ : ∀ x : τ. P x ⊢ Δ) ≜
                                       c ⇓ (Σ | Γ, i₁ : ∀ x : τ. P x, i₂ : P t ⊢ Δ)
                                   and Σ ⊩ t : τ *)
  (* EInstQuant (true, P, i₁, i₂, t, c) ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. P x) ≜
                                      c ⇓ (Σ | Γ ⊢ Δ, i₁ : ∃ x : τ. P x, i₂ : P t)
                                  and Σ ⊩ t : τ *)
  | ERewrite of bool * ctype * 't * 't * 't * 'i * 'i * ('i, 't) ecert
  (* ERewrite (true, τ, a, b, ctxt, i₁, i₂, c) ⇓ (Γ, i₁ : a = b ⊢ Δ, i₂ : ctxt[a]) ≜
                                             c ⇓ (Γ, i₁ : a = b ⊢ Δ, i₂ : ctxt[b]) *)
  (* ERewrite (false, τ, a, b, ctxt, i₁, i₂, c) ⇓ (Γ, i₁ : a = b, i₂ : ctxt[a] ⊢ Δ) ≜
                                              c ⇓ (Γ, i₁ : a = b, i₂ : ctxt[b] ⊢ Δ) *)

type heavy_ecert = ident list * (ident, cterm) ecert
type trimmed_ecert = ident list * (ident, cterm) ecert (* without (Construct, Duplicate) *)
type kernel_ecert = ident list * (ident, cterm) ecert (* without (Construct, Duplicate,Let) *)

let rec print_certif filename cert =
  let oc = open_out filename in
  let fmt = formatter_of_out_channel oc in
  fprintf fmt "%a@." prcertif cert;
  close_out oc
and prcit : type i t. (formatter -> i -> unit) ->
                 (formatter -> t -> unit) ->
                 formatter -> (i, t) cert -> unit
  = fun pri prt fmt c ->
  let prc = prcit pri prt in
  match c with
  | Nc -> fprintf fmt "No_certif"
  | Hole ct -> fprintf fmt "Hole %a" prid ct
  | Cut (i, a, c1, c2) -> fprintf fmt "Cut (@[%a, %a,@ @[<4>%a@],@ @[<4>%a@])@]"
                            pri i prt a prc c1 prc c2
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
  | Weakening (i, c) -> fprintf fmt "Weakening@ (%a,@ %a)" pri i prc c
  | Duplicate (i1, i2, c) -> fprintf fmt "Duplicate@ (%a, %a, @ %a)" pri i1 pri i2 prc c
  | IntroQuant (i, y, c) -> fprintf fmt "IntroQuant (%a, %a,@ %a)" pri i prid y prc c
  | InstQuant (i, j, t, c) -> fprintf fmt "InstQuant (%a, %a, %a,@ %a)" pri i pri j prt t prc c
  | Rewrite (i, h, c) -> fprintf fmt "Rewrite (%a, %a,@ %a)" pri i pri h prc c

and prlid = pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "; ") prid
and prcertif fmt (v, c) = fprintf fmt "@[<v>[%a],@ @[%a@]@]"
                            prlid v (prcit prpr Pretty.print_term) c
and prcore_certif fmt (v, c) = fprintf fmt "@[<v>[%a],@ @[%a@]@]"
                                 prlid v (prcit prhyp pcte) c

let eprcertif c = eprintf "%a@." prcertif c



(** Utility functions on certificates *)

(* Use propagate to define recursive functions on elements of type cert *)
let propagate_cert f fid fte = function
  | (Hole _ | Nc)  as c -> c
  | Axiom (h, g) -> Axiom (fid h, fid g)
  | Trivial i -> Trivial (fid i)
  | EqSym (i, c) -> EqSym (fid i, f c)
  | EqTrans (i1, i2, i3, c) -> EqTrans (fid i1, fid i2, fid i3, f c)
  | Cut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Cut (fid i, fte a, f1, f2)
  | Let (x, i, c) -> Let (fte x, fid i, f c)
  | Unfold (i, c) -> Unfold (fid i, f c)
  | Fold (i, c) -> Fold (fid i, f c)
  | Split (i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      Split (fid i, f1, f2)
  | Destruct (i, j1, j2, c) -> Destruct (fid i, fid j1, fid j2, f c)
  | Construct (i1, i2, j, c) -> Construct (fid i1, fid i2, fid j, f c)
  | Swap (i, c) -> Swap (fid i, f c)
  | Weakening (i, c) -> Weakening (fid i, f c)
  | Duplicate (i1, i2, c) -> Duplicate (fid i1, fid i2, f c)
  | IntroQuant (i, y, c) -> IntroQuant (fid i, y, f c)
  | InstQuant (i, j, t, c) -> InstQuant (fid i, fid j, fte t, f c)
  | Rewrite (i, h, c) -> Rewrite (fid i, fid h, f c)

let rec fill map = function
  | Hole x -> Mid.find x map
  | c -> propagate_cert (fill map) (fun t -> t) (fun t -> t) c

let thunk (ids, c) () =
  let nids = new_idents (List.length ids) in
  let hole_nids = List.map (fun i -> Hole i) nids in
  let map = Mid.of_list (List.combine ids hole_nids) in
  nids, fill map c

let flatten_uniq l =
  let add (s, l) v = if Sid.mem v s
                     then s, l
                     else Sid.add v s, v::l in
  let add_list acc nl = List.fold_left add acc nl in
  let add_list_list acc nll = List.fold_left add_list acc nll in
  let _, fl = add_list_list (Sid.empty, []) l in
  List.rev fl

let (|>>>) (v1, c1) lcv2 =
  let lv2, lc2 = List.split lcv2 in
  assert (List.length v1 = List.length lv2);
  let lvc1 = List.combine v1 lc2 in
  let map = List.fold_left (fun map (v, c) -> Mid.add v c map) Mid.empty lvc1 in
  flatten_uniq lv2, fill map c1

let rec iterate n v = if n = 0 then [] else v :: iterate (n-1) v

let (|>>) (v1, c1) (v2, c2) =
  let n = List.length v1 in
  let lcv2 = iterate n (v2, c2) in
  (v1, c1) |>>> lcv2

let (||>) (v1, c1) f =
  let n = List.length v1 in
  let lcv2 = List.map f (iterate n ()) in
  (v1, c1) |>>> lcv2

(* Use propagate to define recursive functions on elements of type ecert *)
(* TODO : rename g in pos, f in fc, fid in fi *)
let propagate_ecert f fid ft = function
  | EHole _ as c -> c
  | ECut (i, a, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      ECut (fid i, ft a, f1, f2)
  | ELet (x, y, c) -> ELet (ft x, ft y, f c)
  | EAxiom (a, i1, i2) -> EAxiom (ft a, fid i1, fid i2)
  | ETrivial (g, i) -> ETrivial (g, fid i)
  | EEqRefl (cty, t, i) -> EEqRefl (cty, ft t, fid i)
  | EEqSym (g, cty, t1, t2, i, c) -> EEqSym (g, cty, ft t1, ft t2, fid i, f c)
  | EEqTrans (cty, t1, t2, t3, i1, i2, i3, c) ->
      EEqTrans (cty, ft t1, ft t2, ft t3, fid i1, fid i2, fid i3, f c)
  | ESplit (g, a, b, i, c1, c2) ->
      let f1 = f c1 in let f2 = f c2 in
      ESplit (g, ft a, ft b, fid i, f1, f2)
  | EUnfoldIff (g, a, b, i, c) -> EUnfoldIff (g, ft a, ft b, fid i, f c)
  | EUnfoldArr (g, a, b, i, c) -> EUnfoldArr (g, ft a, ft b, fid i, f c)
  | EFoldArr (g, a, b, i, c) -> EFoldArr (g, ft a, ft b, fid i, f c)
  | EDestruct (g, a, b, i, j1, j2, c) -> EDestruct (g, ft a, ft b, fid i, fid j1, fid j2, f c)
  | EConstruct (g, a, b, i1, i2, j, c) -> EConstruct (g, ft a, ft b, fid i1, fid i2, fid j, f c)
  | ESwap (g, a, i, c) -> ESwap (g, ft a, fid i, f c)
  | ESwapNeg (g, a, i, c) -> ESwapNeg (g, ft a, fid i, f c)
  | EWeakening (g, a, i, c) -> EWeakening (g, ft a, fid i, f c)
  | EDuplicate (g, a, i1, i2, c) -> EDuplicate (g, ft a, fid i1, fid i2, f c)
  | EIntroQuant (g, p, i, y, c) -> EIntroQuant (g, ft p, fid i, y, f c)
  | EInstQuant (g, p, i, j, t, c) -> EInstQuant (g, ft p, fid i, fid j, ft t, f c)
  | ERewrite (g, cty, a, b, ctxt, i, h, c) ->
      ERewrite (g, cty, ft a, ft b, ft ctxt, fid i, fid h, f c)


(* Separates hypotheses and goals *)
let split_hyp_goal cta =
  let open Mid in
  fold (fun h (ct, pos) (gamma, delta) ->
      if pos then gamma, add h (ct, pos) delta
      else add h (ct, pos) gamma, delta)
    cta (empty, empty)

(* Creates a new ctask with the same hypotheses but sets the goal with the second argument *)
let set_goal : ctask -> cterm -> ctask = fun cta ->
  let gamma, delta = split_hyp_goal cta.gamma_delta in
  let gpr, _ = Mid.choose gamma in
  fun ct -> { sigma = cta.sigma;
              gamma_delta = Mid.add gpr (ct, true) delta }


(** Compile chain.
    1. visible_cert
       The certificates given by certifying transformations.
       Many constructors and few parameters to ease making certifying
       a transformation.
    2. abstract_cert
       Same as before but with simpler types that can be used by our checkers.
    3. heavy_ecert
       The result of the elaboration and as such contains many additional
       information such as the current formula and whether the focus is on a
       goal or on a hypothesis.
    4. trimmed_ecert
       Same as before except that rules that are derivable with core rules when
       given additional information are replaced (Duplicate, Construct).
    5. kernel_ecert
       The certificates used by checkers.
       Few constructors and many parameters to ease formal verification of
       checkers.

*)

let rec abstract_cert c =
  propagate_cert abstract_cert (fun pr -> pr.pr_name) abstract_term c

exception Elaboration_failed

(* TODO can we remove this ? *)
module Hashid = Hashtbl.Make(struct type t = ident let equal = id_equal let hash = id_hash end)

let rewrite_ctask (cta : ctask) i a b ctxt =
  let ctxt = match ctxt with
    | CTquant (CTlambda, _, ctxt) -> ctxt
    | _ -> assert false in
  let ta = ct_open ctxt a in
  let tb = ct_open ctxt b in
  let rewrite_decl j (t, pos) =
    if id_equal j i && cterm_equal t ta
    then tb, pos
    else t, pos in
  lift_mid_cta (Mid.mapi rewrite_decl) cta

(* TODO can we remove this ? *)
let rec replace_cterm tl tr t =
  if cterm_equal t tl
  then tr
  else cterm_map (replace_cterm tl tr) t

let elaborate (init_ct : ctask) c =
  let rec elab (cta : ctask) c =
  match c with
  | Nc -> eprintf "No certificates@.";
          raise Elaboration_failed
  | Hole i -> EHole i
  | Axiom (i1, i2) ->
      let t1, pos1 = find_ident "Axiom" i1 cta in
      let t2, pos2 = find_ident "Axiom" i2 cta in
      assert (pos1 <> pos2 && cterm_equal t1 t2);
      let i1, i2 = if pos2 then i1, i2 else i2, i1 in
      EAxiom (t1, i1, i2)
  | Trivial i ->
      let t, pos = find_ident "Trivial" i cta in
      begin match t, pos with
      | CTapp (CTapp (e, t1), t2), _ when cterm_equal t1 t2 && cterm_equal e eq ->
          let cty = infer_type cta t1 in
          EEqRefl (cty, t1, i)
      | CTfalse, false | CTtrue, true ->
          ETrivial (pos, i)
      | _ -> eprintf "not an equality or not same terms in eqrefl";
             raise Elaboration_failed end
  | EqSym (i, c) ->
      let t, pos = find_ident "EqSym" i cta in
      begin match t with
      | CTapp (CTapp (e, t1), t2) when cterm_equal e eq ->
          let cty = infer_type cta t1 in
          let rev_eq = CTapp (CTapp (eq, t2), t1) in
          let cta = add i (rev_eq, pos) (remove i cta) in
          EEqSym (pos, cty, t1, t2, i, elab cta c)
      | _ -> eprintf "not an equality"; raise Elaboration_failed end
  | EqTrans (i1, i2, i3, c) ->
      let t1, pos1 = find_ident "EqTrans" i1 cta in
      let t2, pos2 = find_ident "EqTrans" i2 cta in
      begin match t1, t2, pos1, pos2 with
      | CTapp (CTapp (e1, t11), t12), CTapp (CTapp (e2, t21), t22), false, false
        when cterm_equal t12 t21 && cterm_equal e1 eq && cterm_equal e2 eq ->
          let cty = infer_type cta t11 in
          let new_eq = CTapp (CTapp (eq, t11), t22) in
          let cta = add i3 (new_eq, false) cta in
          EEqTrans (cty, t11, t12, t22, i1, i2, i3, elab cta c)
      | _ -> eprintf "wrong hyps form in eqtrans";
             raise Elaboration_failed end
  | Cut (i, a, c1, c2) ->
      let cta1 = add i (a, true) cta in
      let cta2 = add i (a, false) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ECut (i, a, c1, c2)
  | Let (x, i, c) ->
      let y, _ = find_ident "Let" i cta in
      ELet (x, y, elab cta c)
  | Unfold (i, c) ->
      let t, pos = find_ident "Unfold" i cta in
      let iff, cta, t1, t2 = match t with
        | CTbinop (Tiff, t1, t2) ->
            let imp_pos = CTbinop (Timplies, t1, t2) in
            let imp_neg = CTbinop (Timplies, t2, t1) in
            let unfolded_iff = CTbinop (Tand, imp_pos, imp_neg), pos in
            true, add i unfolded_iff cta, t1, t2
        | CTbinop (Timplies, t1, t2) ->
            let unfolded_imp = CTbinop (Tor, CTnot t1, t2), pos in
            false, add i unfolded_imp cta, t1, t2
        | _ -> eprintf "Nothing to unfold : @[%a@]@." pcte t;
               raise Elaboration_failed in
      (* TODO remove pack *)
      let pack = pos, t1, t2, i, elab cta c in
      if iff
      then EUnfoldIff pack
      else EUnfoldArr pack
  | Fold (i, c) ->
      let t, pos = find_ident "Fold" i cta in
      let cta, t1, t2 = match t with
        | CTbinop (Tor, CTnot t1, t2) ->
            add i (CTbinop (Timplies, t1, t2), pos) cta, t1, t2
        | _ -> eprintf "Nothing to fold : @[%a@]@." pcte t;
               raise Elaboration_failed in
      let c = elab cta c in
      EFoldArr (pos, t1, t2, i, c)
      (* TODO fold iff *)
  | Split (i, c1, c2) ->
      let t, pos = find_ident "Split" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), true | CTbinop (Tor, t1, t2), false -> t1, t2
        | _ -> eprintf "Not splittable@.";
               raise Elaboration_failed in
      let cta1 = add i (t1, pos) cta in
      let cta2 = add i (t2, pos) cta in
      let c1 = elab cta1 c1 in
      let c2 = elab cta2 c2 in
      ESplit (pos, t1, t2, i, c1, c2)
  | Destruct (i, j1, j2, c) ->
      let t, pos = find_ident "Destruct" i cta in
      let t1, t2 = match t, pos with
        | CTbinop (Tand, t1, t2), false | CTbinop (Tor, t1, t2), true -> t1, t2
        | _ -> eprintf "Nothing to destruct@.";
               raise Elaboration_failed in
      let cta = remove i cta
                |> add j1 (t1, pos)
                |> add j2 (t2, pos) in
      EDestruct (pos, t1, t2, i, j1, j2, elab cta c)
  | Construct (i1, i2, j, c) ->
      let t1, pos1 = find_ident "Construct1" i1 cta in
      let t2, pos2 = find_ident "Construct2" i2 cta in
      assert (pos1 = pos2);
      let t = if pos1
              then CTbinop (Tor, t1, t2)
              else CTbinop (Tand, t1, t2) in
      let cta = remove i1 cta
                |> remove i2
                |> add j (t, pos1) in
      EConstruct (pos1, t1, t2, i1, i2, j, elab cta c)
  | Swap (i, c) ->
      let t, pos = find_ident "Swap" i cta in
      let neg, underlying_t, neg_t = match t with
        | CTnot t -> true, t, t
        | _ -> false, t, CTnot t in
      let cta = add i (neg_t, not pos) cta in
      let pack = pos, underlying_t, i, elab cta c in
      if neg
      then ESwapNeg pack
      else ESwap pack
  | Weakening (i, c) ->
      let t, pos = find_ident "Weakening" i cta in
      let cta = remove i cta in
      EWeakening (pos, t, i, elab cta c)
  | Duplicate (i1, i2, c) ->
      let t, pos = find_ident "Duplicate" i1 cta in
      let cta = add i2 (t, pos) cta in
      EDuplicate (pos, t, i1, i2, elab cta c)
  | IntroQuant (i, y, c) ->
      let t, pos = find_ident "IntroQuant" i cta in
      let t, ty = match t, pos with
        | CTquant (CTforall, ty, t), true | CTquant (CTexists, ty, t), false -> t, ty
        | _ -> eprintf "Nothing to introduce@.";
               raise Elaboration_failed in
      let cta = add i (ct_open t (CTfvar y), pos) cta
                |> add_var y ty in
      EIntroQuant (pos, CTquant (CTlambda, ty, t), i, y, elab cta c)
  | InstQuant (i, j, t_inst, c) ->
      let t, pos = find_ident "InstQuant" i cta in
      let t, ty = match t, pos with
        | CTquant (CTforall, ty, t), false | CTquant (CTexists, ty, t), true -> t, ty
        | _ -> eprintf "trying to instantiate a non-quantified hypothesis@.";
               raise Elaboration_failed in
      let cta = add j (ct_open t t_inst, pos) cta in
      EInstQuant (pos, CTquant (CTlambda, ty, t), i, j, t_inst, elab cta c)
  | Rewrite (i, h, c) ->
      let rew_hyp, _ = find_ident "Finding rewrite hypothesis" h cta in
      let a, b = match rew_hyp with
        | CTbinop (Tiff, a, b) -> a, b
        | CTapp (CTapp (f, a), b) when cterm_equal f eq -> a, b
        | _ -> eprintf "Rewrite hypothesis is badly-formed : %a@." pcte rew_hyp;
               raise Elaboration_failed in
      let t, pos = find_ident "Finding to be rewritten goal" i cta in
      let id = id_register (id_fresh "ctxt_var") in
      let v = CTfvar id in
      let cty = infer_type cta a in
      let ctxt = CTquant (CTlambda, cty, ct_close id (replace_cterm a v t)) in
      let cta = rewrite_ctask cta i a b ctxt in
      ERewrite (pos, cty, a, b, ctxt, i, h, elab cta c)
  in
  elab init_ct c

let eaxiom g a i j =
  if g then EAxiom (a, i, j)
  else EAxiom (a, j, i)

let eduplicate g a i1 i2 c =
  let c_closed = eaxiom (not g) a i1 i2 in
  let c1, c2 = if g
               then c, c_closed
               else c_closed, c in
  ECut (i2, a, c1, c2)

let erename g a i1 i2 c =
  eduplicate g a i1 i2 (EWeakening (g, a, i1, c))

let rec trim_certif c =
  match c with
  | EDuplicate (g, a, i1, i2, c) ->
      let c = trim_certif c in
      eduplicate g a i1 i2 c
  | EConstruct (g, a, b, i1, i2, j, c) ->
      let c = trim_certif c in
      let i1' = id_register (id_fresh "i1") in
      let i2' = id_register (id_fresh "i2") in
      erename g a i1 i1' (
          erename g b i2 i2' (
              let c_open = EWeakening (g, a, i1', EWeakening (g, b, i2', c)) in
              let c_closed = ESplit (not g, a, b, j,
                                     eaxiom (not g) a i1' j,
                                     eaxiom (not g) b i2' j) in
              let c1, c2, cut = if g
                                then c_open, c_closed, CTbinop (Tor, a, b)
                                else c_closed, c_open, CTbinop (Tand, a, b) in
              ECut (j, cut, c1, c2)))
  | EFoldArr (g, a, b, i, c) ->
      let c = trim_certif c in
      let j = id_register (id_fresh "fold_arr_temp") in
      let pre = CTbinop (Tor, CTnot a, b) in
      let post = CTbinop (Timplies, a, b) in
      let c_open = EWeakening (g, pre, j, c) in
      let c_closed = EUnfoldArr (not g, a, b, i, eaxiom g pre i j) in
      let c1, c2 = if g then c_open, c_closed else c_closed, c_open in
      erename g pre i j (ECut (i, post, c1, c2))
  | _ -> propagate_ecert trim_certif (fun t -> t) (fun i -> i) c

let rec eliminate_let m c =
  match c with
    | ELet (x, y, c) ->
        let x = match x with
                | CTfvar id -> id
                | _ -> assert false in
        let m = Mid.add x y m in
        eliminate_let m c
    | ECut (i, a, c1, c2) ->
        let c1 = eliminate_let m c1 in
        let c2 = eliminate_let m c2 in
        let a = ct_subst m a in
        ECut (i, a, c1, c2)
    | _ -> propagate_ecert (eliminate_let m) (fun t -> t) (fun i -> i) c

let make_core (init_ct : ctask) (_ : ctask list) (v, c : visible_cert) : heavy_ecert =
  (* Format.eprintf "%a@." prcertif c; *)
  v, abstract_cert c
     |> elaborate init_ct
     |> trim_certif
     |> eliminate_let Mid.empty
