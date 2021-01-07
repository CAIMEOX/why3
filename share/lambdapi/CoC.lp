// Define CoC encoding


constant symbol Type : TYPE
constant symbol Kind : TYPE

symbol tEv : Type → TYPE
symbol kEv : Kind → TYPE

constant symbol Prop : Kind
rule kEv Prop ↪ Type

symbol ttPi : Π (x : Type), (tEv x → Type) → Type
symbol tkPi : Π (x : Type), (tEv x → Kind) → Kind
symbol ktPi : Π (x : Kind), (kEv x → Type) → Type
symbol kkPi : Π (x : Kind), (kEv x → Kind) → Kind

rule tEv (ttPi $x $y) ↪  Π (w : tEv $x), tEv ($y w)
rule tEv (ktPi $x $y) ↪  Π (w : kEv $x), tEv ($y w)
rule kEv (tkPi $x $y) ↪  Π (w : tEv $x), kEv ($y w)
rule kEv (kkPi $x $y) ↪  Π (w : kEv $x), kEv ($y w)


// Derive first-order logic connectives

definition t_prop A B ≔  tkPi A (λ _, B)
definition t_type A B ≔  ttPi A (λ _, B)
set infix right 14 "⇒" ≔  t_type

set declared "∀"
definition ∀ ≔  ttPi

definition forall ≔  ktPi Prop

definition false ≔  forall (λ C, C)

definition type_imp A B ≔  ttPi A (λ _, B)
set infix right 14 "⇨" ≔  type_imp

definition true ≔  false ⇨ false

definition tt : tEv true ≔  λ x, x

definition type_neg A ≔  A ⇨ false
set prefix      20 "¬" ≔  type_neg

definition type_and A B ≔  forall (λ C, (A ⇨ B ⇨ C) ⇨ C)
set infix right 18 "∧" ≔  type_and

definition type_or  A B ≔  forall (λ C, (A ⇨ C) ⇨ (B ⇨ C) ⇨ C)
set infix right 16 "∨" ≔  type_or

set declared "∃"
definition ∃ T P ≔  forall (λ C, ttPi T (λ x, P x ⇨ C) ⇨  C)

definition eq T x y ≔  ktPi (t_prop T Prop)
                       (λ P, P x ⇨ P y)

definition type_iff A B ≔  (A ⇨ B) ∧ (B ⇨ A)
set infix right 14 "⇔" ≔  type_iff

symbol iff_eq : Π (A : Type) (B : Type),
       	        tEv (type_iff A B) →
		tEv (ktPi (kkPi Prop (λ _, Prop))
		     (λ P, P A ⇨ P B))

// Integers

constant symbol Nat : Type

constant symbol zero : tEv Nat

constant symbol succ : tEv Nat → tEv Nat

definition one ≔  succ zero

set builtin "0"  ≔  zero
set builtin "+1" ≔  succ


definition infixspeq ≔  eq Nat


// Booleans

constant symbol Bool : Type

constant symbol True : tEv Bool
constant symbol False : tEv Bool


// Define sequents : the sequent <A, B ⊢ C, D> is represented by <A → B → ¬ C → ¬ D → false>.

definition empty : Type
≔  false

definition hyp : Type → Type → Type
≔  λ A s, A ⇨ s

definition goal : Type → Type → Type
≔  λ A s, ¬ A ⇨ s



// Excluded-middle axiom and reasoning about negation.

definition nni : Π A, tEv A → tEv (¬ ¬ A)
≔  λ A a na, na a

definition contra : Π A B, (tEv A → tEv B) → tEv (¬ B) → tEv (¬ A)
≔  λ A B p nb a, nb (p a)

symbol em : Π A, tEv (A ∨ ¬ A)

definition nne : Π A, tEv (¬ ¬ A) → tEv A
≔  λ A nna, em A A (λ a, a) (λ na, nna na A)



// Theorems

// Implication

definition imp_elim : Π A B, tEv (A ⇨ B) → tEv A → tEv B
≔  λ A B p, p

definition imp_intro : Π A B, (tEv A → tEv B) → tEv (A ⇨ B)
≔  λ A B p, p

// Disjunction

definition or_intro_1 : Π A B, tEv A → tEv (A ∨ B)
≔  λ A B (a : tEv A) C (ac: tEv A → tEv C) _, ac a

definition or_intro_2 : Π A B, tEv B → tEv (A ∨ B)
≔  λ A B (b : tEv B) C _ (bc: tEv B → tEv C), bc b

definition or_elim : Π A B, tEv (A ∨ B) → Π C, tEv (A ⇨ C) → tEv (B ⇨ C) → tEv C
≔  λ A B ab, ab

// Conjunction

definition and_intro : Π A B, tEv A → tEv B → tEv (A ∧ B)
≔  λ A B a b C (p : tEv A → tEv B → tEv C), p a b

definition and_elim_1 : Π A B, tEv (A ∧ B) → tEv A
≔  λ A B (ab : tEv (A ∧ B)), ab A (λ a _, a)

definition and_elim_2 : Π A B, tEv (A ∧ B) → tEv B
≔  λ A B (ab : tEv (A ∧ B)), ab B (λ _ b, b)

// Universal quantifier

definition forall_intro : Π P, (Π t, tEv (P t)) → tEv (forall P)
≔  λ P p, p

definition forall_elim : Π P t, tEv (forall P) → tEv (P t)
≔  λ P t p, p t

// Existential quantifier

definition exists_intro : Π T P t, tEv (P t) → tEv (∃ T P)
≔  λ T P t pt C (q : Π x, tEv (P x) → tEv C), q t pt

definition exists_elim : Π T P Q, tEv (∃ T P) →  (Π x, tEv (P x ⇨ Q)) → tEv Q
≔  λ T P Q e pq, e Q pq

// Equality

definition eq_refl : Π T x, tEv (eq T x x)
≔  λ T x P px, px

definition eq_sym : Π T x y, tEv (eq T x y) → tEv (eq T y x)
≔  λ T x y eqxy, eqxy (λ t, eq T t x) (eq_refl T x)

definition eq_trans : Π T x y z, tEv (eq T x y) → tEv (eq T y z) → tEv (eq T x z)
≔  λ T x y z eqxy eqyz, eqyz (λ t, eq T x t) eqxy



// Certificate lines

definition hole :
  tEv empty →
  tEv empty
≔  λ f, f

definition axiom : Π A,
  tEv (hyp A (goal A empty))
≔  λ A a na, na a

definition trivial_hyp :
  tEv (hyp false empty)
≔  λ f, f

definition trivial_goal :
  tEv (goal true empty)
≔  λ ntt, ntt tt

definition eqrefl : Π T t,
  tEv (goal (eq T t t) empty)
≔  λ T t neqtt, neqtt (eq_refl T t)

definition cut : Π A,
  tEv (goal A empty) →
  tEv (hyp A empty) →
  tEv empty
≔  λ A nna na, nna na

definition split_hyp : Π A B,
  tEv (hyp A empty) →
  tEv (hyp B empty) →
  tEv (hyp (A ∨ B) empty)
≔  λ A B s1 s2 ab, or_elim A B ab false s1 s2

definition split_goal : Π A B,
    tEv (goal A empty) →
    tEv (goal B empty) →
    tEv (goal (A ∧ B) empty)
≔  λ A B nna nnb, nni (A ∧ B) (and_intro A B (nne A nna) (nne B nnb))

definition unfold_iff_hyp : Π A B,
    tEv (hyp ((A ⇨ B) ∧ (B ⇨ A)) empty) →
    tEv (hyp (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_iff_goal : Π A B,
    tEv (goal ((A ⇨ B) ∧ (B ⇨ A)) empty) →
    tEv (goal (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_arr_hyp : Π A B,
    tEv (hyp (¬ A ∨ B) empty) →
    tEv (hyp (A ⇨ B) empty)
≔  λ A B s impab,
   s (em A (¬ A ∨ B) (λ a, or_intro_2 (¬ A) B (impab a))
     	      	     (λ na, or_intro_1 (¬ A) B na))

definition unfold_arr_goal : Π A B,
    tEv (goal (¬ A ∨ B) empty) →
    tEv (goal (A ⇨ B) empty)
≔  λ A B s, nni (A ⇨ B) (λ a,
      nne (¬ A ∨ B) s B (λ na, na a B)
                        (λ b, b))

definition swap_neg_hyp : Π A,
    tEv (goal A empty) →
    tEv (hyp (¬ A) empty)
≔  λ A s, s

definition swap_hyp : Π A,
    tEv (goal (¬ A) empty) →
    tEv (hyp A empty)
≔  λ A nnna, nne (¬ A) nnna

definition swap_goal : Π A,
    tEv (hyp (¬ A) empty) →
    tEv (goal A empty)
≔  λ A s, s

definition swap_neg_goal : Π A,
    tEv (hyp A empty) →
    tEv (goal (¬ A) empty)
≔  λ A na, nni (¬ A) na

definition destruct_hyp : Π A B,
    tEv (hyp A (hyp B empty)) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B s ab,
   s (and_elim_1 A B ab) (and_elim_2 A B ab)

definition destruct_goal : Π A B,
    tEv (goal A (goal B empty)) →
    tEv (goal (A ∨ B) empty)
≔  λ A B s nab, s (λ a, nab (or_intro_1 A B a))
                  (λ b, nab (or_intro_2 A B b))

definition construct_goal : Π A B,
    tEv (goal (A ∨ B) empty) →
    tEv (goal A (goal B empty))
≔  λ A B s na nb, or_elim A B (nne (A ∨ B) s) false na nb

definition dir_left_hyp : Π A B,
    tEv (hyp A empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B na ab, na (and_elim_1 A B ab)

definition dir_left_goal : Π A B,
    tEv (goal A empty) →
    tEv (goal (A ∨ B) empty)
≔  λ A B nna nab, nab (or_intro_1 A B (nne A nna))

definition dir_right_hyp : Π A B,
    tEv (hyp B empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B nb ab, nb (and_elim_2 A B ab)

definition dir_right_goal : Π A B,
    tEv (goal B empty) →
    tEv (goal (A ∨ B) empty)
≔  λ A B nnb nab, nab (or_intro_2 A B (nne B nnb))

definition clearhyp : Π A,
    tEv empty →
    tEv (hyp A empty)
≔  λ A f _, f

definition clear_hyp A HA s ≔  clearhyp A s HA

definition cleargoal : Π A,
    tEv empty →
    tEv (goal A empty)
≔  λ A f _, f

definition clear_goal A HA s ≔  cleargoal A s HA

definition intro_quant_hyp : Π (T : Type) (P : kEv (t_prop T Prop)),
    (Π (y : tEv T), tEv (hyp (P y) empty)) →
    tEv (hyp (∃ T P) empty)
≔  λ T P s ep, exists_elim T P false ep s

definition intro_quant_goal : Π T P,
    (Π (y : tEv T), tEv (goal (P y) empty)) →
    tEv (goal (∀ T P) empty)
≔  λ T P s nfp, nfp (λ t, nne (P t) (s t))

definition inst_quant_goal : Π T P t,
    tEv (goal (∃ T P) (goal (P t) empty)) →
    tEv (goal (∃ T P) empty)
≔  λ T P t s nep, s nep (λ pt, nep (exists_intro T P t pt))

definition inst_quant_hyp : Π T P t,
    tEv (hyp (∀ T (λ x, P x)) (hyp (P t) empty)) →
    tEv (hyp (∀ T (λ x, P x)) empty)
≔  λ T P t s h, s h (h t)

definition rewrite_hyp : Π T a b P,
   tEv (hyp (eq T a b) (hyp (P b) empty)) →
   tEv (hyp (eq T a b) (hyp (P a) empty))
≔  λ T a b P s h i, s h (h P i)

definition rewrite_goal : Π T a b P,
   tEv (hyp (eq T a b) (goal (P b) empty)) →
   tEv (hyp (eq T a b) (goal (P a) empty))
≔  λ T a b P s h i, s h (h (λ x, ¬ P x) i)

// definition iffeq : Π (A : Type) (B : Type),
// 	   	   tEv (hyp (eq Prop A B) empty) →
// 		   tEv (hyp (type_iff A B) empty)

// ≔  λ A B s eab, s (iff_eq A B eab)


// To verify



// definition to_verify :
//   tEv (ktPi Prop (λ unit,
//        ktPi Prop (λ t,
//        ∀ (t ⇒ t ⇒ t) (λ o,
//        ∀ t (λ e,
//        ∀ (t ⇒ t) (λ i,
//        ∀ t (λ y,
//        ∀ t (λ x, ∀ t (λ x1, ∀ t (λ x2, eq t (o (o x x1) x2) (o x (o x1 x2))))) ⇨
//        ∀ t (λ x, eq t (o e x) x) ⇨
//        ∀ t (λ x, eq t (o x e) x) ⇨
//        ∀ t (λ x, eq t (o (i x) x) e) ⇨
//        ¬ (eq t (i y) (i y)) ⇨
//        false)))))))
// ≔  λ unit t o e i y Hassoc Hidusleft Hidusright Hinvusleft Hh,
//    eqrefl t (i y) Hh
