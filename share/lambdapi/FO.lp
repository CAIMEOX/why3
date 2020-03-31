constant symbol Term : TYPE
constant symbol Prop : TYPE
symbol prf : Prop ⇒ TYPE

constant symbol true : Prop
constant symbol false : Prop

symbol prop_neg : Prop ⇒ Prop
symbol prop_and : Prop ⇒ Prop ⇒ Prop
symbol prop_or  : Prop ⇒ Prop ⇒ Prop
symbol prop_imp : Prop ⇒ Prop ⇒ Prop

symbol forall : (Term ⇒ Prop) ⇒ Prop
symbol exists : (Term ⇒ Prop) ⇒ Prop
symbol term_equals : Term ⇒ Term ⇒ Prop

set prefix      20 "¬" ≔  prop_neg
set infix right 18 "∧" ≔  prop_and
set infix right 16 "∨" ≔  prop_or
set infix right 14 "⇨" ≔  prop_imp
set infix right 22 "=" ≔  term_equals

definition equiv A B ≔  (A ⇨ B) ∧ (B ⇨ A)

constant symbol tt : prf true

rule prf false     → ∀ C, prf C
rule prf (¬ &A)    → prf &A ⇒ prf false
rule prf (&A ∧ &B) → ∀ C, (prf &A ⇒ prf &B ⇒ prf C) ⇒ prf C
rule prf (&A ∨ &B) → ∀ C, (prf &A ⇒ prf C) ⇒ (prf &B ⇒ prf C) ⇒ prf C
rule prf (&A ⇨ &B) → prf &A ⇒ prf &B

rule prf (forall &P) → ∀ x, prf (&P x)
rule prf (exists &P) → ∀ C, (∀ x, prf (&P x) ⇒ prf C) ⇒ prf C
rule prf (&x = &y) → ∀ (P : Term ⇒ Prop), prf (P &x) ⇒ prf (P &y)

// Define sequents : the sequent <A, B ⊢ C, D> is represented by <A ⇒ B ⇒ ¬ C ⇒ ¬ D ⇒ false>.

definition empty : Prop
≔  false

definition hyp : Prop ⇒ Prop ⇒ Prop
≔  λ A s, A ⇨ s

definition goal : Prop ⇒ Prop ⇒ Prop
≔  λ A s, ¬ A ⇨ s


// Excluded-middle axiom and reasoning about negation.

definition prop_iff : Prop ⇒ Prop ⇒ Prop
≔  λ A B, (A ⇨ B) ∧ (B ⇨ A)

set infix right 14 "⇔" ≔  prop_iff

definition nni : ∀ A, prf A ⇒ prf (¬ ¬ A)
≔  λ A a na, na a

definition contra : ∀ A B, (prf A ⇒ prf B) ⇒ prf (¬ B) ⇒ prf (¬ A)
≔  λ A B p nb a, nb  (p a)

symbol em : ∀ A, prf (A ∨ ¬ A)

definition nne : ∀ A, prf (¬ ¬ A) ⇒ prf A
≔  λ A nna, em A A (λ a, a) (λ na, nna na A)




// Theorems

// Implication

definition imp_elim : ∀ A B, prf (A ⇨ B) ⇒ prf A ⇒ prf B
≔  λ A B p, p

definition imp_intro : ∀ A B, (prf A ⇒ prf B) ⇒ prf (A ⇨ B)
≔  λ A B p, p

// Disjunction

definition or_intro_1 : ∀ A B, prf A ⇒ prf (A ∨ B)
≔  λ A B (a : prf A) C (ac: prf A ⇒ prf C) _, ac a

definition or_intro_2 : ∀ A B, prf B ⇒ prf (A ∨ B)
≔  λ A B (b : prf B) C _ (bc: prf B ⇒ prf C), bc b

definition or_elim : ∀ A B, prf (A ∨ B) ⇒ ∀ C, prf (A ⇨ C) ⇒ prf (B ⇨ C) ⇒ prf C
≔  λ A B ab, ab

// Conjunction

definition and_intro : ∀ A B, prf A ⇒ prf B ⇒ prf (A ∧ B)
≔  λ A B a b C (p : prf A ⇒ prf B ⇒ prf C), p a b

definition and_elim_1 : ∀ A B, prf (A ∧ B) ⇒ prf A
≔  λ A B (ab : prf (A ∧ B)), ab A (λ a _, a)

definition and_elim_2 : ∀ A B, prf (A ∧ B) ⇒ prf B
≔  λ A B (ab : prf (A ∧ B)), ab B (λ _ b, b)

// Universal quantifier

definition forall_intro : ∀ P, (∀ t, prf (P t)) ⇒ prf (forall P)
≔  λ P p, p

definition forall_elim : ∀ P t, prf (forall P) ⇒ prf (P t)
≔  λ P t p, p t

// Existential quantifier

definition exists_intro : ∀ P t, prf (P t) ⇒ prf (exists P)
≔  λ P t pt C (q : ∀ x, prf (P x) ⇒ prf C), q t pt

definition exists_elim : ∀ P Q, prf (exists P) ⇒  (∀ x, prf (P x ⇨ Q)) ⇒ prf Q
≔  λ P Q e pq, e Q pq

// Equality

definition eq_refl : ∀ x, prf (x = x)
≔  λ x P px, px

definition eq_sym : ∀ x y, prf (x = y) ⇒ prf (y = x)
≔  λ x y eqxy, eqxy (λ t, t = x) (eq_refl x)

definition eq_trans : ∀ x y z, prf (x = y) ⇒ prf (y = z) ⇒ prf (x = z)
≔  λ x y z eqxy eqyz, eqyz (λ t, x = t) eqxy



// Certificate lines

definition hole : prf false ⇒ prf false
≔  λ f, f

definition axiom : ∀ A, prf A ⇒ prf (¬ A) ⇒ prf false
≔  λ A a na, na a

definition trivial_hyp : prf false ⇒ prf false
≔  λ f, f

definition trivial_goal : prf (¬ true) ⇒ prf false
≔  λ ntt, ntt tt

definition cut : ∀ A,
  prf (goal A empty) ⇒
  prf (hyp A empty) ⇒
  prf false
≔  λ A nna na, nna na

definition split_hyp : ∀ A B,
  prf (hyp A empty) ⇒
  prf (hyp B empty) ⇒
  prf (hyp (A ∨ B) empty)
≔  λ A B s1 s2 ab, or_elim A B ab false s1 s2

definition split_goal : ∀ A B,
    prf (goal A empty) ⇒
    prf (goal B empty) ⇒
    prf (goal (A ∧ B) empty)
≔ λ A B nna nnb, nni (A ∧ B) (and_intro A B (nne A nna) (nne B nnb))

definition unfold_iff_hyp : ∀ A B,
    prf (hyp ((A ⇨ B) ∧ (B ⇨ A)) empty) ⇒
    prf (hyp (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_iff_goal : ∀ A B,
    prf (goal ((A ⇨ B) ∧ (B ⇨ A)) empty) ⇒
    prf (goal (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_arr_hyp : ∀ A B,
    prf (hyp (¬ A ∨ B) empty) ⇒
    prf (hyp (A ⇨ B) empty)
≔  λ A B s impab,
   s (em A (¬ A ∨ B) (λ a, or_intro_2 (¬ A) B (impab a))
     	      	     (λ na, or_intro_1 (¬ A) B na))

definition unfold_arr_goal : ∀ A B,
    prf (goal (¬ A ∨ B) empty) ⇒
    prf (goal (A ⇨ B) empty)
≔  λ A B s, nni (A ⇨ B) (λ a,
      nne (¬ A ∨ B) s B (λ na, na a B)
                        (λ b, b))

definition swap_neg_hyp : ∀ A,
    prf (goal A empty) ⇒
    prf (hyp (¬ A) empty)
≔  λ A s, s

definition swap_hyp : ∀ A,
    prf (goal (¬ A) empty) ⇒
    prf (hyp A empty)
≔  λ A nnna, nne (¬ A) nnna

definition swap_goal : ∀ A,
    prf (hyp (¬ A) empty) ⇒
    prf (goal A empty)
≔  λ A s, s

definition swap_neg_goal : ∀ A,
    prf (hyp A empty) ⇒
    prf (goal (¬ A) empty)
≔  λ A na, nni (¬ A) na

definition destruct_hyp : ∀ A B,
    prf (hyp A (hyp B empty)) ⇒
    prf (hyp (A ∧ B) empty)
≔  λ A B s ab,
   s (and_elim_1 A B ab) (and_elim_2 A B ab)

definition destruct_goal : ∀ A B,
    prf (goal A (goal B empty)) ⇒
    prf (goal (A ∨ B) empty)
≔  λ A B s nab, s (λ a, nab (or_intro_1 A B a))
                  (λ b, nab (or_intro_2 A B b))

definition construct_goal : ∀ A B,
    prf (goal (A ∨ B) empty) ⇒
    prf (goal A (goal B empty))
≔  λ A B s na nb, or_elim A B (nne (A ∨ B) s) false na nb

definition dir_left_hyp : ∀ A B,
    prf (hyp A empty) ⇒
    prf (hyp (A ∧ B) empty)
≔  λ A B na ab, na (and_elim_1 A B ab)

definition dir_left_goal : ∀ A B,
    prf (goal A empty) ⇒
    prf (goal (A ∨ B) empty)
≔  λ A B nna nab, nab (or_intro_1 A B (nne A nna))

definition dir_right_hyp : ∀ A B,
    prf (hyp B empty) ⇒
    prf (hyp (A ∧ B) empty)
≔  λ A B nb ab, nb (and_elim_2 A B ab)

definition dir_right_goal : ∀ A B,
    prf (goal B empty) ⇒
    prf (goal (A ∨ B) empty)
≔  λ A B nnb nab, nab (or_intro_2 A B (nne B nnb))

definition weakening_hyp : ∀ A,
    prf empty ⇒
    prf (hyp A empty)
≔  λ A f _, f

definition weakening_goal : ∀ A,
    prf empty ⇒
    prf (goal A empty)
≔  λ A f _, f

definition intro_quant_hyp : ∀ P,
    (∀ y, prf (hyp (P y) empty)) ⇒
    prf (hyp (exists P) empty)
≔  λ P s ep, exists_elim P false ep s

definition intro_quant_goal : ∀ P,
    (∀ y, prf (goal (P y) empty)) ⇒
    prf (goal (forall P) empty)
≔  λ P s nfp, nfp (λ t, nne (P t) (s t))

definition inst_quant_goal : ∀ P t,
    prf (goal (exists P) (goal (P t) empty)) ⇒
    prf (goal (exists P) empty)
≔  λ P t s nep, s nep (λ pt, nep (exists_intro P t pt))

definition inst_quant_hyp : ∀ P t,
    prf (hyp (forall (λ x, P x)) (hyp (P t) empty)) ⇒
    prf (hyp (forall (λ x, P x)) empty)
≔  λ P t s h, s h (h t)


// definition to_verify :
// (∀ a, prf (¬ a ⇨ false)) ⇒
// (∀ b, prf (¬ b ⇨ false)) ⇒
// ∀ a b, prf (¬ (a ∧ b) ⇨ false)
// ≔  λ s1 s2 a b G1, split_goal (a) (b) (λ G1, s1 a G1) (λ G1, s2 b G1) G1

