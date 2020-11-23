// Define CoC encoding

constant symbol Utype : TYPE
constant symbol Ukind : TYPE

symbol etype : Utype → TYPE
symbol ekind : Ukind → TYPE

constant symbol dottype : Ukind
rule ekind dottype ↪ Utype

symbol dotpi1 : Π (x : Utype), (etype x → Utype) → Utype
symbol dotpi2 : Π (x : Utype), (etype x → Ukind) → Ukind
symbol dotpi3 : Π (x : Ukind), (ekind x → Utype) → Utype
symbol dotpi4 : Π (x : Ukind), (ekind x → Ukind) → Ukind

rule etype (dotpi1 $x $y) ↪  Π (w : etype $x), etype ($y w)
rule etype (dotpi3 $x $y) ↪  Π (w : ekind $x), etype ($y w)
rule ekind (dotpi2 $x $y) ↪  Π (w : etype $x), ekind ($y w)
rule ekind (dotpi4 $x $y) ↪  Π (w : ekind $x), ekind ($y w)


// Derive first-order logic connectives

definition arrow A B ≔  dotpi4 A (λ _, B)
set infix right 14 "⇒" ≔  arrow

set prefix 20 "∀" ≔  dotpi3

definition forall ≔  ∀ dottype

definition false ≔  forall (λ C, C)

definition type_imp A B ≔  dotpi1 A (λ _, B)
set infix right 14 "⇨" ≔  type_imp

definition true ≔  false ⇨ false

definition tt : etype true ≔  λ x, x

definition type_neg A ≔  A ⇨ false
set prefix      20 "¬" ≔  type_neg

definition type_and A B ≔  forall (λ C, (A ⇨ B ⇨ C) ⇨ C)
set infix right 18 "∧" ≔  type_and

definition type_or  A B ≔  forall (λ C, (A ⇨ C) ⇨ (B ⇨ C) ⇨ C)
set infix right 16 "∨" ≔  type_or

definition exists_gen T P ≔  forall (λ C, (∀ T) (λ x, P x ⇨ C) ⇨  C)
set prefix 20 "∃" ≔  exists_gen

definition exists ≔  exists_gen dottype

definition eq T x y ≔  (∀ (T ⇒ dottype))
                       (λ P, P x ⇨ P y)

definition equiv A B ≔  (A ⇨ B) ∧ (B ⇨ A)

symbol iff_eq : Π (A : Utype) (B : Utype),
       	        etype (equiv A B) →
		etype (eq dottype A B)

// Integers

constant symbol Nat : Ukind

constant symbol zero : ekind Nat

constant symbol succ : ekind Nat → ekind Nat

definition one ≔  succ zero

set builtin "0"  ≔  zero
set builtin "+1" ≔  succ


definition infixspeq ≔  eq Nat


// Booleans

constant symbol Bool : Ukind

constant symbol True : ekind Bool
constant symbol False : ekind Bool


// Define sequents : the sequent <A, B ⊢ C, D> is represented by <A → B → ¬ C → ¬ D → false>.

definition empty : Utype
≔  false

definition hyp : Utype → Utype → Utype
≔  λ A s, A ⇨ s

definition goal : Utype → Utype → Utype
≔  λ A s, ¬ A ⇨ s



// Excluded-middle axiom and reasoning about negation.

definition prop_iff : Utype → Utype → Utype
≔  λ A B, (A ⇨ B) ∧ (B ⇨ A)

set infix right 14 "⇔" ≔  prop_iff

definition nni : Π A, etype A → etype (¬ ¬ A)
≔  λ A a na, na a

definition contra : Π A B, (etype A → etype B) → etype (¬ B) → etype (¬ A)
≔  λ A B p nb a, nb (p a)

symbol em : Π A, etype (A ∨ ¬ A)

definition nne : Π A, etype (¬ ¬ A) → etype A
≔  λ A nna, em A A (λ a, a) (λ na, nna na A)



// Theorems

// Implication

definition imp_elim : Π A B, etype (A ⇨ B) → etype A → etype B
≔  λ A B p, p

definition imp_intro : Π A B, (etype A → etype B) → etype (A ⇨ B)
≔  λ A B p, p

// Disjunction

definition or_intro_1 : Π A B, etype A → etype (A ∨ B)
≔  λ A B (a : etype A) C (ac: etype A → etype C) _, ac a

definition or_intro_2 : Π A B, etype B → etype (A ∨ B)
≔  λ A B (b : etype B) C _ (bc: etype B → etype C), bc b

definition or_elim : Π A B, etype (A ∨ B) → Π C, etype (A ⇨ C) → etype (B ⇨ C) → etype C
≔  λ A B ab, ab

// Conjunction

definition and_intro : Π A B, etype A → etype B → etype (A ∧ B)
≔  λ A B a b C (p : etype A → etype B → etype C), p a b

definition and_elim_1 : Π A B, etype (A ∧ B) → etype A
≔  λ A B (ab : etype (A ∧ B)), ab A (λ a _, a)

definition and_elim_2 : Π A B, etype (A ∧ B) → etype B
≔  λ A B (ab : etype (A ∧ B)), ab B (λ _ b, b)

// Universal quantifier

definition forall_intro : Π P, (Π t, etype (P t)) → etype (forall P)
≔  λ P p, p

definition forall_elim : Π P t, etype (forall P) → etype (P t)
≔  λ P t p, p t

// Existential quantifier

definition exists_intro : Π T P t, etype (P t) → etype ((∃ T) P)
≔  λ T P t pt C (q : Π x, etype (P x) → etype C), q t pt

definition exists_elim : Π T P Q, etype ((∃ T) P) →  (Π x, etype (P x ⇨ Q)) → etype Q
≔  λ T P Q e pq, e Q pq

// Equality

definition eq_refl : Π T x, etype (eq T x x)
≔  λ T x P px, px

definition eq_sym : Π T x y, etype (eq T x y) → etype (eq T y x)
≔  λ T x y eqxy, eqxy (λ t, eq T t x) (eq_refl T x)

definition eq_trans : Π T x y z, etype (eq T x y) → etype (eq T y z) → etype (eq T x z)
≔  λ T x y z eqxy eqyz, eqyz (λ t, eq T x t) eqxy



// Certificate lines

definition hole :
  etype empty →
  etype empty
≔  λ f, f

definition axiom : Π A,
  etype (hyp A (goal A empty))
≔  λ A a na, na a

definition trivial_hyp :
  etype (hyp false empty)
≔  λ f, f

definition trivial_goal :
  etype (goal true empty)
≔  λ ntt, ntt tt

definition eqrefl : Π T t,
  etype (goal (eq T t t) empty)
≔  λ T t neqtt, neqtt (eq_refl T t)

definition cut : Π A,
  etype (goal A empty) →
  etype (hyp A empty) →
  etype empty
≔  λ A nna na, nna na

definition split_hyp : Π A B,
  etype (hyp A empty) →
  etype (hyp B empty) →
  etype (hyp (A ∨ B) empty)
≔  λ A B s1 s2 ab, or_elim A B ab false s1 s2

definition split_goal : Π A B,
    etype (goal A empty) →
    etype (goal B empty) →
    etype (goal (A ∧ B) empty)
≔  λ A B nna nnb, nni (A ∧ B) (and_intro A B (nne A nna) (nne B nnb))

definition unfold_iff_hyp : Π A B,
    etype (hyp ((A ⇨ B) ∧ (B ⇨ A)) empty) →
    etype (hyp (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_iff_goal : Π A B,
    etype (goal ((A ⇨ B) ∧ (B ⇨ A)) empty) →
    etype (goal (A ⇔ B) empty)
≔  λ A B s, s

definition unfold_arr_hyp : Π A B,
    etype (hyp (¬ A ∨ B) empty) →
    etype (hyp (A ⇨ B) empty)
≔  λ A B s impab,
   s (em A (¬ A ∨ B) (λ a, or_intro_2 (¬ A) B (impab a))
     	      	     (λ na, or_intro_1 (¬ A) B na))

definition unfold_arr_goal : Π A B,
    etype (goal (¬ A ∨ B) empty) →
    etype (goal (A ⇨ B) empty)
≔  λ A B s, nni (A ⇨ B) (λ a,
      nne (¬ A ∨ B) s B (λ na, na a B)
                        (λ b, b))

definition swap_neg_hyp : Π A,
    etype (goal A empty) →
    etype (hyp (¬ A) empty)
≔  λ A s, s

definition swap_hyp : Π A,
    etype (goal (¬ A) empty) →
    etype (hyp A empty)
≔  λ A nnna, nne (¬ A) nnna

definition swap_goal : Π A,
    etype (hyp (¬ A) empty) →
    etype (goal A empty)
≔  λ A s, s

definition swap_neg_goal : Π A,
    etype (hyp A empty) →
    etype (goal (¬ A) empty)
≔  λ A na, nni (¬ A) na

definition destruct_hyp : Π A B,
    etype (hyp A (hyp B empty)) →
    etype (hyp (A ∧ B) empty)
≔  λ A B s ab,
   s (and_elim_1 A B ab) (and_elim_2 A B ab)

definition destruct_goal : Π A B,
    etype (goal A (goal B empty)) →
    etype (goal (A ∨ B) empty)
≔  λ A B s nab, s (λ a, nab (or_intro_1 A B a))
                  (λ b, nab (or_intro_2 A B b))

definition construct_goal : Π A B,
    etype (goal (A ∨ B) empty) →
    etype (goal A (goal B empty))
≔  λ A B s na nb, or_elim A B (nne (A ∨ B) s) false na nb

definition dir_left_hyp : Π A B,
    etype (hyp A empty) →
    etype (hyp (A ∧ B) empty)
≔  λ A B na ab, na (and_elim_1 A B ab)

definition dir_left_goal : Π A B,
    etype (goal A empty) →
    etype (goal (A ∨ B) empty)
≔  λ A B nna nab, nab (or_intro_1 A B (nne A nna))

definition dir_right_hyp : Π A B,
    etype (hyp B empty) →
    etype (hyp (A ∧ B) empty)
≔  λ A B nb ab, nb (and_elim_2 A B ab)

definition dir_right_goal : Π A B,
    etype (goal B empty) →
    etype (goal (A ∨ B) empty)
≔  λ A B nnb nab, nab (or_intro_2 A B (nne B nnb))

definition clear_hyp : Π A,
    etype empty →
    etype (hyp A empty)
≔  λ A f _, f

definition clear_goal : Π A,
    etype empty →
    etype (goal A empty)
≔  λ A f _, f

definition intro_quant_hyp : Π T (P : ekind (T ⇒ dottype)),
    (Π y, etype (hyp (P y) empty)) →
    etype (hyp ((∃ T) P) empty)
≔  λ T P s ep, exists_elim T P false ep s

definition intro_quant_goal : Π T P,
    (Π y, etype (goal (P y) empty)) →
    etype (goal ((∀ T) P) empty)
≔  λ T P s nfp, nfp (λ t, nne (P t) (s t))

definition inst_quant_goal : Π T P t,
    etype (goal ((∃ T) P) (goal (P t) empty)) →
    etype (goal ((∃ T) P) empty)
≔  λ T P t s nep, s nep (λ pt, nep (exists_intro T P t pt))

definition inst_quant_hyp : Π T P t,
    etype (hyp ((∀ T) (λ x, P x)) (hyp (P t) empty)) →
    etype (hyp ((∀ T) (λ x, P x)) empty)
≔  λ T P t s h, s h (h t)

definition rewrite_hyp : Π T a b P,
   etype (hyp (eq T a b) (hyp (P b) empty)) →
   etype (hyp (eq T a b) (hyp (P a) empty))
≔  λ T a b P s h i, s h (h P i)

definition rewrite_goal : Π T a b P,
   etype (hyp (eq T a b) (goal (P b) empty)) →
   etype (hyp (eq T a b) (goal (P a) empty))
≔  λ T a b P s h i, s h (h (λ x, ¬ P x) i)

definition iffeq : Π (A : Utype) (B : Utype),
	   	   etype (hyp (eq dottype A B) empty) →
		   etype (hyp (equiv A B) empty)

≔  λ A B s eab, s (iff_eq A B eab)


// To verify



