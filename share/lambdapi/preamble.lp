// Define CoC encoding


symbol Type : TYPE;
symbol Kind : TYPE;

symbol tEv : Type → TYPE;
symbol kEv : Kind → TYPE;

symbol DType : Kind;
rule kEv DType ↪ Type;

symbol ttPi : Π (x : Type), (tEv x → Type) → Type;
symbol tkPi : Π (x : Type), (tEv x → Kind) → Kind;
symbol ktPi : Π (x : Kind), (kEv x → Type) → Type;
symbol kkPi : Π (x : Kind), (kEv x → Kind) → Kind;

rule tEv (ttPi $x $y) ↪  Π (w : tEv $x), tEv ($y w);
rule tEv (ktPi $x $y) ↪  Π (w : kEv $x), tEv ($y w);
rule kEv (tkPi $x $y) ↪  Π (w : tEv $x), kEv ($y w);
rule kEv (kkPi $x $y) ↪  Π (w : kEv $x), kEv ($y w);

symbol ⇀ A B ≔  tkPi A (λ _, B);
notation ⇀ infix right 14;

symbol ⇁ A B ≔  ttPi A (λ _, B);
notation ⇁ infix right 14;

symbol ∀ ≔  ttPi;

symbol forall ≔  ktPi DType;

symbol false ≔  forall (λ C, C);

symbol ↝ A B ≔  ttPi A (λ _, B);
notation ↝ infix right 14;

symbol true ≔  false ↝ false;

symbol tt : tEv true ≔  λ x, x;

symbol ¬ A ≔  A ↝ false;
notation ¬ prefix 20;

symbol ∧ A B ≔  forall (λ C, (A ↝ B ↝ C) ↝ C);
notation ∧ infix right 18;

symbol ∨ A B ≔  forall (λ C, (A ↝ C) ↝ (B ↝ C) ↝ C);
notation ∨ infix right 16;

symbol ∃ T P ≔  forall (λ C, ttPi T (λ x, P x ↝ C) ↝  C);

symbol infixspeq T (x y : tEv T) ≔  ktPi (T ⇀ DType)
       	       	       	     	         (λ P, P x ↝ P y);

symbol eq_fmla A B ≔  ktPi (kkPi DType (λ _, DType))
		           (λ P, P A ↝ P B);

symbol ⇔ A B ≔  (A ↝ B) ∧ (B ↝ A);
notation ⇔ infix right 14;

symbol iff_eq : Π (A : Type) (B : Type),
       	        tEv (A ⇔  B) →
		tEv (eq_fmla A B);



// Integers

symbol pos : Type;
symbol positive ≔ tEv pos;

symbol xI : positive → positive;
symbol xO : positive → positive;
symbol xH : positive;

symbol positive_rect :
  tEv (ktPi (pos ⇀ DType) (λ Q,
       (∀ pos (λ p, Q p ↝ Q (xI p))) ↝
       (∀ pos (λ p, Q p ↝ Q (xO p))) ↝
       Q xH ↝
       ∀ pos (λ p, Q p)));

// symbol positive_rect :  Π (Q : positive → Type),
//   (Π p, tEv (Q p) → tEv (Q (xI p))) →
//   (Π p, tEv (Q p) → tEv (Q (xO p))) →
//   tEv (Q xH) →
//   Π p, tEv (Q p);

rule positive_rect _  _   _   $vH xH      ↪ $vH;
rule positive_rect $Q $vI $vO $vH (xI $p) ↪ $vI $p (positive_rect $Q $vI $vO $vH $p);
rule positive_rect $Q $vI $vO $vH (xO $p) ↪ $vO $p (positive_rect $Q $vI $vO $vH $p);

symbol pos_pred_double (x : positive) : positive ≔
  positive_rect (λ _, pos) (λ p _, xI (xO p)) (λ _ rp, xI rp) xH x;

// Check that 2 * 6 - 1 ≡ 11
// assert ⊢ pos_pred_double (xO (xI xH)) ≡ xI (xI (xO xH)); 

symbol int : Type;
symbol integer ≔ tEv int;

symbol Z0 : integer;
symbol Zpos : positive → integer;
symbol Zneg : positive → integer;

symbol integer_rect :
  tEv (ktPi (int ⇀ DType) (λ Q,
       Q Z0 ↝
       (∀ pos (λ p, Q (Zpos p))) ↝
       (∀ pos (λ p, Q (Zneg p))) ↝
       ∀ int (λ z, Q z)));

rule integer_rect _ $v0 _     _     Z0        ↪ $v0;
rule integer_rect _ _   $vpos _     (Zpos $x) ↪ $vpos $x;
rule integer_rect _ _   _     $vneg (Zneg $x) ↪ $vneg $x;

symbol zero ≔ Z0;
symbol one ≔ Zpos xH;

symbol double ≔
  integer_rect (λ _, int) zero
               (λ p, Zpos (xO p))
               (λ p, Zneg (xO p));

// Check that 2 * 7 ≡ 14
// assert ⊢ double (Zpos (xI (xI xH))) ≡ Zpos (xO (xI (xI xH))); 

symbol succ_double ≔
  integer_rect (λ _, int) one
               (λ p, Zpos (xI p))
               (λ p, Zneg (pos_pred_double p));

// Check that 2 * (-5) + 1 ≡ -9 and that 2 * 5 + 1 ≡ 11
// assert ⊢ succ_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xO (xO xH))); 
// assert ⊢ succ_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xI (xO xH))); 

symbol pred_double ≔
  integer_rect (λ _, int) (Zneg xH)
               (λ p, Zpos (pos_pred_double p))
               (λ p, Zneg (xI p));

// Check that 2 * (-5) - 1 ≡ -11 and that 2 * 5 - 1 ≡ 9
// assert ⊢ pred_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xI (xO xH))); 
// assert ⊢ pred_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xO (xO xH))); 



symbol succ : integer → integer;

builtin "0"  ≔  zero;
builtin "+1" ≔  succ;

symbol infixspls : integer → integer → Type;
symbol infixspgt : integer → integer → Type;
symbol infixsplseq : integer → integer → Type;
symbol infixspgteq : integer → integer → Type;

symbol infixsppl : integer → integer → integer;
symbol infixspas : integer → integer → integer;
symbol infixspmn : integer → integer → integer;

symbol prefixspmn : integer → integer;


// Booleans

symbol bool : Type;

symbol True : tEv bool;
symbol False : tEv bool;


// Define sequents : the sequent <A, B ⊢ C, D> is represented by <A → B → ¬ C → ¬ D → false>.

symbol empty : Type
≔  false;

symbol hyp : Type → Type → Type
≔  λ A s, A ↝ s;

symbol goal : Type → Type → Type
≔  λ A s, ¬ A ↝ s;



// Excluded-middle axiom and reasoning about negation.

symbol nni : Π A, tEv A → tEv (¬ ¬ A)
≔  λ A a na, na a;

symbol contra : Π A B, (tEv A → tEv B) → tEv (¬ B) → tEv (¬ A)
≔  λ A B p nb a, nb (p a);

symbol em : tEv (forall (λ A, A ∨ ¬ A));

symbol nne : Π A, tEv (¬ ¬ A) → tEv A
≔  λ A nna, em A A (λ a, a) (λ na, nna na A);



// Theorems

// Implication

symbol imp_elim : Π A B, tEv (A ↝ B) → tEv A → tEv B
≔  λ A B p, p;

symbol imp_intro : Π A B, (tEv A → tEv B) → tEv (A ↝ B)
≔  λ A B p, p;

// Disjunction

symbol or_intro_1 : Π A B, tEv A → tEv (A ∨ B)
≔  λ A B (a : tEv A) C (ac: tEv A → tEv C) _, ac a;

symbol or_intro_2 : Π A B, tEv B → tEv (A ∨ B)
≔  λ A B (b : tEv B) C _ (bc: tEv B → tEv C), bc b;

symbol or_elim : Π A B, tEv (A ∨ B) → Π C, tEv (A ↝ C) → tEv (B ↝ C) → tEv C
≔  λ A B ab, ab;

// Conjunction

symbol and_intro : Π A B, tEv A → tEv B → tEv (A ∧ B)
≔  λ A B a b C (p : tEv A → tEv B → tEv C), p a b;

symbol and_elim_1 : Π A B, tEv (A ∧ B) → tEv A
≔  λ A B (ab : tEv (A ∧ B)), ab A (λ a _, a);

symbol and_elim_2 : Π A B, tEv (A ∧ B) → tEv B
≔  λ A B (ab : tEv (A ∧ B)), ab B (λ _ b, b);

// Universal quantifier

symbol forall_intro : Π P, (Π t, tEv (P t)) → tEv (forall P)
≔  λ P p, p;

symbol forall_elim : Π P t, tEv (forall P) → tEv (P t)
≔  λ P t p, p t;

// Existential quantifier

symbol exists_intro : Π T P t, tEv (P t) → tEv (∃ T P)
≔  λ T P t pt C (q : Π x, tEv (P x) → tEv C), q t pt;

symbol exists_elim : Π T P Q, tEv (∃ T P) →  (Π x, tEv (P x ↝ Q)) → tEv Q
≔  λ T P Q e pq, e Q pq;

// Equality

symbol eq_refl : Π T x, tEv (infixspeq T x x)
≔  λ T x P px, px;

symbol eq_sym : Π T x y, tEv (infixspeq T x y) → tEv (infixspeq T y x)
≔  λ T x y eqxy, eqxy (λ t, infixspeq T t x) (eq_refl T x);

symbol eq_trans : Π T x y z, tEv (infixspeq T x y) → tEv (infixspeq T y z) → tEv (infixspeq T x z)
≔  λ T x y z eqxy eqyz, eqyz (λ t, infixspeq T x t) eqxy;



// Certificate lines

symbol hole :
  tEv empty →
  tEv empty
≔  λ f, f;

symbol axiom : Π A,
  tEv (hyp A (goal A empty))
≔  λ A a na, na a;

symbol trivial_hyp :
  tEv (hyp false empty)
≔  λ f, f;

symbol trivial_goal :
  tEv (goal true empty)
≔  λ ntt, ntt tt;

symbol eqrefl : Π T t,
  tEv (goal (infixspeq T t t) empty)
≔  λ T t neqtt, neqtt (eq_refl T t);

symbol cut : Π A,
  tEv (goal A empty) →
  tEv (hyp A empty) →
  tEv empty
≔  λ A nna na, nna na;

symbol split_hyp : Π A B,
  tEv (hyp A empty) →
  tEv (hyp B empty) →
  tEv (hyp (A ∨ B) empty)
≔  λ A B s1 s2 ab, or_elim A B ab false s1 s2;

symbol split_goal : Π A B,
    tEv (goal A empty) →
    tEv (goal B empty) →
    tEv (goal (A ∧ B) empty)
≔  λ A B nna nnb, nni (A ∧ B) (and_intro A B (nne A nna) (nne B nnb));

symbol unfold_iff_hyp : Π A B,
    tEv (hyp ((A ↝ B) ∧ (B ↝ A)) empty) →
    tEv (hyp (A ⇔ B) empty)
≔  λ A B s, s;

symbol unfold_iff_goal : Π A B,
    tEv (goal ((A ↝ B) ∧ (B ↝ A)) empty) →
    tEv (goal (A ⇔ B) empty)
≔  λ A B s, s;

symbol unfold_arr_hyp : Π A B,
    tEv (hyp (¬ A ∨ B) empty) →
    tEv (hyp (A ↝ B) empty)
≔  λ A B s impab,
   s (em A (¬ A ∨ B) (λ a, or_intro_2 (¬ A) B (impab a))
     	      	     (λ na, or_intro_1 (¬ A) B na));

symbol unfold_arr_goal : Π A B,
    tEv (goal (¬ A ∨ B) empty) →
    tEv (goal (A ↝ B) empty)
≔  λ A B s, nni (A ↝ B) (λ a,
      nne (¬ A ∨ B) s B (λ na, na a B)
                        (λ b, b));

symbol swap_neg_hyp : Π A,
    tEv (goal A empty) →
    tEv (hyp (¬ A) empty)
≔  λ A s, s;

symbol swap_hyp : Π A,
    tEv (goal (¬ A) empty) →
    tEv (hyp A empty)
≔  λ A nnna, nne (¬ A) nnna;

symbol swap_goal : Π A,
    tEv (hyp (¬ A) empty) →
    tEv (goal A empty)
≔  λ A s, s;

symbol swap_neg_goal : Π A,
    tEv (hyp A empty) →
    tEv (goal (¬ A) empty)
≔  λ A na, nni (¬ A) na;

symbol destruct_hyp : Π A B,
    tEv (hyp A (hyp B empty)) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B s ab,
   s (and_elim_1 A B ab) (and_elim_2 A B ab);

symbol destruct_goal : Π A B,
    tEv (goal A (goal B empty)) →
    tEv (goal (A ∨ B) empty)
≔  λ A B s nab, s (λ a, nab (or_intro_1 A B a))
                  (λ b, nab (or_intro_2 A B b));

symbol construct_goal : Π A B,
    tEv (goal (A ∨ B) empty) →
    tEv (goal A (goal B empty))
≔  λ A B s na nb, or_elim A B (nne (A ∨ B) s) false na nb;

symbol dir_left_hyp : Π A B,
    tEv (hyp A empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B na ab, na (and_elim_1 A B ab);

symbol dir_left_goal : Π A B,
    tEv (goal A empty) →
    tEv (goal (A ∨ B) empty)
≔  λ A B nna nab, nab (or_intro_1 A B (nne A nna));

symbol dir_right_hyp : Π A B,
    tEv (hyp B empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ A B nb ab, nb (and_elim_2 A B ab);

symbol dir_right_goal : Π A B,
    tEv (goal B empty) →
    tEv (goal (A ∨ B) empty)
≔  λ A B nnb nab, nab (or_intro_2 A B (nne B nnb));

symbol clearhyp : Π A,
    tEv empty →
    tEv (hyp A empty)
≔  λ A f _, f;

symbol clear_hyp A HA s ≔  clearhyp A s HA;

symbol cleargoal : Π A,
    tEv empty →
    tEv (goal A empty)
≔  λ A f _, f;

symbol clear_goal A HA s ≔  cleargoal A s HA;

symbol forget :
    tEv empty →
    tEv empty
≔  λ f, f;

symbol intro_quant_hyp : Π (T : Type) (P : kEv (T ⇀ DType)),
    (Π (y : tEv T), tEv (hyp (P y) empty)) →
    tEv (hyp (∃ T P) empty)
≔  λ T P s ep, exists_elim T P false ep s;

symbol intro_quant_goal : Π T P,
    (Π (y : tEv T), tEv (goal (P y) empty)) →
    tEv (goal (∀ T P) empty)
≔  λ T P s nfp, nfp (λ t, nne (P t) (s t));

symbol inst_quant_goal : Π T P t,
    tEv (goal (∃ T P) (goal (P t) empty)) →
    tEv (goal (∃ T P) empty)
≔  λ T P t s nep, s nep (λ pt, nep (exists_intro T P t pt));

symbol inst_quant_hyp : Π T P t,
    tEv (hyp (∀ T (λ x, P x)) (hyp (P t) empty)) →
    tEv (hyp (∀ T (λ x, P x)) empty)
≔  λ T P t s h, s h (h t);

symbol rewrite_hyp : Π T a b P,
   tEv (hyp (infixspeq T a b) (hyp (P b) empty)) →
   tEv (hyp (infixspeq T a b) (hyp (P a) empty))
≔  λ T a b P s h i, s h (h P i);

symbol rewrite_goal : Π T a b P,
   tEv (hyp (infixspeq T a b) (goal (P b) empty)) →
   tEv (hyp (infixspeq T a b) (goal (P a) empty))
≔  λ T a b P s h i, s h (h (λ x, ¬ P x) i);

symbol rewrite_fmla_hyp : Π A B P,
   tEv (hyp (eq_fmla A B) (hyp (P B) empty)) →
   tEv (hyp (eq_fmla A B) (hyp (P A) empty))
≔  λ A B P s h i, s h (h P i);

symbol rewrite_fmla_goal : Π A B P,
   tEv (hyp (eq_fmla A B) (goal (P B) empty)) →
   tEv (hyp (eq_fmla A B) (goal (P A) empty))
≔  λ A B P s h i, s h (h (λ x, ¬ P x) i);

symbol iffeq : Π (A : Type) (B : Type),
	   	   tEv (hyp (eq_fmla A B) empty) →
		   tEv (hyp (A ⇔ B) empty)
≔  λ A B s eab, s (iff_eq A B eab);

symbol strong_induction : Π a P,
   (Π x, tEv (hyp (infixsplseq x a) (goal (P x) empty))) →
   (Π x, tEv (hyp (infixspls a x) (hyp (∀ int (λ n, infixspls n x ↝ P n)) (goal (P x) empty)))) →
   Π x, tEv (goal (P x) empty);

