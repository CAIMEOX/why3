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


symbol eq T (x y : tEv T) ≔  ktPi (T ⇀ DType)
       	       	       	     	  (λ P, P x ↝ P y);
symbol infixspeq ≔ eq;

symbol eq_fmla A B ≔  ktPi (kkPi DType (λ _, DType))
		           (λ P, P A ↝ P B);

symbol ⇔ A B ≔  (A ↝ B) ∧ (B ↝ A);
notation ⇔ infix right 14;

symbol iff_eq : Π (A : Type) (B : Type),
       	        tEv (A ⇔  B) →
		tEv (eq_fmla A B);

// Booleans

symbol bool : Type;
symbol boolean ≔ tEv bool;

symbol True : boolean;
symbol False : boolean;

symbol bool_rect :
  tEv (ktPi (bool ⇀ DType) (λ Q,
       Q True ↝
       Q False ↝
       ∀ bool (λ b, Q b)));

rule bool_rect _ $vT _   True  ↪ $vT;
rule bool_rect _ _   $vF False ↪ $vF;

symbol if a b t e ≔
  bool_rect (λ _, a) t e b;

// symbol bool_ind :  Π (Q : boolean → TYPE),
//   Q True →
//   Q False →
//   Π b, Q b;
// symbol is_True ≔
//   bool_ind (λ _, Type)
//       true
//       false;

symbol is_True b ≔
  eq bool b True;

// Comparison

symbol comp : Type;
symbol comparison ≔ tEv comp;

symbol Eq : comparison;
symbol Lt : comparison;
symbol Gt : comparison;

symbol comp_rect :
  tEv (ktPi (comp ⇀ DType) (λ Q,
       Q Eq ↝
       Q Lt ↝
       Q Gt ↝
       ∀ comp (λ c, Q c)));

rule comp_rect _ $vE _   _   Eq  ↪ $vE;
rule comp_rect _ _   $vL _   Lt  ↪ $vL;
rule comp_rect _ _   _   $vG Gt  ↪ $vG;

// Integers

symbol pos : Type;
symbol positive ≔ tEv pos;

symbol xI : positive → positive;
symbol xO : positive → positive;
symbol xH : positive;

symbol pos_rect :
  tEv (ktPi (pos ⇀ DType) (λ Q,
       (∀ pos (λ p, Q p ↝ Q (xI p))) ↝
       (∀ pos (λ p, Q p ↝ Q (xO p))) ↝
       Q xH ↝
       ∀ pos (λ p, Q p)));

// symbol pos_rect :  Π (Q : positive → Type),
//   (Π p, tEv (Q p) → tEv (Q (xI p))) →
//   (Π p, tEv (Q p) → tEv (Q (xO p))) →
//   tEv (Q xH) →
//   Π p, tEv (Q p);

rule pos_rect _  _   _   $vH xH      ↪ $vH;
rule pos_rect $Q $vI $vO $vH (xI $p) ↪ $vI $p (pos_rect $Q $vI $vO $vH $p);
rule pos_rect $Q $vI $vO $vH (xO $p) ↪ $vO $p (pos_rect $Q $vI $vO $vH $p);

symbol pos_succ ≔
  pos_rect (λ _, pos)
    (λ _ succ_p, xO succ_p)
    (λ p _, xI p)
    (xO xH);

symbol pos_add_carry  ≔
  pos_rect (λ _, pos ⇁ bool ⇁ pos)
    (λ p ac_p y b, pos_rect (λ _, pos)
       (λ q _, if pos b
               (xI (ac_p q True))
               (xO (ac_p q True)))
       (λ q _, if pos b
               (xO (ac_p q True))
               (xI (ac_p q False)))
       (if pos b
        (xI (pos_succ p))
        (xO (pos_succ p)))
       y)
    (λ p ac_p y b, pos_rect (λ _, pos)
       (λ q _, if pos b
               (xO (ac_p q True))
               (xI (ac_p q False)))
       (λ q _, if pos b
               (xI (ac_p q False))
               (xO (ac_p q False)))
       (if pos b
        (xO (pos_succ p))
        (xI p))
       y)
    (λ y b, pos_rect (λ _, pos)
       (λ q _, if pos b
               (xI (pos_succ q))
               (xO (pos_succ q)))
       (λ q _, if pos b
               (xO (pos_succ q))
               (xI q))
       (if pos b
        (xI xH)
        (xO xH))
       y);

symbol pos_add x y ≔ pos_add_carry x y False;

// Check that 7 + 5 = 12
// assert ⊢ pos_add (xI (xI xH)) (xI (xO xH)) ≡ xO (xO (xI xH));

// Check that 110101010 + 101101100 ≡ 1100010110 in base 2 (426 + 364 ≡ 790)
// assert ⊢ pos_add (xO (xI (xO (xI (xO (xI (xO (xI xH)))))))) (xO (xO (xI (xI (xO (xI (xI (xO xH)))))))) ≡ (xO (xI (xI (xO (xI (xO (xO (xO (xI xH)))))))));

symbol pos_mul x y ≔
  pos_rect (λ _, pos)
     (λ _ mul_p_y, pos_add y (xO mul_p_y))
     (λ _ mul_p_y, xO mul_p_y)
     y
     x;

// Check that 6 * 5 = 30
// assert ⊢ pos_mul (xO (xI xH)) (xI (xO xH)) ≡ xO (xI (xI (xI xH)));

     
symbol pos_pred_double ≔
  pos_rect (λ _, pos)
     (λ p _, xI (xO p))
     (λ _ pos_pred_double_p, xI pos_pred_double_p)
     xH;

// Check that 2 * 6 - 1 ≡ 11
// assert ⊢ pos_pred_double (xO (xI xH)) ≡ xI (xI (xO xH)); 

symbol pos_compare_acc ≔
  pos_rect (λ _, comp ⇁ pos ⇁ comp)
     (λ _ comp_p r, pos_rect (λ _, comp)
        (λ q _, comp_p r q)
        (λ q _, comp_p Gt q)
        Gt)
     (λ _ comp_p r, pos_rect (λ _, comp)
        (λ q _, comp_p Lt q)
        (λ q _, comp_p r q)
        Gt)
     (λ r, pos_rect (λ _, comp)
        (λ _ _, Lt)
        (λ _ _, Lt)
        r);

symbol pos_compare x y ≔ pos_compare_acc x Eq y;

symbol int : Type;
symbol integer ≔ tEv int;

symbol Z0 : integer;
symbol Zpos : positive → integer;
symbol Zneg : positive → integer;

symbol int_rect :
  tEv (ktPi (int ⇀ DType) (λ Q,
       Q Z0 ↝
       (∀ pos (λ p, Q (Zpos p))) ↝
       (∀ pos (λ p, Q (Zneg p))) ↝
       ∀ int (λ z, Q z)));

rule int_rect _ $v0 _     _     Z0        ↪ $v0;
rule int_rect _ _   $vpos _     (Zpos $x) ↪ $vpos $x;
rule int_rect _ _   _     $vneg (Zneg $x) ↪ $vneg $x;

symbol zero ≔ Z0;
symbol one ≔ Zpos xH;

symbol double ≔
  int_rect (λ _, int)
    zero
    (λ p, Zpos (xO p))
    (λ p, Zneg (xO p));

// Check that 2 * 7 ≡ 14
// assert ⊢ double (Zpos (xI (xI xH))) ≡ Zpos (xO (xI (xI xH))); 

symbol succ_double ≔
  int_rect (λ _, int)
    one
    (λ p, Zpos (xI p))
    (λ p, Zneg (pos_pred_double p));

// Check that 2 * (-5) + 1 ≡ -9 and that 2 * 5 + 1 ≡ 11
// assert ⊢ succ_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xO (xO xH))); 
// assert ⊢ succ_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xI (xO xH))); 

symbol pred_double ≔
  int_rect (λ _, int)
    (Zneg xH)
    (λ p, Zpos (pos_pred_double p))
    (λ p, Zneg (xI p));

// Check that 2 * (-5) - 1 ≡ -11 and that 2 * 5 - 1 ≡ 9
// assert ⊢ pred_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xI (xO xH))); 
// assert ⊢ pred_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xO (xO xH))); 

symbol pos_sub ≔
  pos_rect (λ _, pos ⇁ int)
     (λ p pos_sub_p, pos_rect (λ _, int)
        (λ q _, double (pos_sub_p q))
        (λ q _, succ_double (pos_sub_p q))
        (Zpos (xO p)))
     (λ p pos_sub_p, pos_rect (λ _, int)
        (λ q _, pred_double (pos_sub_p q))
        (λ q _, double (pos_sub_p q))
        (Zpos (pos_pred_double p)))
     (pos_rect (λ _, int)
        (λ q _, Zneg (xO q))
        (λ q _, Zneg (pos_pred_double q))
        zero);

// Check that 3 - 5 ≡ -2
// Check that 3 - 4 ≡ -1
// Check that 3 - 1 ≡ 2
// assert ⊢ pos_sub (xI xH) (xI (xO xH)) ≡ Zneg (xO xH);
// assert ⊢ pos_sub (xI xH) (xO (xO xH)) ≡ Zneg xH;
// assert ⊢ pos_sub (xI xH) xH ≡ Zpos (xO xH);
// Check that 4 - 3 ≡ 1
// Check that 4 - 6 ≡ -2
// Check that 4 - 1 ≡ 3
// assert ⊢ pos_sub (xO (xO xH)) (xI xH) ≡ Zpos xH;
// assert ⊢ pos_sub (xO (xO xH)) (xO (xI xH)) ≡ Zneg (xO xH);
// assert ⊢ pos_sub (xO (xO xH)) xH ≡ Zpos (xI xH);
// Check that 1 - 5 ≡ -4
// Check that 1 - 2 ≡ -1
// Check that 1 - 1 ≡ 0
// assert ⊢ pos_sub xH (xI (xO xH)) ≡ Zneg (xO (xO xH));
// assert ⊢ pos_sub xH (xO xH) ≡ Zneg xH;
// assert ⊢ pos_sub xH xH ≡ Z0;


symbol add x y ≔
  int_rect (λ _, int)
    y
    (λ x', int_rect (λ _, int)
       x
       (λ y', Zpos (pos_add x' y'))
       (λ y', pos_sub x' y')
       y)
    (λ x', int_rect (λ _, int)
       x
       (λ y', pos_sub y' x')
       (λ y', Zneg (pos_add x' y'))
       y)
    x;

symbol opp ≔
  int_rect (λ _, int)
     zero
     (λ x, Zneg x)
     (λ x, Zpos x);

symbol succ x ≔ add x one;

symbol sub x y ≔ add x (opp y);

symbol mul x y ≔
  int_rect (λ _, int)
     zero
     (λ x', int_rect (λ _, int)
        zero
        (λ y', Zpos (pos_mul x' y'))
        (λ y', Zneg (pos_mul x' y'))
        y)
     (λ x', int_rect (λ _, int)
        zero
        (λ y', Zneg (pos_mul x' y'))
        (λ y', Zpos (pos_mul x' y'))
        y)
     x;

symbol compare x y ≔
  int_rect (λ _, comp)
     (int_rect (λ _, comp)
         Eq
         (λ _, Lt)
         (λ _, Gt)
         y)
     (λ x', int_rect (λ _, comp)
        Gt
        (λ y', pos_compare x' y')
        (λ _, Gt)
        y)
     (λ x', int_rect (λ _, comp)
        Lt
        (λ _, Lt)
        (λ y', pos_compare y' x')
        y)
     x;

symbol leb x y ≔
  comp_rect (λ _, bool)
      True
      True
      False
      (compare x y);

symbol ltb x y ≔
  comp_rect (λ _, bool)
      False
      True
      False
      (compare x y);

symbol geb x y ≔
  comp_rect (λ _, bool)
      True
      False
      True
      (compare x y);

symbol gtb x y ≔
  comp_rect (λ _, bool)
      False
      False
      True
      (compare x y);

builtin "0"  ≔  zero;
builtin "+1" ≔  succ;

symbol infixsppl ≔ add;
symbol infixspas ≔ mul;
symbol infixspmn ≔ sub;
symbol prefixspmn ≔ opp;

symbol infixspls x y ≔ is_True (ltb x y);
symbol infixspgt x y ≔ is_True (gtb x y);
symbol infixsplseq x y ≔ is_True (leb x y);
symbol infixspgteq x y ≔ is_True (geb x y);




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



symbol emb : Π b, tEv (eq bool b True ∨ eq bool b False) ≔
  bool_rect (λ b, eq bool b True ∨ eq bool b False)
      (λ C f1 _, f1 (eq_refl bool True))
      (λ C _ f2, f2 (eq_refl bool False));
