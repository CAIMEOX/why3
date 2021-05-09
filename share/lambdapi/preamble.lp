

// COC ENCODING


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

rule tEv (ttPi $x $y) ↪  Π (w : tEv $x), tEv ($y w)
with kEv (tkPi $x $y) ↪  Π (w : tEv $x), kEv ($y w)
with tEv (ktPi $x $y) ↪  Π (w : kEv $x), tEv ($y w)
with kEv (kkPi $x $y) ↪  Π (w : kEv $x), kEv ($y w);

// Improve quantification notations

symbol ∀ {A} ≔ ttPi A;
notation ∀ quantifier;

symbol π {A} ≔ ktPi A;
notation π quantifier;

symbol ↝ A B ≔  tkPi A (λ _, B);
notation ↝ infix right 14;

symbol ⇒ A B ≔  ttPi A (λ _, B);
notation ⇒ infix right 14;

// Help the unification algorithm so that we can use the shallow types
// inside the deep terms

unif_rule Type ≡ kEv $t ↪ [ $t ≡ DType ];
unif_rule tEv $a ≡ tEv $b ↪ [ $a ≡ $b ];
unif_rule kEv $a ≡ kEv $b ↪ [ $a ≡ $b ];
unif_rule $a → $b ≡ kEv $c ↪ [ $a ≡ tEv $a'; $b ≡ kEv $b'; $c ≡ $a' ↝ $b' ];
unif_rule $a → $b ≡ tEv $c ↪ [ $a ≡ tEv $a'; $b ≡ tEv $b'; $c ≡ $a' ⇒ $b' ];

// To use the inductive notation

builtin "Prop" ≔ Type;
builtin "P" ≔ tEv;

// Define our higher order logic

symbol false ≔ `π C : Type, C;

symbol true ≔ false ⇒ false;

symbol tt : tEv true ≔ λ x, x;

symbol ¬ A ≔ A ⇒ false;
notation ¬ prefix 20;

symbol ∧ A B ≔ `π C, (A ⇒ B ⇒ C) ⇒ C;
notation ∧ infix right 18;

symbol ∨ A B ≔ `π C, (A ⇒ C) ⇒ (B ⇒ C) ⇒ C;
notation ∨ infix right 16;

symbol ⇔ A B ≔ (A ⇒ B) ∧ (B ⇒ A);
notation ⇔ infix right 14;

symbol ∃ {T} P ≔ `π C, (`∀ x : tEv T, P x ⇒ C) ⇒  C;
notation ∃ quantifier;

// Excluded-middle axiom

symbol em : tEv (`π A, A ∨ ¬ A);


// THEOREMS


//  Reasoning about negation.

symbol nni A : tEv A → tEv (¬ ¬ A)
≔  λ a na, na a;

symbol contra A B : (tEv A → tEv B) → tEv (¬ B) → tEv (¬ A)
≔  λ p nb a, nb (p a);

symbol nne A : tEv (¬ ¬ A) → tEv A
≔  λ nna, em A A (λ a, a) (λ na, nna na A);

// Implication

symbol imp_elim A B : tEv (A ⇒ B) → tEv A → tEv B
≔  λ p, p;

symbol imp_intro A B : (tEv A → tEv B) → tEv (A ⇒ B)
≔  λ p, p;

// Disjunction

symbol or_intro_1 A B : tEv A → tEv (A ∨ B)
≔  λ (a : tEv A) C (ac: tEv A → tEv C) _, ac a;

symbol or_intro_2 A B : tEv B → tEv (A ∨ B)
≔  λ (b : tEv B) C _ (bc: tEv B → tEv C), bc b;

symbol or_elim A B : tEv (A ∨ B) → Π C, tEv (A ⇒ C) → tEv (B ⇒ C) → tEv C
≔  λ ab, ab;

// Conjunction

symbol and_intro A B : tEv A → tEv B → tEv (A ∧ B)
≔  λ a b C (p : tEv A → tEv B → tEv C), p a b;

symbol and_elim_1 A B : tEv (A ∧ B) → tEv A
≔  λ (ab : tEv (A ∧ B)), ab A (λ a _, a);

symbol and_elim_2 A B : tEv (A ∧ B) → tEv B
≔  λ (ab : tEv (A ∧ B)), ab B (λ _ b, b);

// Universal quantifier

symbol forall_intro T : Π P, (Π t : tEv T, tEv (P t)) → tEv (`∀ x, P x)
≔  λ P p, p;

symbol forall_elim T : Π P (t : tEv T), tEv (`∀ x, P x) → tEv (P t)
≔  λ P t p, p t;

// Existential quantifier

symbol exists_intro T : Π P (t : tEv T), tEv (P t) → tEv (`∃ x, P x)
≔  λ P t pt C q, q t pt;

symbol exists_elim T : Π P Q, tEv (`∃ x, P x) → (Π x, tEv (P x ⇒ Q)) → tEv Q
≔  λ (P : tEv T → Type) Q e pq, e Q pq;

// Equality

symbol eq T (x y : tEv T) ≔ `π P, P x ⇒ P y;

// TODO : explain why we need another axiom
symbol eq_fmla A B ≔ ktPi (kkPi DType (λ _, DType))
		          (λ P, P A ⇒ P B);

symbol iff_eq : Π (A : Type) (B : Type),
       	        tEv (A ⇔ B) →
		tEv (eq_fmla A B);

symbol eq_refl {T} x : tEv (eq T x x)
≔  λ P px, px;

symbol eq_sym {T} x y : tEv (eq T x y) → tEv (eq T y x)
≔  λ eqxy, eqxy (λ t, eq T t x) (eq_refl x);

symbol eq_trans {T} x y z: tEv (eq T x y) → tEv (eq T y z) → tEv (eq T x z)
≔  λ eqxy eqyz, eqyz (λ t, eq T x t) eqxy;

symbol eq_ind T x y : tEv (eq T x y) → Π P, tEv (P y) → tEv (P x)
≔ λ eq, eq_sym x y eq;

// symbol exists (T : Kind) (P : kEv T → Type)  ≔
// `π C, (`π x : kEv T, P x ⇒ C) ⇒ C;

// opaque symbol eq_and_def :
//   tEv (exists (kkPi DType (λ T, T ↝ T ↝ DType)) (λ eq,
//        @π DType (λ C : Type,
//           ((`π T : Type, `∀ x : tEv T, eq T x x) ⇒
//            (`π T : Type, (`∀ x : tEv T, (`∀ y : tEv T, eq T x y ⇒
//               (`π P : tEv T → Type, P y ⇒ P x)))) ⇒ C) ⇒ C)
//       ))
// ≔ begin
//   assume C_ex p_ex;
//   refine p_ex eq _;
//   assume C_and p_and;
//   refine p_and eq_refl eq_ind;
// end;

// TODO : remove opaque and prove =_refl and =_ind
opaque symbol = {T}: tEv T → tEv T → Type ≔ @eq T;
notation = infix 22;

symbol =_refl T (x : tEv T) : tEv (x = x);

// TODO : why do we need =_ind to rewrite sometimes ?
symbol =_ind {T} (x y : tEv T) : tEv (x = y) → Π P, tEv (P y) → tEv (P x);

builtin "T"     ≔ tEv;
builtin "eq"    ≔ =;
builtin "refl"  ≔ =_refl;
builtin "eqind" ≔ =_ind;

symbol f_equal {T1 T2} (a b : tEv T1) (f : tEv T1 → tEv T2) :
  tEv (a = b ⇒ f a = f b)
≔ begin
  assume T1 T2 a b f eq;
  rewrite eq;
  reflexivity;
end;

// THEORIES


// Booleans

inductive boolean : TYPE ≔
| True : boolean
| False : boolean;

symbol Dboolean : Type;
rule tEv Dboolean ↪ boolean;
unif_rule boolean ≡ tEv $t ↪ [ $t ≡ Dboolean ];

// symbol True : boolean;
// symbol False : boolean;

// symbol bool_ind :
//   tEv (`π Q,
//        Q True ⇒
//        Q False ⇒
//        `∀ b : boolean, Q b) ≔ ind_boolean;

// rule bool_ind _ $vT _   True  ↪ $vT
// with bool_ind _ _   $vF False ↪ $vF;

symbol if (a : Type) b t e ≔
  ind_boolean (λ _, a) t e b;

// TODO : how to do with only the inductive definition ?
symbol bool_rect :
  Π (Q : boolean → Kind),
  kEv (Q True) →
  kEv (Q False) →
  Π b, kEv(Q b);

rule bool_rect _ $vT _   True  ↪ $vT
with bool_rect _ _   $vF False ↪ $vF;

symbol is_True ≔
  bool_rect (λ _, DType)
      true
      false;

symbol discr_False_True : tEv (¬ (False = True))
≔ begin
  assume H;
  have f : tEv (is_True False);
  rewrite H; refine tt;
  // TODO : why do we need to provide false here ?
  refine f false;
end;

symbol eq_True_is_True b : tEv (b = True ⇒ is_True b)
≔ begin
  induction;
  assume _; refine tt;
  assume f; refine discr_False_True f false;
end;

// Comparison

inductive comparison : TYPE ≔
| Eq : comparison
| Lt : comparison
| Gt : comparison;

symbol Dcomparison : Type;
rule tEv Dcomparison ↪ comparison;
unif_rule comparison ≡ tEv $t ↪ [ $t ≡ Dcomparison ];

// symbol Dcomparison : Type;
// symbol comparison ≔ tEv Dcomparison;

// symbol Eq : comparison;
// symbol Lt : comparison;
// symbol Gt : comparison;

symbol comp_ind :
  tEv (`π Q : comparison → Type,
       Q Eq ⇒
       Q Lt ⇒
       Q Gt ⇒
       `∀ c : comparison, Q c) ≔ ind_comparison;

// rule comp_ind _ $vE _   _   Eq  ↪ $vE
// with comp_ind _ _   $vL _   Lt  ↪ $vL
// with comp_ind _ _   _   $vG Gt  ↪ $vG;

symbol comp_rect :
  Π Q : comparison → Kind,
  kEv (Q Eq) →
  kEv (Q Lt) →
  kEv (Q Gt) →
  Π c, kEv (Q c);

rule comp_rect _ $vE _   _   Eq  ↪ $vE
with comp_rect _ _   $vL _   Lt  ↪ $vL
with comp_rect _ _   _   $vG Gt  ↪ $vG;

symbol is_Eq ≔ comp_rect (λ _, DType) true false false;

symbol discr_Lt_Eq : tEv (¬ (Lt = Eq))
≔ begin
  assume H;
  have f : tEv (is_Eq Lt);
  rewrite H; refine tt;
  refine f false;
end;

symbol discr_Gt_Eq : tEv (¬ (Gt = Eq))
≔ begin
  assume H;
  have f : tEv (is_Eq Gt);
  rewrite H; refine tt;
  refine f false;
end;

symbol is_Lt ≔ comp_rect (λ _, DType) false true false;
symbol discr_Gt_Lt : tEv (¬ (Gt = Lt))
≔ begin
  assume H;
  have f : tEv (is_Lt Gt);
  rewrite H; refine tt;
  refine f false;
end;

symbol CompOpp : comparison → comparison ≔
  ind_comparison (λ _, Dcomparison)
     Eq
     Gt
     Lt;

symbol compopp_idem c : tEv (CompOpp (CompOpp c) = c)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Positives

inductive positive : TYPE ≔
| xI : positive → positive
| xO : positive → positive
| xH : positive;

symbol Dpositive : Type;
rule tEv Dpositive ↪ positive;
unif_rule positive ≡ tEv $t ↪ [ $t ≡ Dpositive ];

// symbol Dpositive : Type;
// symbol positive ≔ tEv Dpositive;

// symbol xI : positive → positive;
// symbol xO : positive → positive;
// symbol xH : positive;

symbol pos_ind :
  tEv (`π Q : positive → Type,
       (`∀ p : positive, Q p ⇒ Q (xI p)) ⇒
       (`∀ p : positive, Q p ⇒ Q (xO p)) ⇒
       Q xH ⇒
       `∀ p : positive, Q p) ≔ ind_positive;

// rule pos_ind _  _   _   $vH xH      ↪ $vH
// with pos_ind $Q $vI $vO $vH (xI $p) ↪ $vI $p (pos_ind $Q $vI $vO $vH $p)
// with pos_ind $Q $vI $vO $vH (xO $p) ↪ $vO $p (pos_ind $Q $vI $vO $vH $p);

symbol pos_succ ≔
  pos_ind (λ _, Dpositive)
    (λ _ succ_p, xO succ_p)
    (λ p _, xI p)
    (xO xH);

// TODO : how to unfold a definition ?
opaque symbol pos_succ_xI p : tEv (pos_succ (xI p) = xO (pos_succ p))
≔ begin assume p; reflexivity; end;

opaque symbol pos_succ_xO p : tEv (pos_succ (xO p) = xI p)
≔ begin assume p; reflexivity; end;

opaque symbol pos_succ_xH : tEv (pos_succ xH = xO xH)
≔ begin reflexivity; end;

symbol pos_peano_ind :
   tEv (`π Q : positive → Type,
        Q xH ⇒
        (`∀ p, Q p ⇒ Q (pos_succ p)) ⇒
        `∀ p, Q p)
≔ begin
  assume Q qH qS p;

  refine pos_ind (λ p, `π P, P xH ⇒ (`∀ x, P x ⇒ P (pos_succ x)) ⇒ P p)
                 _ _ _ p Q qH qS;
  assume q rec_q P pH pS;
  rewrite left (pos_succ_xO q);
  refine pS (xO q) _;
  refine rec_q (λ p, P (xO p)) (pS xH pH) _;
  assume x p2x;
  rewrite left (pos_succ_xI x);
  refine pS (pos_succ (xO x)) _;
  rewrite left (pos_succ_xO x);
  refine pS (xO x) p2x;

  assume q rec_q P pH pS;
  refine rec_q (λ p, P (xO p)) (pS xH pH) _;
  assume x p2x;
  rewrite left (pos_succ_xI x);
  refine pS (pos_succ (xO x)) _;
  rewrite left (pos_succ_xO x);
  refine pS (xO x) p2x;

  assume P pH pS;
  refine pH;
end;


symbol pos_add_carry  ≔
  pos_ind (λ _, Dpositive ⇒ Dboolean ⇒ Dpositive)
    (λ p ac_p y b, pos_ind (λ _, Dpositive)
       (λ q _, if Dpositive b
               (xI (ac_p q True))
               (xO (ac_p q True)))
       (λ q _, if Dpositive b
               (xO (ac_p q True))
               (xI (ac_p q False)))
       (if Dpositive b
        (xI (pos_succ p))
        (xO (pos_succ p)))
       y)
    (λ p ac_p y b, pos_ind (λ _, Dpositive)
       (λ q _, if Dpositive b
               (xO (ac_p q True))
               (xI (ac_p q False)))
       (λ q _, if Dpositive b
               (xI (ac_p q False))
               (xO (ac_p q False)))
       (if Dpositive b
        (xO (pos_succ p))
        (xI p))
       y)
    (λ y b, pos_ind (λ _, Dpositive)
       (λ q _, if Dpositive b
               (xI (pos_succ q))
               (xO (pos_succ q)))
       (λ q _, if Dpositive b
               (xO (pos_succ q))
               (xI q))
       (if Dpositive b
        (xI xH)
        (xO xH))
       y);



symbol pos_add x y ≔ pos_add_carry x y False;

symbol pos_add_xH y : tEv (pos_add xH y = pos_succ y)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pos_add_xH_right y : tEv (pos_add y xH = pos_succ y)
≔ begin
  refine pos_ind (λ y, pos_add y xH = pos_succ y) _ _ _;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pos_add_carry_succ x : tEv (`∀ y, pos_add_carry x y True = pos_succ (pos_add x y))
≔ begin
  // TODO : why we can't simply do 'induction' here ?
  refine pos_ind (λ x, `∀ y, pos_add_carry x y True = pos_succ (pos_add x y)) _ _ _;
  assume p prec y;
  refine pos_ind (λ y, pos_add_carry (xI p) y True = pos_succ (pos_add (xI p) y)) _ _ _ y;
  assume q _; reflexivity;
  assume q _;
  have e : tEv (pos_add_carry (xI p) (xO q) True = xO (pos_add_carry p q True));
  reflexivity; rewrite e; rewrite prec; reflexivity;
  reflexivity;
  assume p prec y;
  refine pos_ind (λ y, pos_add_carry (xO p) y True = pos_succ (pos_add (xO p) y)) _ _ _ y;
  assume q _;
  have e : tEv (pos_add_carry (xO p) (xI q) True = xO (pos_add_carry p q True));
  reflexivity; rewrite e; rewrite prec; reflexivity;
  assume q _; reflexivity;
  reflexivity;
  refine pos_ind (λ y, pos_add_carry xH y True = pos_succ (pos_add xH y)) _ _ _;
  assume y _; reflexivity;
  assume y _; reflexivity;
  reflexivity;
end;

symbol pos_add_succ x y : tEv (pos_add (pos_succ x) y = pos_succ (pos_add x y))
≔ begin
  refine pos_ind (λ x, `∀ y, pos_add (pos_succ x) y = pos_succ (pos_add x y)) _ _ _;

  assume p prec;
  refine pos_ind (λ y, pos_add (pos_succ (xI p)) y = pos_succ (pos_add (xI p) y)) _ _ _;
  assume q _;
  have e : tEv (pos_add (pos_succ (xI p)) (xI q) = xI (pos_add (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec;
  // TODO : why do we need to provide p and q here ?
  rewrite left (pos_add_carry_succ p q);
  reflexivity;
  assume q _;
  have e : tEv (pos_add (pos_succ (xI p)) (xO q) = xO (pos_add (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec; reflexivity;
  reflexivity;

  assume p prec;
  refine pos_ind (λ y, pos_add (pos_succ (xO p)) y = pos_succ (pos_add (xO p) y)) _ _ _;
  assume q _;
  have e : tEv (pos_add (pos_succ (xO p)) (xI q) = xO (pos_add_carry p q True));
  reflexivity; rewrite e;
  rewrite pos_add_carry_succ; reflexivity;
  reflexivity;
  reflexivity;

  induction;
  assume q _;
  have e : tEv (pos_add (pos_succ xH) (xI q) = xI (pos_add xH q));
  reflexivity; rewrite e;
  rewrite pos_add_xH; reflexivity;
  assume q _;
  have e : tEv (pos_add (pos_succ xH) (xO q) = xO (pos_add xH q));
  reflexivity; rewrite e;
  rewrite pos_add_xH; reflexivity;
  reflexivity;
end;

symbol pos_add_assoc x y z : tEv (pos_add (pos_add x y) z = pos_add x (pos_add y z))
≔ begin
  refine pos_peano_ind (λ x, `∀ y, `∀ z, pos_add (pos_add x y) z = pos_add x (pos_add y z)) _ _;
  assume y z;
  rewrite pos_add_xH;
  rewrite pos_add_xH;
  rewrite pos_add_succ;
  reflexivity;

  assume p prec y z;
  rewrite pos_add_succ;
  rewrite pos_add_succ;
  rewrite pos_add_succ;
  rewrite prec;
  reflexivity;
end;

symbol pos_add_succ_right x y : tEv (pos_add x (pos_succ y) = pos_succ (pos_add x y))
≔ begin
  assume x y;
  refine pos_peano_ind (λ x, pos_add x (pos_succ y) = pos_succ (pos_add x y)) _ _ x;
  rewrite pos_add_xH; rewrite pos_add_xH; reflexivity;

  assume p prec;
  rewrite pos_add_succ;
  rewrite pos_add_succ;
  rewrite prec;
  reflexivity;
end;

symbol pos_add_comm x y : tEv (pos_add x y = pos_add y x)
≔ begin
  refine pos_peano_ind (λ x, `∀ y, pos_add x y = pos_add y x) _ _;
  assume y; rewrite pos_add_xH; rewrite pos_add_xH_right;
  reflexivity;

  assume p prec y;
  rewrite pos_add_succ;
  rewrite pos_add_succ_right;
  rewrite prec;
  reflexivity;
end;


// Check that 7 + 5 = 12
// assert ⊢ pos_add (xI (xI xH)) (xI (xO xH)) ≡ xO (xO (xI xH));

// Check that 110101010 + 101101100 ≡ 1100010110 in base 2 (426 + 364 ≡ 790)
// assert ⊢ pos_add (xO (xI (xO (xI (xO (xI (xO (xI xH)))))))) (xO (xO (xI (xI (xO (xI (xI (xO xH)))))))) ≡ (xO (xI (xI (xO (xI (xO (xO (xO (xI xH)))))))));

symbol pos_mul x y ≔
  pos_ind (λ _, Dpositive)
     (λ _ mul_p_y, pos_add y (xO mul_p_y))
     (λ _ mul_p_y, xO mul_p_y)
     y
     x;

// Check that 6 * 5 = 30
// assert ⊢ pos_mul (xO (xI xH)) (xI (xO xH)) ≡ xO (xI (xI (xI xH)));

symbol pos_pred_double ≔
  pos_ind (λ _, Dpositive)
     (λ p _, xI (xO p))
     (λ _ pos_pred_double_p, xI pos_pred_double_p)
     xH;

// Check that 2 * 6 - 1 ≡ 11
// assert ⊢ pos_pred_double (xO (xI xH)) ≡ xI (xI (xO xH));

symbol pos_compare_acc : positive → comparison → positive → comparison  ≔
  pos_ind (λ _, Dcomparison ⇒ Dpositive ⇒ Dcomparison)
     (λ _ pca_p r, pos_ind (λ _, Dcomparison)
        (λ q _, pca_p r q)
        (λ q _, pca_p Gt q)
        Gt)
     (λ _ pca_p r, pos_ind (λ _, Dcomparison)
        (λ q _, pca_p Lt q)
        (λ q _, pca_p r q)
        Gt)
     (λ r, pos_ind (λ _, Dcomparison)
        (λ _ _, Lt)
        (λ _ _, Lt)
        r);

symbol pos_compare x y ≔ pos_compare_acc x Eq y;
symbol pc_def x y : tEv (pos_compare x y = pos_compare_acc x Eq y)
≔ begin assume x y; reflexivity; end;

symbol pos_compare' ≔
  pos_ind (λ _, Dpositive ⇒ Dcomparison)
     (λ _ pc'_p, pos_ind (λ _, Dcomparison)
        (λ q _, pc'_p q)
        (λ q _, comp_ind (λ _, Dcomparison)
                         Gt
                         Lt
                         Gt
                         (pc'_p q))
        Gt)
     (λ _ pc'_p, pos_ind (λ _, Dcomparison)
        (λ q _, comp_ind (λ _, Dcomparison)
                         Lt
                         Lt
                         Gt
                         (pc'_p q))
        (λ q _, pc'_p q)
        Gt)
     (pos_ind (λ _, Dcomparison)
              (λ _ _, Lt)
              (λ _ _, Lt)
              Eq);

symbol pca_comm x y r :
  tEv (pos_compare_acc x r y =
       CompOpp (pos_compare_acc y (CompOpp r) x))
≔ begin
  refine pos_ind (λ x, `∀ y, `∀ r, pos_compare_acc x r y =
       CompOpp (pos_compare_acc y (CompOpp r) x))
                 _ _ _;

  assume p Hrec y r;

  refine pos_ind (λ y, pos_compare_acc (xI p) r y =
                 CompOpp (pos_compare_acc y (CompOpp r) (xI p)))
                 _ _ _ y;
  assume q _; refine Hrec q r;
  assume q _; refine Hrec q Gt;
  reflexivity;

  assume p Hrec y r;
  refine pos_ind (λ y, pos_compare_acc (xO p) r y =
                 CompOpp (pos_compare_acc y (CompOpp r) (xO p)))
                 _ _ _ y;
  assume q _; refine Hrec q Lt;
  assume q _; refine Hrec q r;
  reflexivity;

  assume y r;
  refine pos_ind (λ y, pos_compare_acc xH r y =
                  CompOpp (pos_compare_acc y (CompOpp r) xH))
                 _ _ _ y;
  assume p _; reflexivity;
  assume p _; reflexivity;
  rewrite left [in pos_compare_acc xH r xH] (compopp_idem r);
  reflexivity;
end;

symbol pc_comm x y : tEv (pos_compare x y = CompOpp (pos_compare y x))
≔ begin
  assume x y;
  rewrite pc_def;
  rewrite pca_comm;
  reflexivity;
end;

symbol pc'_comm x y :
  tEv (pos_compare' x y = CompOpp (pos_compare' y x))
≔ begin
  refine pos_ind (λ x, `∀ y, pos_compare' x y = CompOpp (pos_compare' y x)) _ _ _;

  assume p prec;
  induction;
  // Case xI - xI
  assume q _; refine prec q;
  // Case xI - xO
  assume q _;
  have e1 : tEv (pos_compare' (xI p) (xO q) =
                 comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' p q));
  reflexivity; rewrite e1;
  have e2 : tEv (pos_compare' (xO q) (xI p) =
                 comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' q p));
  reflexivity;
  refine =_ind (pos_compare' (xO q) (xI p)) (comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' q p)) e2 (λ u, comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' p q) = CompOpp u) _;
  refine =_ind (pos_compare' p q) (CompOpp (pos_compare' q p)) (prec q)
               (λ u, comp_ind (λ _, Dcomparison) Gt Lt Gt u = CompOpp (comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' q p))) _;
  refine comp_ind (λ c, comp_ind (λ _, Dcomparison) Gt Lt Gt (CompOpp c) = CompOpp (comp_ind (λ _, Dcomparison) Lt Lt Gt c)) _ _ _ (pos_compare' q p);
  reflexivity;
  reflexivity;
  reflexivity;
  // Case xI - xH
  reflexivity;

  assume p prec;
  induction;
  // Case xO - xI
  assume q _;
  have e1 : tEv (pos_compare' (xO p) (xI q) =
                 comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' p q));
  reflexivity; rewrite e1;
  have e2 : tEv (pos_compare' (xI q) (xO p) =
                 comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' q p));
  reflexivity;
  refine =_ind (pos_compare' (xI q) (xO p)) (comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' q p)) e2 (λ u, comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' p q) = CompOpp u) _;
  refine =_ind (pos_compare' p q) (CompOpp (pos_compare' q p)) (prec q)
               (λ u, comp_ind (λ _, Dcomparison) Lt Lt Gt u = CompOpp (comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' q p))) _;
  refine comp_ind (λ c, comp_ind (λ _, Dcomparison) Lt Lt Gt (CompOpp c) = CompOpp (comp_ind (λ _, Dcomparison) Gt Lt Gt c)) _ _ _ (pos_compare' q p);
  reflexivity;
  reflexivity;
  reflexivity;
  // Case xO - xO
  assume q _; refine prec q;
  // Case xO - xH
  reflexivity;

  // Case xH -
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// assert ⊢ pos_compare xH xH ≡ Eq;
// assert ⊢ pos_compare (xI xH) xH ≡ Gt;
// assert ⊢ pos_compare (xI xH) (xO xH) ≡ Gt;

symbol discr_pc'_xI_xO x y : tEv (¬ (pos_compare' (xI x) (xO y) = Eq))
≔ begin
  assume x y;
  have e : tEv (pos_compare' (xI x) (xO y) =
                           comp_ind (λ _, Dcomparison) Gt Lt Gt
                           (pos_compare' x y));
  reflexivity;
  refine comp_ind (λ p, pos_compare' x y = p ⇒ ¬ (pos_compare' (xI x) (xO y) = Eq)) _ _ _ (pos_compare' x y) _;


  rewrite e;
  assume eq;
  refine =_ind (pos_compare' x y) Eq eq (λ u :comparison, ¬ (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq)) _;
  assume H;
  have f : tEv (is_Eq Gt);
  refine =_ind Gt Eq H (λ u, is_Eq u) _;
  refine tt;
  refine f false;

  rewrite e;
  assume eq;
  refine =_ind (pos_compare' x y) Lt eq (λ u :comparison, ¬ (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq)) _;
  assume H;
  have f : tEv (is_Eq Lt);
  refine =_ind Lt Eq H (λ u, is_Eq u) _;
  refine tt;
  refine f false;

  rewrite e;
  assume eq;
  refine =_ind (pos_compare' x y) Gt eq (λ u :comparison, ¬ (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq)) _;
  assume H;
  have f : tEv (is_Eq Gt);
  refine =_ind Gt Eq H (λ u, is_Eq u) _;
  refine tt;
  refine f false;

  reflexivity;
end;

symbol discr_pc'_xO_xI x y : tEv (¬ (pos_compare' (xO x) (xI y) = Eq))
≔ begin
  assume x y H;
  refine discr_pc'_xI_xO y x _;
  rewrite pc'_comm;
  rewrite H;
  reflexivity;
end;

symbol mod_left ≔
  comp_ind (λ _, Dpositive ⇒ Dpositive)
      (λ p, p)
      xO
      xI;

symbol mod_right ≔
  comp_ind (λ _, Dpositive ⇒ Dpositive)
      (λ p, p)
      xI
      xO;

symbol remove_mod_discr x y acc :
  tEv (¬ (pos_compare' x y = Eq) ⇒
         pos_compare' (mod_left acc x) (mod_right acc y) = pos_compare' x y)
≔ begin
  assume x y acc;
  refine comp_ind (λ c, pos_compare' x y = c ⇒ ¬ (c = Eq) ⇒ pos_compare' (mod_left acc x) (mod_right acc y) = c) _ _ _ (pos_compare' x y) _;
  assume _ f; refine f _ _; reflexivity;

  assume H _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc x) (mod_right acc y) = Lt)
                  _ _ _ acc;
  refine H;
  have e : tEv (pos_compare' (mod_left Lt x) (mod_right Lt y) =
                comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  refine =_ind (pos_compare' x y) Lt H (λ u, comp_ind (λ _, Dcomparison) Lt Lt Gt u = Lt) _;
  reflexivity;
  have e : tEv (pos_compare' (mod_left Gt x) (mod_right Gt y) =
                comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  refine =_ind (pos_compare' x y) Lt H (λ u, comp_ind (λ _, Dcomparison) Gt Lt Gt u = Lt) _;
  reflexivity;

  assume H _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc x) (mod_right acc y) = Gt)
                  _ _ _ acc;
  refine H;
  have e : tEv (pos_compare' (mod_left Lt x) (mod_right Lt y) =
                comp_ind (λ _, Dcomparison) Lt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  refine =_ind (pos_compare' x y) Gt H (λ u, comp_ind (λ _, Dcomparison) Lt Lt Gt u = Gt) _;
  reflexivity;
  have e : tEv (pos_compare' (mod_left Gt x) (mod_right Gt y) =
                comp_ind (λ _, Dcomparison) Gt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  refine =_ind (pos_compare' x y) Gt H (λ u, comp_ind (λ _, Dcomparison) Gt Lt Gt u = Gt) _;
  reflexivity;

  reflexivity;
end;


symbol remove_mod_xI_xO x y acc :
  tEv (pos_compare' (mod_left acc (xI x)) (mod_right acc (xO y)) =
       pos_compare' (xI x) (xO y))
≔ begin
  assume x y acc;
  refine remove_mod_discr (xI x) (xO y) acc _;
  refine discr_pc'_xI_xO x y;
end;

symbol remove_mod_xO_xI x y acc :
  tEv (pos_compare' (mod_left acc (xO x)) (mod_right acc (xI y)) =
       pos_compare' (xO x) (xI y))
≔ begin
  assume x y acc;
  refine remove_mod_discr (xO x) (xI y) acc _;
  refine discr_pc'_xO_xI x y;
end;


symbol pcc'_gen x y acc :
  tEv (pos_compare' (mod_left acc x) (mod_right acc y) = pos_compare_acc x acc y)
≔ begin
  refine pos_ind (λ x, `∀ y, `∀ acc, pos_compare' (mod_left acc x) (mod_right acc y) = pos_compare_acc x acc y) _ _ _;

  assume x xrec y acc;
  refine pos_ind (λ y, pos_compare' (mod_left acc (xI x)) (mod_right acc y) = pos_compare_acc (xI x) acc y) _ _ _ y;
  // xI - xI case
  assume q _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc (xI x)) (mod_right acc (xI q)) = pos_compare_acc (xI x) acc (xI q)) _ _ _ acc;
  refine xrec q Eq;
  refine xrec q Lt;
  refine xrec q Gt;
  // xI - xO case
  assume q _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc (xI x)) (mod_right acc (xO q)) = pos_compare_acc (xI x) acc (xO q)) _ _ _ acc;
  refine xrec q Gt;
  rewrite remove_mod_xI_xO;
  refine xrec q Gt;
  rewrite remove_mod_xI_xO;
  refine xrec q Gt;
  // xI - xH case
  rewrite remove_mod_discr (xI x) xH acc _;
  refine discr_Gt_Eq;
  reflexivity;

  assume x xrec y acc;
  refine pos_ind (λ y, pos_compare' (mod_left acc (xO x)) (mod_right acc y) = pos_compare_acc (xO x) acc y) _ _ _ y;
  // xO - xI case
  assume q _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc (xO x)) (mod_right acc (xI q)) = pos_compare_acc (xO x) acc (xI q)) _ _ _ acc;
  refine xrec q Lt;
  rewrite remove_mod_xO_xI;
  refine xrec q Lt;
  rewrite remove_mod_xO_xI;
  refine xrec q Lt;
  // xO - xO case
  assume q _;
  refine comp_ind (λ acc, pos_compare' (mod_left acc (xO x)) (mod_right acc (xO q)) = pos_compare_acc (xO x) acc (xO q)) _ _ _ acc;
  refine xrec q Eq;
  refine xrec q Lt;
  refine xrec q Gt;
  // xO - xH case
  rewrite remove_mod_discr (xO x) xH acc _;
  refine discr_Gt_Eq;
  reflexivity;

  refine pos_ind (λ y, `∀ acc, pos_compare' (mod_left acc xH) (mod_right acc y) = pos_compare_acc xH acc y) _ _ _;
  // xH - xI case
  assume p prec acc;
  rewrite remove_mod_discr xH (xI p) acc _;
  refine discr_Lt_Eq;
  reflexivity;
  // xH - xO case
  assume p prec acc;
  rewrite remove_mod_discr xH (xO p) acc _;
  refine discr_Lt_Eq;
  reflexivity;
  // xH - xH case
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pcc' x y : tEv (pos_compare x y = pos_compare' x y)
≔ begin
  assume x y;
  symmetry;
  refine pcc'_gen x y Eq;
end;

symbol pc'_xI x y : tEv (pos_compare' (xI x) y = Eq ⇒ `∃ q, y = xI q)
≔ begin
  assume x y;
  refine pos_ind (λ y, pos_compare' (xI x) y = Eq ⇒ `∃ q, y = xI q) _ _ _ y;
  assume q _ _ a b; refine b q _; reflexivity;
  assume q _ H;
  refine discr_pc'_xI_xO x q H (`∃ q0, xO q = xI q0);
  assume H;
  have f : tEv (is_Eq Gt);
  refine =_ind Gt Eq H (λ u, is_Eq u) _;
  refine tt;
  refine f (`∃ q, xH = xI q);
end;

symbol pc'_xO x y : tEv (pos_compare' (xO x) y = Eq ⇒ `∃ q, y = xO q)
≔ begin
  assume x y;
  refine pos_ind (λ y, pos_compare' (xO x) y = Eq ⇒ `∃ q, y = xO q) _ _ _ y;
  assume q _ H;
  refine discr_pc'_xO_xI x q H (`∃ q0, xI q = xO q0);
  assume q _ _ a b; refine b q _; reflexivity;
  assume H;
  have f : tEv (is_Eq Gt);
  refine =_ind Gt Eq H (λ u, is_Eq u) _;
  refine tt;
  refine f (`∃ q, xH = xO q);
end;

symbol pc'_xH y : tEv (pos_compare' xH y = Eq ⇒ xH = y)
≔ begin
  induction;
  assume q _ H;
  have e : tEv (is_Eq Eq ⇒ xH = xI q);
  rewrite left H; assume f;
  refine f _; refine e tt;

  assume q _ H;
  have e : tEv (is_Eq Eq ⇒ xH = xO q);
  rewrite left H; assume f;
  refine f _; refine e tt;

  assume _; reflexivity;
end;

symbol pc_Eq x y : tEv (pos_compare x y = Eq ⇒ x = y)
≔ begin
  assume x y;
  rewrite pcc';
  refine pos_ind (λ x, `∀ y, pos_compare' x y = Eq ⇒ x = y) _ _ _ x y;

  assume p prec q H;
  refine pc'_xI p q H _ (λ q', _);
  assume Hq1;
  rewrite Hq1;
  // TODO : how to improve this ? generalize too strong and rewrite on hyps
  have H1 : tEv (pos_compare' (xI p) q = Eq); refine H;
  generalize H1;
  refine =_ind q (xI q') Hq1 (λ u, pos_compare' (xI p) u = Eq ⇒ xI p = xI q') _;
  assume H1; rewrite prec q' H1;
  reflexivity;

  assume p prec q H;
  refine pc'_xO p q H _ (λ q', _);
  assume Hq1;
  rewrite Hq1;
  have H1 : tEv (pos_compare' (xO p) q = Eq); refine H;
  generalize H1;
  refine =_ind q (xO q') Hq1 (λ u, pos_compare' (xO p) u = Eq ⇒ xO p = xO q') _;
  assume H1; rewrite prec q' H1;
  reflexivity;

  refine pc'_xH;
end;

symbol pca_xH_Lt y : tEv (pos_compare_acc xH Lt y = Lt)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_Gt_xH x : tEv (pos_compare_acc x Gt xH  = Gt)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_xH_succ acc y : tEv (pos_compare_acc xH acc (pos_succ y) = Lt)
≔ begin
  assume acc;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_succ_xH acc x : tEv (pos_compare_acc (pos_succ x) acc xH = Gt)
≔ begin
  assume acc;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_succ_Lt x y :
  tEv (pos_compare_acc (pos_succ x) Lt y = pos_compare_acc x Gt y)
≔ begin
  refine pos_ind (λ x, `∀ y, pos_compare_acc (pos_succ x) Lt y = pos_compare_acc x Gt y) _ _ _;
  assume p prec;
  induction;
  // Case xI - xI
  assume q _; refine prec q;
  // Case xI - xO
  assume q _; refine prec q;
  // Case xI - xH
  reflexivity;

  assume p prec;
  induction;
  // Case xO - xI
  assume q _; reflexivity;
  // Case xO - xO
  assume q _; reflexivity;
  // Case xO - xH
  reflexivity;

  induction;
  // Case xH - xI
  assume q _; refine pca_xH_Lt q;
  // Case xH - xI
  assume q _; refine pca_xH_Lt q;
  // Case xH - xI
  reflexivity;
end;

symbol pca_Gt_succ x y :
  tEv (pos_compare_acc x Gt (pos_succ y) = pos_compare_acc x Lt y)
≔ begin
  assume x y;
  rewrite pca_comm;
  rewrite [pos_compare_acc x Lt y] pca_comm;
  refine f_equal (pos_compare_acc (pos_succ y) (CompOpp Gt) x) (pos_compare_acc y (CompOpp Lt) x) CompOpp _;
  refine pca_succ_Lt y x;
end;

symbol pca_succ_succ x y acc :
  tEv (pos_compare_acc (pos_succ x) acc (pos_succ y) = pos_compare_acc x acc y)
≔ begin
  refine pos_ind (λ x, `∀ y, `∀ acc, pos_compare_acc (pos_succ x) acc (pos_succ y) = pos_compare_acc x acc y) _ _ _;

  assume p prec y acc;
  refine pos_ind (λ y, pos_compare_acc (pos_succ (xI p)) acc (pos_succ y) = pos_compare_acc (xI p) acc y) _ _ _ y;
  // Case xI - xI
  assume q _; refine prec q acc;
  // Case xI - xO
  assume q _; refine pca_succ_Lt p q;
  // Case xI - xH
  refine pca_succ_xH acc p;

  assume p prec y acc;
  refine pos_ind (λ y, pos_compare_acc (pos_succ (xO p)) acc (pos_succ y) = pos_compare_acc (xO p) acc y) _ _ _ y;
  // Case xO - xI
  assume q _; refine pca_Gt_succ p q;
  // Case xO - xO
  assume q _; reflexivity;
  // Case xO - xH
  refine pca_Gt_xH p;

  assume y acc;
  refine pos_ind (λ y, pos_compare_acc (pos_succ xH) acc (pos_succ y) = pos_compare_acc xH acc y) _ _ _ y;
  // Case xH - xI
  assume q _; refine pca_xH_succ acc q;
  // Case xH - xO
  assume q _; refine pca_xH_Lt q;
  // Case xH - xH
  reflexivity;
end;

symbol pc'_succ_succ x y :
  tEv (pos_compare' (pos_succ x) (pos_succ y) = pos_compare' x y)
≔ begin
  assume x y;
  rewrite left pcc' x y;
  rewrite left pcc' (pos_succ x) (pos_succ y);
  refine pca_succ_succ x y Eq;
end;

symbol pc'_compat_add x y a :
  tEv (pos_compare' (pos_add x a) (pos_add y a) = pos_compare' x y)
≔ begin
  assume x y;
  refine pos_peano_ind (λ a, pos_compare' (pos_add x a) (pos_add y a) = pos_compare' x y) _ _;
  rewrite pos_add_xH_right;
  rewrite pos_add_xH_right;
  refine pc'_succ_succ x y;

  assume p prec;
  rewrite pos_add_succ_right;
  rewrite pos_add_succ_right;
  rewrite pc'_succ_succ;
  refine prec;
end;

// Integers

inductive Z : TYPE ≔
| Z0 : Z
| Zpos : positive → Z
| Zneg : positive → Z;

symbol DZ : Type;
rule tEv DZ ↪ Z;
unif_rule Z ≡ tEv $t ↪ [ $t ≡ DZ ];

// symbol DZ : Type;
// symbol Z ≔ tEv DZ;

// symbol Z0 : Z;
// symbol Zpos : positive → Z;
// symbol Zneg : positive → Z;

symbol Z_ind :
  tEv (`π Q : Z → Type,
       Q Z0 ⇒
       (`∀ p : positive, Q (Zpos p)) ⇒
       (`∀ p : positive, Q (Zneg p)) ⇒
       `∀ z : Z, Q z) ≔ ind_Z;

// rule Z_ind _ $v0 _     _     Z0        ↪ $v0
// with Z_ind _ _   $vpos _     (Zpos $x) ↪ $vpos $x
// with Z_ind _ _   _     $vneg (Zneg $x) ↪ $vneg $x;

symbol zero ≔ Z0;
symbol one ≔ Zpos xH;

symbol ~ ≔
  Z_ind (λ _, DZ)
     zero
     (λ x, Zneg x)
     (λ x, Zpos x);
notation ~ prefix 44;

symbol double ≔
  Z_ind (λ _, DZ)
    zero
    (λ p, Zpos (xO p))
    (λ p, Zneg (xO p));

symbol double_opp x : tEv (double (~ x) = ~ double x)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Check that 2 * 7 ≡ 14
// assert ⊢ double (Zpos (xI (xI xH))) ≡ Zpos (xO (xI (xI xH)));

symbol succ_double ≔
  Z_ind (λ _, DZ)
    one
    (λ p, Zpos (xI p))
    (λ p, Zneg (pos_pred_double p));

// Check that 2 * (-5) + 1 ≡ -9 and that 2 * 5 + 1 ≡ 11
// assert ⊢ succ_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xO (xO xH)));
// assert ⊢ succ_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xI (xO xH)));

symbol pred_double ≔
  Z_ind (λ _, DZ)
    (Zneg xH)
    (λ p, Zpos (pos_pred_double p))
    (λ p, Zneg (xI p));

symbol pred_double_opp x : tEv (pred_double (~ x) = ~ succ_double x)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol succ_double_opp x : tEv (succ_double (~ x) = ~ pred_double x)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

// Check that 2 * (-5) - 1 ≡ -11 and that 2 * 5 - 1 ≡ 9
// assert ⊢ pred_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xI (xO xH)));
// assert ⊢ pred_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xO (xO xH)));

symbol pos_sub ≔
  pos_ind (λ _, Dpositive ⇒ DZ)
     (λ p pos_sub_p, pos_ind (λ _, DZ)
        (λ q _, double (pos_sub_p q))
        (λ q _, succ_double (pos_sub_p q))
        (Zpos (xO p)))
     (λ p pos_sub_p, pos_ind (λ _, DZ)
        (λ q _, pred_double (pos_sub_p q))
        (λ q _, double (pos_sub_p q))
        (Zpos (pos_pred_double p)))
     (pos_ind (λ _, DZ)
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

symbol ps_same x : tEv (pos_sub x x = zero)
≔ begin
  induction;
  assume x xrec;
  have e : tEv (pos_sub (xI x) (xI x) = double (pos_sub x x));
  reflexivity; rewrite e; rewrite xrec; reflexivity;
  assume x xrec;
  have e : tEv (pos_sub (xO x) (xO x) = double (pos_sub x x));
  reflexivity; rewrite e; rewrite xrec; reflexivity;
  reflexivity;
end;


symbol ps_opp x y : tEv (~ pos_sub x y = pos_sub y x)
≔ begin
  refine pos_ind (λ x, `∀ y, ~ (pos_sub x y) = pos_sub y x) _ _ _;
  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xI a) (xI b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left double_opp (pos_sub a b);
  rewrite arec; reflexivity;
  assume b _;
  have e : tEv (pos_sub (xI a) (xO b) = succ_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left pred_double_opp (pos_sub a b);
  rewrite arec; reflexivity;
  reflexivity;

  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xO a) (xI b) = pred_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left succ_double_opp (pos_sub a b);
  rewrite arec; reflexivity;
  assume b _;
  have e : tEv (pos_sub (xO a) (xO b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left double_opp (pos_sub a b);
  rewrite arec; reflexivity;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol + x y ≔
  Z_ind (λ _, DZ)
    y
    (λ x', Z_ind (λ _, DZ)
       x
       (λ y', Zpos (pos_add x' y'))
       (λ y', pos_sub x' y')
       y)
    (λ x', Z_ind (λ _, DZ)
       x
       (λ y', pos_sub y' x')
       (λ y', Zneg (pos_add x' y'))
       y)
    x;
notation + infix left 40;

symbol add_comm x y : tEv (x + y = y + x)
≔ begin
  refine Z_ind (λ x, `∀ y, x + y = y + x) _ _ _;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  assume y; have e : tEv (Zpos x + Zpos y = Zpos (pos_add x y));
  reflexivity; rewrite e;
  rewrite pos_add_comm; reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  reflexivity;
  assume y; have e : tEv (Zneg x + Zneg y = Zneg (pos_add x y));
  reflexivity; rewrite e;
  rewrite pos_add_comm; reflexivity;
end;

symbol add_Z0 x : tEv (Z0 + x = x)
≔ begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol add_Z0_right x : tEv (x + Z0 = x)
≔ begin
  induction; reflexivity; reflexivity; reflexivity;
end;

symbol succ x ≔ x + one;

symbol - x y ≔ x + ~ y;
notation - infix left 40;

symbol sub_def x y : tEv (x - y = x + ~ y)
≔ begin assume x y; reflexivity; end;

symbol add_opp a : tEv (a - a = zero)
≔ begin
  induction;
  reflexivity;
  assume x; refine ps_same x;
  assume x; refine ps_same x;
end;

symbol * x y ≔
  Z_ind (λ _, DZ)
     zero
     (λ x', Z_ind (λ _, DZ)
        zero
        (λ y', Zpos (pos_mul x' y'))
        (λ y', Zneg (pos_mul x' y'))
        y)
     (λ x', Z_ind (λ _, DZ)
        zero
        (λ y', Zneg (pos_mul x' y'))
        (λ y', Zpos (pos_mul x' y'))
        y)
     x;
notation * infix right 42;



symbol distr_opp x y : tEv (~ (x + y) = ~ x + ~ y)
≔ begin
  assume x y;
  refine Z_ind (λ x, ~ (x + y) = (~ x + ~ y)) _ _ _ x;
  reflexivity;
  assume a;
  refine Z_ind (λ y, ~ (Zpos a + y) = (~ (Zpos a) + ~ y)) _ _ _ y;
  reflexivity;
  reflexivity;
  assume b; refine ps_opp a b;
  assume a;
  refine Z_ind (λ y, ~ (Zneg a + y) = (~ (Zneg a) + ~ y)) _ _ _ y;
  reflexivity;
  assume b;
  refine ps_opp b a;
  reflexivity;
end;

// TODO
symbol ps_Zpos a b c : tEv (pos_sub a b + Zpos c = pos_sub (pos_add a c) b);

symbol ps_Zneg a b c : tEv (pos_sub a b + Zneg c = pos_sub a (pos_add b c))
≔ begin
  assume a b c;
  rewrite left ps_opp b a;
  have e : tEv (Zneg c = ~ Zpos c);
  reflexivity; rewrite e;
  rewrite left distr_opp (pos_sub b a) (Zpos c);
  rewrite ps_Zpos;
  rewrite ps_opp;
  reflexivity;
end;

symbol add_assoc x y z : tEv (x + y + z = x + (y + z))
≔ begin
  assume x y z;
  refine Z_ind (λ x, (x + y) + z = x + (y + z)) _ _ _ x;
  reflexivity;

  assume a;
  refine Z_ind (λ y, ((Zpos a + y) + z) = (Zpos a + (y + z))) _ _ _ y;
  reflexivity;

  assume b;
  refine Z_ind (λ z, ((Zpos a + Zpos b) + z) = (Zpos a + (Zpos b + z))) _ _ _ z;
  reflexivity;
  // Zpos - Zpos - Zpos case
  assume c;
  have e : tEv ((Zpos a + Zpos b) + Zpos c = Zpos (pos_add (pos_add a b) c));
  reflexivity; rewrite e; rewrite pos_add_assoc; reflexivity;
  // Zpos - Zpos - Zneg case
  assume c;
  symmetry; rewrite add_comm;
  rewrite [Zpos a + Zpos b] add_comm;
  refine ps_Zpos b c a;

  assume b;
  refine Z_ind (λ z, ((Zpos a + Zneg b) + z) = (Zpos a + (Zneg b + z))) _ _ _ z;
  rewrite add_Z0_right; rewrite add_Z0_right; reflexivity;
  // Zpos - Zneg - Zpos case
  assume c;
  have e : tEv (Zpos a + Zneg b = pos_sub a b);
  reflexivity; rewrite e;
  rewrite ps_Zpos a b c;
  rewrite pos_add_comm; symmetry;
  rewrite add_comm; refine ps_Zpos c b a;
  // Zpos - Zneg - Zpos case
  assume c;
  refine ps_Zneg a b c;

  assume a;
  refine Z_ind (λ y, ((Zneg a + y) + z) = (Zneg a + (y + z))) _ _ _ y;
  reflexivity;

  assume b;
  refine Z_ind (λ z, ((Zneg a + Zpos b) + z) = (Zneg a + (Zpos b + z))) _ _ _ z;
  rewrite add_Z0_right; rewrite add_Z0_right; reflexivity;
  // Zneg - Zpos - Zpos case
  assume c;
  refine ps_Zpos b a c;
  // Zneg - Zpos - Zneg case
  assume c;
  have e : tEv ((Zneg a + Zpos b) + Zneg c = pos_sub b a + Zneg c);
  reflexivity; rewrite e; rewrite ps_Zneg b a c;
  symmetry; rewrite pos_add_comm; rewrite add_comm;
  refine ps_Zneg b c a;

  assume b;
  refine Z_ind (λ z, ((Zneg a + Zneg b) + z) = (Zneg a + (Zneg b + z))) _ _ _ z;
  reflexivity;
  // Zneg - Zneg - Zpos case
  assume c;
  rewrite [Zneg a + Zneg b] add_comm;
  symmetry; rewrite add_comm;
  refine ps_Zneg c b a;
  // Zneg - Zneg - Zneg case
  assume c;
  have e : tEv (Zneg a + Zneg b + Zneg c = Zneg (pos_add (pos_add a b) c));
  reflexivity; rewrite e;
  rewrite pos_add_assoc;
  reflexivity;
end;

symbol compare x y ≔
  Z_ind (λ _, Dcomparison)
     (Z_ind (λ _, Dcomparison)
         Eq
         (λ _, Lt)
         (λ _, Gt)
         y)
     (λ x', Z_ind (λ _, Dcomparison)
        Gt
        (λ y', pos_compare x' y')
        (λ _, Gt)
        y)
     (λ x', Z_ind (λ _, Dcomparison)
        Lt
        (λ _, Lt)
        (λ y', pos_compare y' x')
        y)
     x;

symbol c_comm x y : tEv (compare x y = CompOpp (compare y x))
≔ begin
  assume x;
  refine ind_Z (λ x, `∀ y, compare x y = CompOpp (compare y x)) _ _ _ x;

  induction;
  reflexivity; reflexivity; reflexivity;

  assume x0;
  induction;
  reflexivity;
  assume x1; refine pca_comm x0 x1 Eq;
  reflexivity;

  assume x0;
  induction;
  reflexivity;
  reflexivity;
  assume x1; refine pca_comm x1 x0 Eq;
end;

// TODO
symbol c_opp a b :
  tEv (compare (~ a) (~ b) = CompOpp (compare a b));

// TODO
symbol pc'_sub a b c :
  tEv (pos_compare' a b = compare (pos_sub a b) (pos_sub b c));

// TODO
symbol c_Zpos_add_sub a b c :
  tEv (compare (Zpos (pos_add a c)) (pos_sub a b) = Gt);

symbol leb x y ≔
  comp_ind (λ _, Dboolean)
      True
      True
      False
      (compare x y);
symbol leb_def x y : tEv (leb x y = (comp_ind (λ _, Dboolean) True True False (compare x y)))
≔ begin reflexivity; end;

symbol leb_eq x y : tEv (compare x y = Eq ⇒ leb x y = True)
≔ begin
  assume x y eq;
  rewrite leb_def;
  refine =_ind (compare x y) Eq eq (λ u, comp_ind (λ _, Dboolean) True True False u = True) _;
  reflexivity;
end;

symbol leb_lt x y : tEv (compare x y = Lt ⇒ leb x y = True)
≔ begin
  assume x y eq;
  rewrite leb_def;
  refine =_ind (compare x y) Lt eq (λ u, comp_ind (λ _, Dboolean) True True False u = True) _;
  reflexivity;
end;
symbol leb_gt x y : tEv (compare x y = Gt ⇒ leb x y = False)
≔ begin
  assume x y eq;
  rewrite leb_def;
  refine =_ind (compare x y) Gt eq (λ u, comp_ind (λ _, Dboolean) True True False u = False) _;
  reflexivity;
end;

symbol ltb x y ≔
  comp_ind (λ _, Dboolean)
      False
      True
      False
      (compare x y);
symbol ltb_def x y : tEv (ltb x y = (comp_ind (λ _, Dboolean) False True False (compare x y)))
≔ begin reflexivity; end;

symbol ltb_eq x y : tEv (compare x y = Eq ⇒ ltb x y = False)
≔ begin
  assume x y eq;
  rewrite ltb_def;
  refine =_ind (compare x y) Eq eq (λ u, comp_ind (λ _, Dboolean) False True False u = False) _;
  reflexivity;
end;
symbol ltb_lt x y : tEv (compare x y = Lt ⇒ ltb x y = True)
≔ begin
  assume x y eq;
  rewrite ltb_def;
  refine =_ind (compare x y) Lt eq (λ u, comp_ind (λ _, Dboolean) False True False u = True) _;
  reflexivity;
end;
symbol ltb_gt x y : tEv (compare x y = Gt ⇒ ltb x y = False)
≔ begin
  assume x y eq;
  rewrite ltb_def;
  refine =_ind (compare x y) Gt eq (λ u, comp_ind (λ _, Dboolean) False True False u = False) _;
  reflexivity;
end;

symbol geb x y ≔
  comp_ind (λ _, Dboolean)
      True
      False
      True
      (compare x y);
symbol geb_def x y : tEv (geb x y = (comp_ind (λ _, Dboolean) True False True (compare x y)))
≔ begin reflexivity; end;

symbol geb_eq x y : tEv (compare x y = Eq ⇒ geb x y = True)
≔ begin
  assume x y eq;
  rewrite geb_def;
  refine =_ind (compare x y) Eq eq (λ u, comp_ind (λ _, Dboolean) True False True u = True) _;
  reflexivity;
end;
symbol geb_lt x y : tEv (compare x y = Lt ⇒ geb x y = False)
≔ begin
  assume x y eq;
  rewrite geb_def;
  refine =_ind (compare x y) Lt eq (λ u, comp_ind (λ _, Dboolean) True False True u = False) _;
  reflexivity;
end;
symbol geb_gt x y : tEv (compare x y = Gt ⇒ geb x y = True)
≔ begin
  assume x y eq;
  rewrite geb_def;
  refine =_ind (compare x y) Gt eq (λ u, comp_ind (λ _, Dboolean) True False True u = True) _;
  reflexivity;
end;

symbol gtb x y ≔
  comp_ind (λ _, Dboolean)
      False
      False
      True
      (compare x y);
symbol gtb_def x y : tEv (gtb x y = (comp_ind (λ _, Dboolean) False False True (compare x y)))
≔ begin reflexivity; end;

symbol gtb_eq x y : tEv (compare x y = Eq ⇒ gtb x y = False)
≔ begin
  assume x y eq;
  rewrite gtb_def;
  refine =_ind (compare x y) Eq eq (λ u, comp_ind (λ _, Dboolean) False False True u = False) _;
  reflexivity;
end;
symbol gtb_lt x y : tEv (compare x y = Lt ⇒ gtb x y = False)
≔ begin
  assume x y eq;
  rewrite gtb_def;
  refine =_ind (compare x y) Lt eq (λ u, comp_ind (λ _, Dboolean) False False True u = False) _;
  reflexivity;
end;
symbol gtb_gt x y : tEv (compare x y = Gt ⇒ gtb x y = True)
≔ begin
  assume x y eq;
  rewrite gtb_def;
  refine =_ind (compare x y) Gt eq (λ u, comp_ind (λ _, Dboolean) False False True u = True) _;
  reflexivity;
end;


builtin "0"  ≔  zero;
builtin "+1" ≔  succ;

symbol ≤ x y ≔ is_True (leb x y);
notation ≤ infix 30;
symbol < x y ≔ is_True (ltb x y);
notation < infix 30;
symbol ≥ x y ≔ is_True (geb x y);
notation ≥ infix 30;
symbol > x y ≔ is_True (gtb x y);
notation > infix 30;

// assert ⊢ 3 < ~ 2 ≡ false;
// assert ⊢ 3 < 3 ≡ false;
// assert ⊢ 3 < 5 ≡ true;

// assert ⊢ 4 ≥ ~ 3 ≡ true;
// assert ⊢ 4 ≥ 4 ≡ true;
// assert ⊢ 4 ≥ 7 ≡ false;

symbol natlike_rec : Π (P : Z → Type), tEv (P 0) →
                     (Π (z : Z), tEv (0 ≤ z) → tEv (P z) → tEv (P (z + 1))) →
                     Π (z : Z), tEv (0 ≤ z) → tEv (P z)
≔ begin
  assume P p0 prec z Hz;
  have posrec : Π p, tEv (P (Zpos p));
  refine pos_peano_ind (λ p, P (Zpos p)) _ _;
  refine prec 0 _ p0;
  refine tt;

  assume a ha;
  have e : tEv (Zpos (pos_succ a) = Zpos a + 1);
  refine pos_ind (λ a, Zpos (pos_succ a) = Zpos a + 1) _ _ _ a;
  reflexivity; reflexivity; reflexivity;
  rewrite e;
  refine prec (Zpos a) _ ha;
  refine tt;

  refine Z_ind (λ z, 0 ≤ z ⇒ P z) _ _ _ z Hz;
  assume _; refine p0;
  assume p _; refine posrec p;

  assume p Hp;
  refine Hp (P (Zneg p));
end;

symbol simpl_right x a : tEv (x + a - a = x)
≔ begin
  assume x a;
  rewrite sub_def;
  rewrite add_assoc;
  rewrite left (sub_def a a);
  rewrite add_opp;
  rewrite add_comm;
  reflexivity;
end;


symbol simpl_inv_right x a : tEv (x - a + a = x)
≔ begin
  assume x a;
  rewrite sub_def;
  rewrite add_assoc;
  rewrite [~ a + a] add_comm;
  // have e : Π u v, tEv (u - v = u + ~ v);
  // refine sub_def;
  // apply sub_def ? (apply almost never works)
  rewrite left (sub_def a a);
  rewrite add_opp;
  rewrite add_comm;
  reflexivity;
end;

// TODO
symbol le_compat_add x y a : tEv (x ≤ y) → tEv (x + a ≤ y + a);
// TODO
symbol lt_compat_add x y a : tEv (x < y) → tEv (x + a < y + a);

symbol le_add_compat x y a : tEv (x + a ≤ y + a) → tEv (x ≤ y)
≔ begin
  assume x y a leq;
  rewrite left (simpl_right x a);
  rewrite left (simpl_right y a);
  rewrite sub_def;
  rewrite sub_def;
  refine le_compat_add (x + a) (y + a) (~ a) leq;
end;

symbol lt_add_compat x y a : tEv (x + a < y + a) → tEv (x < y)
≔ begin
  assume x y a ltq;
  rewrite left (simpl_right x a);
  rewrite left (simpl_right y a);
  rewrite sub_def;
  rewrite sub_def;
  refine lt_compat_add (x + a) (y + a) (~ a) ltq;
end;

// TODO
symbol lt_le u z : tEv (u < succ z) → tEv (u ≤ z);
// TODO
symbol le_lt u z : tEv (u ≤ z) → tEv (u < succ z);

// TODO : need decidability of equality
symbol case u bound : tEv (u ≤ bound) → tEv (bound = u ∨ u < bound);
// ≔ begin
//   assume u z luz;
//   refine ind_comparison (λ c, compare u z = c ⇒ z = u ∨ u < z) _ _ _ (compare u z) _;

//   assume eq; refine or_intro_1 _ _ _;
// end;

symbol max (x y : Z)
≔ if DZ (leb x y) y x;

symbol max_def x y : tEv (max x y = if DZ (leb x y) y x)
≔ begin reflexivity; end;

symbol max_is_greater_1 : Π x y, tEv (x ≤ max x y)
≔ begin
  assume x y;
  refine ind_boolean (λ b, leb x y = b ⇒ x ≤ max x y) _ _ (leb x y) _;
  assume lxy;
  rewrite max_def;
  rewrite lxy;
  refine eq_True_is_True (leb x y) lxy;

  assume nlxy;
  rewrite max_def;
  rewrite nlxy;
  refine le_add_compat x x (~ x) _;
  rewrite left (sub_def x x);
  rewrite add_opp; refine tt;

  reflexivity;
end;

symbol max_is_greater_2 : Π x y, tEv (y ≤ max x y)
≔ begin
  assume x y;
  refine ind_boolean (λ b, leb x y = b ⇒ y ≤ max x y) _ _ (leb x y) _;
  assume lxy;
  rewrite max_def;
  rewrite lxy;
  refine le_add_compat y y (~ y) _;
  rewrite left (sub_def y y);
  rewrite add_opp; refine tt;

  assume nlxy; rewrite max_def; rewrite nlxy; generalize nlxy;
  refine ind_comparison (λ c, compare x y = c ⇒ leb x y = False ⇒ y ≤ x)
         _ _ _ (compare x y) _;
  assume eq; rewrite (leb_eq x y eq);
  assume f;
  have e : tEv (False = True); rewrite f; reflexivity;
  refine discr_False_True e _;

  assume lt; rewrite (leb_lt x y lt);
  assume f;
  have e : tEv (False = True); rewrite f; reflexivity;
  refine discr_False_True e _;

  assume gt _;
  have lt : tEv (CompOpp (compare x y) = CompOpp Gt);
  rewrite gt; reflexivity;
  generalize lt;
  have g : tEv (CompOpp (compare x y) = Lt ⇒ y ≤ x);
  rewrite left (c_comm y x);
  assume lt;
  refine eq_True_is_True (leb y x) _;
  refine leb_lt y x lt;
  refine g;

  reflexivity;
  reflexivity;
end;

// Prove strong induction


symbol strong_bound_0_alt_rec : Π P,
                                (Π z, tEv (z ≤ 0) → tEv (P z)) →
                                (Π z, tEv (0 ≤ z) →
                                      (Π v, tEv (v ≤ z) → tEv (P v)) →
                                      tEv (P (z + 1))) →
                                Π z, tEv (P z)
≔
begin
  assume P p0 prec;

// use natlike_rec on Q ≔ λz, ∀ u, u ≤ z → P u
  have q : Π z, tEv (0 ≤ z) → Π u, tEv (u ≤ z) → tEv (P u);
  refine natlike_rec (λ a, `∀ u : Z, u ≤ a ⇒ P u) _ _;
// Base case
  refine p0;
// Recursive case
  assume z Hz Hrec u Hu;
  refine case u (succ z) Hu (P u) _ _;
  assume eq_sz_u;
  rewrite left eq_sz_u;
  refine prec z Hz _;
  refine Hrec;
  assume lt_u_sz;
  refine Hrec u _;
  refine lt_le u z lt_u_sz;

  assume z;
  refine q (max 0 z) _ z _;
  refine max_is_greater_1 0 z;
  refine max_is_greater_2 0 z;
end;

symbol strong_ind : Π a P,
                    (Π x, tEv (x ≤ a) → tEv (P x)) →
                    (Π x, tEv (a < x) →
                          (Π v, tEv (v < x) → tEv (P v)) →
                          tEv (P x)) →
                    Π x, tEv (P x)
≔ begin
  assume a P p0 prec;

  have q : Π z, tEv (P (z + a));
  refine strong_bound_0_alt_rec (λ z, P (z + a)) _ _;
// Base case
  assume z Hz;
  refine p0 (z + a) _;
  refine le_compat_add z 0 a Hz;
// Recursive case
  assume z Hz Hrec;
  refine prec (z + 1 + a) _ _;
  refine lt_compat_add 0 (z + 1) a _;
  refine le_lt 0 z Hz;
  assume v Hv;
  have e : tEv (v = v - a + a);
  symmetry;
  refine simpl_inv_right v a;
  rewrite e;
  refine Hrec (v - a) _;
  refine lt_le (v - a) z _;
  have eqsa : tEv (z + 1 + a - a = succ z);
  refine simpl_right (succ z) a;
  rewrite left eqsa;
  refine lt_compat_add v (z + 1 + a) (~ a) Hv;

  assume x;
  have e : tEv (x - a + a = x);
  refine simpl_inv_right x a;
  rewrite left e;
  refine q (x - a);
end;


// ENCODING OF TASKS


symbol empty : Type
≔  false;

symbol hyp : Type → Type → Type
≔  λ A s, A ⇒ s;

symbol goal : Type → Type → Type
≔  λ A s, ¬ A ⇒ s;

// A task < t | x : t | H : A ⊢ G : B > is encoded by
// < `π t : Type, ∀ x : t, hyp (tr A) (goal (tr A)) empty >
// where < tr > is the function encoding terms


// KERNEL CERTIFICATE RULES


symbol hole :
  tEv empty →
  tEv empty
≔  λ f, f;

symbol axiom A :
  tEv (hyp A (goal A empty))
≔  λ a na, na a;

symbol trivial_hyp :
  tEv (hyp false empty)
≔  λ f, f;

symbol trivial_goal :
  tEv (goal true empty)
≔  λ ntt, ntt tt;

symbol eqrefl T t :
  tEv (goal (t = t) empty)
≔  λ neqtt, neqtt (=_refl T t);

symbol cut A :
  tEv (goal A empty) →
  tEv (hyp A empty) →
  tEv empty
≔  λ nna na, nna na;

symbol split_hyp A B :
  tEv (hyp A empty) →
  tEv (hyp B empty) →
  tEv (hyp (A ∨ B) empty)
≔  λ s1 s2 ab, or_elim A B ab false s1 s2;

symbol split_goal A B :
    tEv (goal A empty) →
    tEv (goal B empty) →
    tEv (goal (A ∧ B) empty)
≔  λ nna nnb, nni (A ∧ B) (and_intro A B (nne A nna) (nne B nnb));

symbol unfold_iff_hyp A B :
    tEv (hyp ((A ⇒ B) ∧ (B ⇒ A)) empty) →
    tEv (hyp (A ⇔ B) empty)
≔  λ s, s;

symbol unfold_iff_goal A B :
    tEv (goal ((A ⇒ B) ∧ (B ⇒ A)) empty) →
    tEv (goal (A ⇔ B) empty)
≔  λ s, s;

symbol unfold_arr_hyp A B :
    tEv (hyp (¬ A ∨ B) empty) →
    tEv (hyp (A ⇒ B) empty)
≔  λ s impab,
   s (em A (¬ A ∨ B) (λ a, or_intro_2 (¬ A) B (impab a))
     	      	     (λ na, or_intro_1 (¬ A) B na));

symbol unfold_arr_goal A B :
    tEv (goal (¬ A ∨ B) empty) →
    tEv (goal (A ⇒ B) empty)
≔  λ s, nni (A ⇒ B) (λ a,
      nne (¬ A ∨ B) s B (λ na, na a B)
                        (λ b, b));

symbol swap_neg_hyp A :
    tEv (goal A empty) →
    tEv (hyp (¬ A) empty)
≔  λ s, s;

symbol swap_hyp A :
    tEv (goal (¬ A) empty) →
    tEv (hyp A empty)
≔  λ nnna, nne (¬ A) nnna;

symbol swap_goal A :
    tEv (hyp (¬ A) empty) →
    tEv (goal A empty)
≔  λ s, s;

symbol swap_neg_goal A :
    tEv (hyp A empty) →
    tEv (goal (¬ A) empty)
≔  λ na, nni (¬ A) na;

symbol destruct_hyp A B :
    tEv (hyp A (hyp B empty)) →
    tEv (hyp (A ∧ B) empty)
≔  λ s ab,
   s (and_elim_1 A B ab) (and_elim_2 A B ab);

symbol destruct_goal A B :
    tEv (goal A (goal B empty)) →
    tEv (goal (A ∨ B) empty)
≔  λ s nab, s (λ a, nab (or_intro_1 A B a))
              (λ b, nab (or_intro_2 A B b));

symbol construct_goal A B :
    tEv (goal (A ∨ B) empty) →
    tEv (goal A (goal B empty))
≔  λ s na nb, or_elim A B (nne (A ∨ B) s) false na nb;

symbol dir_left_hyp A B :
    tEv (hyp A empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ na ab, na (and_elim_1 A B ab);

symbol dir_left_goal A B :
    tEv (goal A empty) →
    tEv (goal (A ∨ B) empty)
≔  λ nna nab, nab (or_intro_1 A B (nne A nna));

symbol dir_right_hyp A B :
    tEv (hyp B empty) →
    tEv (hyp (A ∧ B) empty)
≔  λ nb ab, nb (and_elim_2 A B ab);

symbol dir_right_goal A B :
    tEv (goal B empty) →
    tEv (goal (A ∨ B) empty)
≔  λ nnb nab, nab (or_intro_2 A B (nne B nnb));

symbol clearhyp A :
    tEv empty →
    tEv (hyp A empty)
≔  λ f _, f;

symbol clear_hyp A HA s ≔ clearhyp A s HA;

symbol cleargoal A :
    tEv empty →
    tEv (goal A empty)
≔  λ f _, f;

symbol clear_goal A HA s ≔ cleargoal A s HA;

symbol forget :
    tEv empty →
    tEv empty
≔  λ f, f;

symbol intro_quant_hyp {T} P :
    (Π y, tEv (hyp (P y) empty)) →
    tEv (hyp (`∃ x : tEv T, P x) empty)
≔  λ s ep, exists_elim T P false ep s;

symbol intro_quant_goal {T} P :
    (Π y, tEv (goal (P y) empty)) →
    tEv (goal (`∀ x : tEv T, P x) empty)
≔  λ s nfp, nfp (λ t, nne (P t) (s t));

symbol inst_quant_goal {T} P t :
    tEv (goal (`∃ x : tEv T, P x) (goal (P t) empty)) →
    tEv (goal (`∃ x : tEv T, P x) empty)
≔  λ s nep, s nep (λ pt, nep (exists_intro T P t pt));

symbol inst_quant_hyp {T} P t :
    tEv (hyp (`∀ x, P x) (hyp (P t) empty)) →
    tEv (hyp (`∀ x : tEv T, P x) empty)
≔  λ s h, s h (h t);

symbol rewrite_hyp {T} (a b : tEv T) P :
   tEv (hyp (a = b) (hyp (P b) empty)) →
   tEv (hyp (a = b) (hyp (P a) empty))
≔ begin
  assume T a b P s eq pa;
  refine s eq _;
  rewrite left eq;
  refine pa;
end;

symbol rewrite_goal {T} (a b : tEv T) P :
   tEv (hyp (a = b) (goal (P b) empty)) →
   tEv (hyp (a = b) (goal (P a) empty))
≔  begin
  assume T a b P s eq pa;
  refine s eq _;
  rewrite left eq;
  refine pa;
end;

symbol rewrite_fmla_hyp A B P :
   tEv (hyp (eq_fmla A B) (hyp (P B) empty)) →
   tEv (hyp (eq_fmla A B) (hyp (P A) empty))
≔  λ s h i, s h (h P i);

symbol rewrite_fmla_goal A B P :
   tEv (hyp (eq_fmla A B) (goal (P B) empty)) →
   tEv (hyp (eq_fmla A B) (goal (P A) empty))
≔  λ s h i, s h (h (λ x, ¬ P x) i);

symbol iffeq A B :
  tEv (hyp (eq_fmla A B) empty) →
  tEv (hyp (A ⇔ B) empty)
≔  λ s eab, s (iff_eq A B eab);

symbol strong_induction a P :
   (Π x, tEv (hyp (x ≤ a) (goal (P x) empty))) →
   (Π x, tEv (hyp (a < x) (hyp (`∀ n : Z, n < x ⇒ P n) (goal (P x) empty)))) →
   Π x, tEv (goal (P x) empty)
≔ begin
  assume a P pbase prec x;
  refine nni (P x) _;
  refine strong_ind a P _ _ x;
  assume z Hz;
  refine nne (P z) _;
  refine pbase z Hz;

  assume z Ha Hrec;
  refine nne (P z) _;
  refine prec z Ha Hrec;
end;


// COMPATIBILITY WITH IDENTIFIERS FROM Why3

symbol int ≔ DZ;
symbol bool ≔ Dboolean;

// symbol True ≔ True;
// symbol False ≔ False;

symbol infixspeq T a b ≔ @= T a b;

symbol infixsppl ≔ @+;
symbol infixspas ≔ @*;
symbol infixspmn ≔ @-;
symbol prefixspmn z ≔ ~ z;

symbol infixsplseq ≔ @≤;
symbol infixspls ≔ @<;
symbol infixspgteq ≔ @≥;
symbol infixspgt ≔ @>;

// Also targeted, but not from an ident : quantifications and arrows, true,
// false, ∧, ∨, ¬, ⇔, ~, Z, boolean, DType, Type, int litterals
