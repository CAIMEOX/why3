

// COC ENCODING


symbol Type : TYPE;
symbol Kind : TYPE;

injective symbol tEv : Type → TYPE;
injective symbol kEv : Kind → TYPE;

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

symbol ⇀ A B ≔  kkPi A (λ _, B);
notation ⇀ infix right 14;

symbol ⇁ A B ≔  tkPi A (λ _, B);
notation ⇁ infix right 14;

symbol ⇒ A B ≔  ttPi A (λ _, B);
notation ⇒ infix right 14;

// To use the inductive notation

builtin "Prop" ≔ Type;
builtin "P" ≔ tEv;

// Define our higher order logic

symbol ⊥ ≔ `π C : Type, C;
symbol ⊤ ≔ ⊥ ⇒ ⊥;
symbol tt : tEv ⊤ ≔ λ x, x;

symbol ¬ A ≔ A ⇒ ⊥;
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


// UTILITY THEOREMS


//  Reasoning about negation.

symbol to_nn A : tEv A → tEv (¬ ¬ A)
≔ λ a na, na a;

symbol from_nn A : tEv (¬ ¬ A) → tEv A
≔ λ nna, em A A (λ a, a) (λ na, nna na A);

// Implication

symbol fold_arrow {A B} : tEv (A ⇒ B) → tEv A → tEv B
≔ λ p, p;

// Disjunction

symbol Left A B : tEv (
  A ⇒ A ∨ B)
≔ λ (a : tEv A) C (ac: tEv A → tEv C) _, ac a;

symbol Right A B : tEv (
  B ⇒ A ∨ B)
≔ λ (b : tEv B) C _ (bc: tEv B → tEv C), bc b;

symbol DestructDisj A B C : tEv (
  A ∨ B ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C)
≔ λ H, H C;

// Conjunction

symbol SplitConj A B : tEv (
  A ⇒ B ⇒ A ∧ B)
≔ λ a b C p, p a b;

symbol DestructConj A B C : tEv (
  A ∧ B ⇒ (A ⇒ B ⇒ C) ⇒ C)
≔ λ ab, ab C;

// Equality

symbol eq T (x y : tEv T) ≔ `π P, P x ⇒ P y;

symbol eq_fmla A B ≔ @π (DType ⇀ DType)
                      (λ P, P A ⇒ P B);

// This axiom is needed to be able to rewrite formulas
symbol iff_eq A B : tEv (
  (A ⇔ B) ⇒
  eq_fmla A B);

symbol eq_refl {T} x : tEv (eq T x x)
≔ λ P px, px;

symbol eq_sym {T} x y : tEv (eq T x y) → tEv (eq T y x)
≔ λ eqxy, eqxy (λ t, eq T t x) (eq_refl x);

symbol eq_trans {T} x y z: tEv (eq T x y) → tEv (eq T y z) → tEv (eq T x z)
≔ λ eqxy eqyz, eqyz (λ t, eq T x t) eqxy;

symbol eq_ind T x y : tEv (eq T x y) → Π P, tEv (P y) → tEv (P x)
≔ λ eq, eq_sym x y eq;

// symbol exists (T : Kind) (P : kEv T → Type)  ≔
// `π C, (`π x : kEv T, P x ⇒ C) ⇒ C;

// opaque symbol eq_and_def :
//   tEv (exists (kkPi DType (λ T, T ⇁ T ⇁ DType)) (λ eq,
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
symbol = {T} : tEv T → tEv T → Type; // ≔ @eq T;
notation = infix 22;

symbol =_refl T (x : tEv T) : tEv (x = x);

symbol =_ind {T} (x y : tEv T) : tEv (x = y) → Π P, tEv (P y) → tEv (P x);

builtin "T"     ≔ tEv;
builtin "eq"    ≔ =;
builtin "refl"  ≔ =_refl;
builtin "eqind" ≔ =_ind;


// THEORIES


// Booleans

inductive boolean : TYPE ≔
| True : boolean
| False : boolean;

symbol Dboolean : Type;
rule tEv Dboolean ↪ boolean;

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

symbol rect_boolean :
  Π (Q : boolean → Kind),
  kEv (Q True) →
  kEv (Q False) →
  Π b, kEv(Q b);

rule rect_boolean _ $vT _   True  ↪ $vT
with rect_boolean _ _   $vF False ↪ $vF;

symbol is_True ≔
  rect_boolean (λ _, DType)
      ⊤
      ⊥;

symbol discr_False_True : tEv (¬ (False = True))
≔ begin assume H;
  have f : tEv (is_True False);
  rewrite H; refine tt;
  refine f ⊥;
end;

symbol eq_True_is_True b : tEv (b = True ⇒ is_True b)
≔ begin
  induction;
  assume _; refine tt;
  assume f; refine discr_False_True f ⊥;
end;

symbol eq_False_not_is_True b : tEv (b = False ⇒ ¬ is_True b)
≔ begin assume b eb;
  rewrite eb; refine tt;
end;

// Comparison

inductive comparison : TYPE ≔
| Eq : comparison
| Lt : comparison
| Gt : comparison;

symbol Dcomparison : Type;
rule tEv Dcomparison ↪ comparison;

// symbol Dcomparison : Type;
// symbol comparison ≔ tEv Dcomparison;

// symbol Eq : comparison;
// symbol Lt : comparison;
// symbol Gt : comparison;

// symbol comp_ind :
//   tEv (`π Q : comparison → Type,
//        Q Eq ⇒
//        Q Lt ⇒
//        Q Gt ⇒
//        `∀ c : comparison, Q c) ≔ ind_comparison;

// rule comp_ind _ $vE _   _   Eq  ↪ $vE
// with comp_ind _ _   $vL _   Lt  ↪ $vL
// with comp_ind _ _   _   $vG Gt  ↪ $vG;

symbol rect_comparison :
  Π Q : comparison → Kind,
  kEv (Q Eq) →
  kEv (Q Lt) →
  kEv (Q Gt) →
  Π c, kEv (Q c);

rule rect_comparison _ $vE _   _   Eq  ↪ $vE
with rect_comparison _ _   $vL _   Lt  ↪ $vL
with rect_comparison _ _   _   $vG Gt  ↪ $vG;

symbol is_Eq ≔ rect_comparison (λ _, DType) ⊤ ⊥ ⊥;

symbol discr_Lt_Eq : tEv (¬ (Lt = Eq))
≔ begin assume H;
  have f : tEv (is_Eq Lt);
  rewrite H; refine tt;
  refine f ⊥;
end;

symbol discr_Gt_Eq : tEv (¬ (Gt = Eq))
≔ begin assume H;
  have f : tEv (is_Eq Gt);
  rewrite H; refine tt;
  refine f ⊥;
end;

symbol is_Lt ≔ rect_comparison (λ _, DType) ⊥ ⊤ ⊥;
symbol discr_Gt_Lt : tEv (¬ (Gt = Lt))
≔ begin assume H;
  have f : tEv (is_Lt Gt);
  rewrite H; refine tt;
  refine f ⊥;
end;

symbol CompOpp ≔
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

// symbol Dpositive : Type;
// symbol positive ≔ tEv Dpositive;

// symbol xI : positive → positive;
// symbol xO : positive → positive;
// symbol xH : positive;

// symbol pos_ind :
//   tEv (`π Q : positive → Type,
//        (`∀ p : positive, Q p ⇒ Q (xI p)) ⇒
//        (`∀ p : positive, Q p ⇒ Q (xO p)) ⇒
//        Q xH ⇒
//        `∀ p : positive, Q p) ≔ ind_positive;

// rule pos_ind _  _   _   $vH xH      ↪ $vH
// with pos_ind $Q $vI $vO $vH (xI $p) ↪ $vI $p (pos_ind $Q $vI $vO $vH $p)
// with pos_ind $Q $vI $vO $vH (xO $p) ↪ $vO $p (pos_ind $Q $vI $vO $vH $p);

symbol pos_succ ≔
  ind_positive (λ _, Dpositive)
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

symbol ind_positive_peano :
   tEv (`π Q : positive → Type,
        Q xH ⇒
        (`∀ p, Q p ⇒ Q (pos_succ p)) ⇒
        `∀ p, Q p)
≔ begin
  assume Q qH qS p;

  refine ind_positive (λ p, `π P, P xH ⇒ (`∀ x, P x ⇒ P (pos_succ x)) ⇒ P p)
                 _ _ _ p Q qH qS;
  assume q rec_q P pH pS;
  rewrite left pos_succ_xO;
  refine pS (xO q) _;
  refine rec_q (λ p, P (xO p)) (pS xH pH) _;
  assume x p2x;
  rewrite left pos_succ_xI;
  refine pS (pos_succ (xO x)) _;
  refine pS (xO x) p2x;

  assume q rec_q P pH pS;
  refine rec_q (λ p, P (xO p)) (pS xH pH) _;
  assume x p2x;
  rewrite left pos_succ_xI;
  refine pS (pos_succ (xO x)) _;
  refine pS (xO x) p2x;

  assume P pH pS;
  refine pH;
end;


symbol pos_add_carry ≔
  ind_positive (λ _, Dpositive ⇒ Dboolean ⇒ Dpositive)
    (λ p ac_p y b, ind_positive (λ _, Dpositive)
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
    (λ p ac_p y b, ind_positive (λ _, Dpositive)
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
    (λ y b, ind_positive (λ _, Dpositive)
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

symbol pa_xH y : tEv (pos_add xH y = pos_succ y)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pa_xH_right y : tEv (pos_add y xH = pos_succ y)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pac_succ x : tEv (`∀ y, pos_add_carry x y True = pos_succ (pos_add x y))
≔ begin
  induction;
  assume p prec y;
  refine ind_positive (λ y, pos_add_carry (xI p) y True = pos_succ (pos_add (xI p) y)) _ _ _ y;
  assume q _; reflexivity;
  assume q _;
  have e : tEv (pos_add_carry (xI p) (xO q) True = xO (pos_add_carry p q True));
  reflexivity; rewrite e; rewrite prec; reflexivity;
  reflexivity;
  assume p prec y;
  refine ind_positive (λ y, pos_add_carry (xO p) y True = pos_succ (pos_add (xO p) y)) _ _ _ y;
  assume q _;
  have e : tEv (pos_add_carry (xO p) (xI q) True = xO (pos_add_carry p q True));
  reflexivity; rewrite e; rewrite prec; reflexivity;
  assume q _; reflexivity;
  reflexivity;
  refine ind_positive (λ y, pos_add_carry xH y True = pos_succ (pos_add xH y)) _ _ _;
  assume y _; reflexivity;
  assume y _; reflexivity;
  reflexivity;
end;

symbol pa_succ x y : tEv (pos_add (pos_succ x) y = pos_succ (pos_add x y))
≔ begin
  induction;
  assume p prec;
  induction;
  assume q _;
  have e : tEv (pos_add (pos_succ (xI p)) (xI q) = xI (pos_add (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec;
  rewrite left pac_succ;
  reflexivity;
  assume q _;
  have e : tEv (pos_add (pos_succ (xI p)) (xO q) = xO (pos_add (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec; reflexivity;
  reflexivity;

  assume p prec;
  induction;
  assume q _;
  have e : tEv (pos_add (pos_succ (xO p)) (xI q) = xO (pos_add_carry p q True));
  reflexivity; rewrite e;
  rewrite pac_succ; reflexivity;
  reflexivity;
  reflexivity;

  induction;
  assume q _;
  have e : tEv (pos_add (pos_succ xH) (xI q) = xI (pos_add xH q));
  reflexivity; rewrite e;
  rewrite pa_xH; reflexivity;
  assume q _;
  have e : tEv (pos_add (pos_succ xH) (xO q) = xO (pos_add xH q));
  reflexivity; rewrite e;
  rewrite pa_xH; reflexivity;
  reflexivity;
end;

symbol pa_assoc x y z : tEv (pos_add (pos_add x y) z = pos_add x (pos_add y z))
≔ begin
  refine ind_positive_peano (λ x, `∀ y, `∀ z, pos_add (pos_add x y) z = pos_add x (pos_add y z)) _ _;
  assume y z;
  rewrite pa_xH;
  rewrite pa_xH;
  rewrite pa_succ;
  reflexivity;

  assume p prec y z;
  rewrite pa_succ;
  rewrite pa_succ;
  rewrite pa_succ;
  rewrite prec;
  reflexivity;
end;

symbol pa_succ_right x y : tEv (pos_add x (pos_succ y) = pos_succ (pos_add x y))
≔ begin
  assume x y;
  refine ind_positive_peano (λ x, pos_add x (pos_succ y) = pos_succ (pos_add x y)) _ _ x;
  rewrite pa_xH; rewrite pa_xH; reflexivity;

  assume p prec;
  rewrite pa_succ;
  rewrite pa_succ;
  rewrite prec;
  reflexivity;
end;

symbol pa_comm x y : tEv (pos_add x y = pos_add y x)
≔ begin
  refine ind_positive_peano (λ x, `∀ y, pos_add x y = pos_add y x) _ _;
  assume y; rewrite pa_xH; rewrite pa_xH_right;
  reflexivity;

  assume p prec y;
  rewrite pa_succ;
  rewrite pa_succ_right;
  rewrite prec;
  reflexivity;
end;

// Check that 7 + 5 = 12
// assert ⊢ pos_add (xI (xI xH)) (xI (xO xH)) ≡ xO (xO (xI xH));

// Check that 110101010 + 101101100 ≡ 1100010110 in base 2 (426 + 364 ≡ 790)
// assert ⊢ pos_add (xO (xI (xO (xI (xO (xI (xO (xI xH)))))))) (xO (xO (xI (xI (xO (xI (xI (xO xH)))))))) ≡ (xO (xI (xI (xO (xI (xO (xO (xO (xI xH)))))))));

symbol pos_mul x y ≔
  ind_positive (λ _, Dpositive)
     (λ _ mul_p_y, pos_add y (xO mul_p_y))
     (λ _ mul_p_y, xO mul_p_y)
     y
     x;

// Check that 6 * 5 = 30
// assert ⊢ pos_mul (xO (xI xH)) (xI (xO xH)) ≡ xO (xI (xI (xI xH)));

symbol pos_pred_double ≔
  ind_positive (λ _, Dpositive)
     (λ p _, xI (xO p))
     (λ _ pos_pred_double_p, xI pos_pred_double_p)
     xH;

// Check that 2 * 6 - 1 ≡ 11
// assert ⊢ pos_pred_double (xO (xI xH)) ≡ xI (xI (xO xH));

symbol ppd_succ p : tEv (pos_pred_double (pos_succ p) = xI p)
≔ begin
  induction;
  assume p prec;
  have e : tEv (pos_pred_double (pos_succ (xI p)) = xI (pos_pred_double (pos_succ p)));
  reflexivity; rewrite e; rewrite prec; reflexivity;
  reflexivity;
  reflexivity;
end;

symbol succ_ppd p : tEv (pos_succ (pos_pred_double p) = xO p)
≔ begin
  induction;
  reflexivity;
  assume x xrec;
  have e : tEv (pos_succ (pos_pred_double (xO x)) = xO (pos_succ (pos_pred_double x)));
  reflexivity; rewrite e;
  rewrite xrec; reflexivity;
  reflexivity;
end;

symbol pos_compare_acc ≔
  ind_positive (λ _, Dcomparison ⇒ Dpositive ⇒ Dcomparison)
     (λ _ pca_p r, ind_positive (λ _, Dcomparison)
        (λ q _, pca_p r q)
        (λ q _, pca_p Gt q)
        Gt)
     (λ _ pca_p r, ind_positive (λ _, Dcomparison)
        (λ q _, pca_p Lt q)
        (λ q _, pca_p r q)
        Gt)
     (λ r, ind_positive (λ _, Dcomparison)
        (λ _ _, Lt)
        (λ _ _, Lt)
        r);

symbol pos_compare x y ≔ pos_compare_acc x Eq y;
symbol pc_def x y : tEv (pos_compare x y = pos_compare_acc x Eq y)
≔ begin assume x y; reflexivity; end;

symbol pos_compare' ≔
  ind_positive (λ _, Dpositive ⇒ Dcomparison)
     (λ _ pc'_p, ind_positive (λ _, Dcomparison)
        (λ q _, pc'_p q)
        (λ q _, ind_comparison (λ _, Dcomparison)
                         Gt
                         Lt
                         Gt
                         (pc'_p q))
        Gt)
     (λ _ pc'_p, ind_positive (λ _, Dcomparison)
        (λ q _, ind_comparison (λ _, Dcomparison)
                         Lt
                         Lt
                         Gt
                         (pc'_p q))
        (λ q _, pc'_p q)
        Gt)
     (ind_positive (λ _, Dcomparison)
              (λ _ _, Lt)
              (λ _ _, Lt)
              Eq);

symbol pca_comm x y r : tEv (
  pos_compare_acc x r y =
  CompOpp (pos_compare_acc y (CompOpp r) x))
≔ begin
  induction;

  assume p Hrec;
  induction;
  assume q _ r; refine Hrec q r;
  assume q _ r; refine Hrec q Gt;
  reflexivity;

  assume p Hrec;
  induction;
  assume q _ r; refine Hrec q Lt;
  assume q _ r; refine Hrec q r;
  reflexivity;

  induction;
  assume p _ r; reflexivity;
  assume p _ r; reflexivity;
  assume r; rewrite left [in pos_compare_acc xH r xH] compopp_idem;
  reflexivity;
end;

symbol pc_comm x y : tEv (pos_compare x y = CompOpp (pos_compare y x))
≔ begin
  assume x y;
  rewrite pc_def;
  rewrite pca_comm;
  reflexivity;
end;

symbol pc'_comm x y : tEv (pos_compare' x y = CompOpp (pos_compare' y x))
≔ begin
  induction;

  assume p prec;
  induction;
  // Case xI - xI
  assume q _; refine prec q;
  // Case xI - xO
  assume q _;
  have e1 : tEv (pos_compare' (xI p) (xO q) =
                 ind_comparison (λ _, Dcomparison) Gt Lt Gt (pos_compare' p q));
  reflexivity; rewrite e1;
  have e2 : tEv (pos_compare' (xO q) (xI p) =
                 ind_comparison (λ _, Dcomparison) Lt Lt Gt (pos_compare' q p));
  reflexivity; rewrite e2;
  rewrite prec;
  refine ind_comparison (λ c, ind_comparison (λ _, Dcomparison) Gt Lt Gt (CompOpp c) = CompOpp (ind_comparison (λ _, Dcomparison) Lt Lt Gt c)) _ _ _ (pos_compare' q p);
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
                 ind_comparison (λ _, Dcomparison) Lt Lt Gt (pos_compare' p q));
  reflexivity; rewrite e1;
  have e2 : tEv (pos_compare' (xI q) (xO p) =
                 ind_comparison (λ _, Dcomparison) Gt Lt Gt (pos_compare' q p));
  reflexivity; rewrite e2;
  rewrite prec;
  refine ind_comparison (λ c, ind_comparison (λ _, Dcomparison) Lt Lt Gt (CompOpp c) = CompOpp (ind_comparison (λ _, Dcomparison) Gt Lt Gt c)) _ _ _ (pos_compare' q p);
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
≔ begin assume x y;
  refine ind_comparison (λ p, pos_compare' x y = p ⇒ ¬ (ind_comparison (λ _, Dcomparison) Gt Lt Gt (pos_compare' x y) = Eq)) _ _ _ (pos_compare' x y) _;

  assume eq; rewrite eq; refine discr_Gt_Eq;

  assume eq; rewrite eq; refine discr_Lt_Eq;

  assume eq; rewrite eq; refine discr_Gt_Eq;

  reflexivity;
end;

symbol discr_pc'_xO_xI x y : tEv (¬ (pos_compare' (xO x) (xI y) = Eq))
≔ begin assume x y H;
  refine discr_pc'_xI_xO y x _;
  rewrite pc'_comm;
  rewrite H; reflexivity;
end;

symbol mod_left ≔
  ind_comparison (λ _, Dpositive ⇒ Dpositive)
      (λ p, p)
      xO
      xI;

symbol mod_right ≔
  ind_comparison (λ _, Dpositive ⇒ Dpositive)
      (λ p, p)
      xI
      xO;

symbol remove_mod_discr x y acc : tEv (
  ¬ (pos_compare' x y = Eq) ⇒
  pos_compare' (mod_left acc x) (mod_right acc y) = pos_compare' x y)
≔ begin assume x y acc;
  refine ind_comparison (λ c, pos_compare' x y = c ⇒ ¬ (c = Eq) ⇒ pos_compare' (mod_left acc x) (mod_right acc y) = c) _ _ _ (pos_compare' x y) _;
  assume _ f; refine f _ _; reflexivity;

  assume H _;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc x) (mod_right acc y) = Lt)
                  _ _ _ acc;
  refine H;
  have e : tEv (pos_compare' (mod_left Lt x) (mod_right Lt y) =
                ind_comparison (λ _, Dcomparison) Lt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  rewrite H; reflexivity;
  have e : tEv (pos_compare' (mod_left Gt x) (mod_right Gt y) =
                ind_comparison (λ _, Dcomparison) Gt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  rewrite H; reflexivity;

  assume H _;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc x) (mod_right acc y) = Gt)
                  _ _ _ acc;
  refine H;
  have e : tEv (pos_compare' (mod_left Lt x) (mod_right Lt y) =
                ind_comparison (λ _, Dcomparison) Lt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  rewrite H; reflexivity;

  have e : tEv (pos_compare' (mod_left Gt x) (mod_right Gt y) =
                ind_comparison (λ _, Dcomparison) Gt Lt Gt (pos_compare' x y));
  reflexivity; rewrite e;
  rewrite H; reflexivity;

  reflexivity;
end;

symbol remove_mod_xI_xO x y acc : tEv (
  pos_compare' (mod_left acc (xI x)) (mod_right acc (xO y)) =
  pos_compare' (xI x) (xO y))
≔ begin assume x y acc;
  refine remove_mod_discr (xI x) (xO y) acc _;
  refine discr_pc'_xI_xO x y;
end;

symbol remove_mod_xO_xI x y acc : tEv (
  pos_compare' (mod_left acc (xO x)) (mod_right acc (xI y)) =
  pos_compare' (xO x) (xI y))
≔ begin assume x y acc;
  refine remove_mod_discr (xO x) (xI y) acc _;
  refine discr_pc'_xO_xI x y;
end;

symbol pcc'_gen x y acc : tEv (
  pos_compare' (mod_left acc x) (mod_right acc y) = pos_compare_acc x acc y)
≔ begin
  induction;

  assume x xrec;
  induction;
  // xI - xI case
  assume q _ acc;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc (xI x)) (mod_right acc (xI q)) = pos_compare_acc (xI x) acc (xI q)) _ _ _ acc;
  refine xrec q Eq;
  refine xrec q Lt;
  refine xrec q Gt;
  // xI - xO case
  assume q _ acc;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc (xI x)) (mod_right acc (xO q)) = pos_compare_acc (xI x) acc (xO q)) _ _ _ acc;
  refine xrec q Gt;
  rewrite remove_mod_xI_xO;
  refine xrec q Gt;
  rewrite remove_mod_xI_xO;
  refine xrec q Gt;
  // xI - xH case
  assume acc;
  rewrite remove_mod_discr (xI x) xH acc _;
  refine discr_Gt_Eq;
  reflexivity;

  assume x xrec;
  induction;
  // xO - xI case
  assume q _ acc;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc (xO x)) (mod_right acc (xI q)) = pos_compare_acc (xO x) acc (xI q)) _ _ _ acc;
  refine xrec q Lt;
  rewrite remove_mod_xO_xI;
  refine xrec q Lt;
  rewrite remove_mod_xO_xI;
  refine xrec q Lt;
  // xO - xO case
  assume q _ acc;
  refine ind_comparison (λ acc, pos_compare' (mod_left acc (xO x)) (mod_right acc (xO q)) = pos_compare_acc (xO x) acc (xO q)) _ _ _ acc;
  refine xrec q Eq;
  refine xrec q Lt;
  refine xrec q Gt;
  // xO - xH case
  assume acc;
  rewrite remove_mod_discr (xO x) xH acc _;
  refine discr_Gt_Eq;
  reflexivity;

  induction;
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
≔ begin assume x y;
  symmetry;
  refine pcc'_gen x y Eq;
end;

symbol pc'_xI x y : tEv (pos_compare' (xI x) y = Eq ⇒ `∃ q, y = xI q)
≔ begin assume x;
  induction;
  assume q _ _ a b; refine b q _; reflexivity;
  assume q _ H;
  refine discr_pc'_xI_xO x q H (`∃ q0, xO q = xI q0);
  assume H;
  refine discr_Gt_Eq H (`∃ q, xH = xI q);
end;

symbol pc'_xO x y : tEv (pos_compare' (xO x) y = Eq ⇒ `∃ q, y = xO q)
≔ begin assume x;
  induction;
  assume q _ H;
  refine discr_pc'_xO_xI x q H (`∃ q0, xI q = xO q0);
  assume q _ _ a b; refine b q _; reflexivity;
  assume H;
  refine discr_Gt_Eq H (`∃ q, xH = xO q);
end;

symbol pc'_xH y : tEv (pos_compare' xH y = Eq ⇒ xH = y)
≔ begin
  induction;
  assume q _ H;
  refine discr_Lt_Eq H _;
  assume q _ H;
  refine discr_Lt_Eq H _;
  assume _; reflexivity;
end;

symbol pc'_decides : tEv (`∀ x, `∀ y, pos_compare' x y = Eq ⇒ x = y)
≔ begin
  induction;

  assume p prec q H;
  refine pc'_xI p q H _ (λ q' Hq', _);
  rewrite Hq';
  have H1 : tEv (pos_compare' (xI p) q = Eq); refine H;
  generalize H1; refine fold_arrow _; rewrite Hq';
  assume H1; rewrite prec q' H1;
  reflexivity;

  assume p prec q H;
  refine pc'_xO p q H _ (λ q' Hq', _);
  rewrite Hq';
  have H1 : tEv (pos_compare' (xO p) q = Eq); refine H;
  generalize H1; refine fold_arrow _; rewrite Hq';
  assume H1; rewrite prec q' H1;
  reflexivity;

  refine pc'_xH;
end;

symbol pc_decides : tEv (`∀ x, `∀ y, pos_compare x y = Eq ⇒ x = y)
≔ begin
  assume x y;
  rewrite pcc';
  refine pc'_decides x y;
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
≔ begin assume acc;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_succ_xH acc x : tEv (pos_compare_acc (pos_succ x) acc xH = Gt)
≔ begin assume acc;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol pca_succ_Lt x y : tEv (
  pos_compare_acc (pos_succ x) Lt y = pos_compare_acc x Gt y)
≔ begin
  induction;
  assume p prec;
  induction;
  // Case xI - xI
  assume q _; refine prec q;
  // Case xI - xO
  assume q _; refine prec q;
  // Case xI - xH
  reflexivity;

  assume p _;
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

symbol pca_Gt_succ x y : tEv (
  pos_compare_acc x Gt (pos_succ y) = pos_compare_acc x Lt y)
≔ begin
  assume x y;
  rewrite pca_comm;
  rewrite [pos_compare_acc x Lt y] pca_comm;
  have e : tEv (CompOpp Gt = Lt);
  reflexivity; rewrite e;
  rewrite pca_succ_Lt y x;
  reflexivity;
end;

symbol pca_succ_succ x y acc :
  tEv (pos_compare_acc (pos_succ x) acc (pos_succ y) = pos_compare_acc x acc y)
≔ begin
  induction;

  assume p prec;
  induction;
  // Case xI - xI
  assume q _ acc; refine prec q acc;
  // Case xI - xO
  assume q _ acc; refine pca_succ_Lt p q;
  // Case xI - xH
  assume acc; refine pca_succ_xH acc p;

  assume p prec;
  induction;
  // Case xO - xI
  assume q _ acc; refine pca_Gt_succ p q;
  // Case xO - xO
  assume q _ acc; reflexivity;
  // Case xO - xH
  assume acc; refine pca_Gt_xH p;

  induction;
  // Case xH - xI
  assume q _ acc; refine pca_xH_succ acc q;
  // Case xH - xO
  assume q _ acc; refine pca_xH_Lt q;
  // Case xH - xH
  reflexivity;
end;

symbol pc'_succ_succ x y : tEv (
  pos_compare' (pos_succ x) (pos_succ y) = pos_compare' x y)
≔ begin assume x y;
  rewrite left pcc';
  rewrite left pcc';
  refine pca_succ_succ x y Eq;
end;

symbol pc'_compat_add x y a : tEv (
  pos_compare' (pos_add x a) (pos_add y a) = pos_compare' x y)
≔ begin assume x y;
  refine ind_positive_peano (λ a, pos_compare' (pos_add x a) (pos_add y a) = pos_compare' x y) _ _;
  rewrite pa_xH_right;
  rewrite pa_xH_right;
  refine pc'_succ_succ x y;

  assume p prec;
  rewrite pa_succ_right;
  rewrite pa_succ_right;
  rewrite pc'_succ_succ;
  refine prec;
end;

symbol pc'_add_Gt x y : tEv (pos_compare' (pos_add x y) x = Gt)
≔ begin
  refine ind_positive_peano (λ x, `∀ y, pos_compare' (pos_add x y) x = Gt) _ _ ;
  assume y; rewrite pa_xH; rewrite left pcc';
  refine pca_succ_xH Eq y;

  assume x xrec y;
  rewrite pa_succ;
  rewrite pc'_succ_succ;
  refine xrec y;
end;

// Integers

inductive Z : TYPE ≔
| Z0 : Z
| Zpos : positive → Z
| Zneg : positive → Z;

symbol DZ : Type;
rule tEv DZ ↪ Z;

// symbol DZ : Type;
// symbol Z ≔ tEv DZ;

// symbol Z0 : Z;
// symbol Zpos : positive → Z;
// symbol Zneg : positive → Z;

// symbol Z_ind :
//   tEv (`π Q : Z → Type,
//        Q Z0 ⇒
//        (`∀ p : positive, Q (Zpos p)) ⇒
//        (`∀ p : positive, Q (Zneg p)) ⇒
//        `∀ z : Z, Q z) ≔ ind_Z;

// rule Z_ind _ $v0 _     _     Z0        ↪ $v0
// with Z_ind _ _   $vpos _     (Zpos $x) ↪ $vpos $x
// with Z_ind _ _   _     $vneg (Zneg $x) ↪ $vneg $x;

symbol zero ≔ Z0;
symbol one ≔ Zpos xH;

symbol ~ ≔
  ind_Z (λ _, DZ)
     zero
     (λ x, Zneg x)
     (λ x, Zpos x);
notation ~ prefix 44;

symbol double ≔
  ind_Z (λ _, DZ)
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
  ind_Z (λ _, DZ)
    one
    (λ p, Zpos (xI p))
    (λ p, Zneg (pos_pred_double p));

// Check that 2 * (-5) + 1 ≡ -9 and that 2 * 5 + 1 ≡ 11
// assert ⊢ succ_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xO (xO xH)));
// assert ⊢ succ_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xI (xO xH)));

symbol pred_double ≔
  ind_Z (λ _, DZ)
    (Zneg xH)
    (λ p, Zpos (pos_pred_double p))
    (λ p, Zneg (xI p));

// Check that 2 * (-5) - 1 ≡ -11 and that 2 * 5 - 1 ≡ 9
// assert ⊢ pred_double (Zneg (xI (xO xH))) ≡ Zneg (xI (xI (xO xH)));
// assert ⊢ pred_double (Zpos (xI (xO xH))) ≡ Zpos (xI (xO (xO xH)));

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

symbol pos_sub ≔
  ind_positive (λ _, Dpositive ⇒ DZ)
     (λ p pos_sub_p, ind_positive (λ _, DZ)
        (λ q _, double (pos_sub_p q))
        (λ q _, succ_double (pos_sub_p q))
        (Zpos (xO p)))
     (λ p pos_sub_p, ind_positive (λ _, DZ)
        (λ q _, pred_double (pos_sub_p q))
        (λ q _, double (pos_sub_p q))
        (Zpos (pos_pred_double p)))
     (ind_positive (λ _, DZ)
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
  induction;
  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xI a) (xI b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left double_opp;
  rewrite arec; reflexivity;
  assume b _;
  have e : tEv (pos_sub (xI a) (xO b) = succ_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left pred_double_opp;
  rewrite arec; reflexivity;
  reflexivity;

  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xO a) (xI b) = pred_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left succ_double_opp;
  rewrite arec; reflexivity;
  assume b _;
  have e : tEv (pos_sub (xO a) (xO b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite left double_opp;
  rewrite arec; reflexivity;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol + x y ≔
  ind_Z (λ _, DZ)
    y
    (λ x', ind_Z (λ _, DZ)
       x
       (λ y', Zpos (pos_add x' y'))
       (λ y', pos_sub x' y')
       y)
    (λ x', ind_Z (λ _, DZ)
       x
       (λ y', pos_sub y' x')
       (λ y', Zneg (pos_add x' y'))
       y)
    x;
notation + infix left 40;

symbol add_comm x y : tEv (x + y = y + x)
≔ begin
  induction;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  assume y; have e : tEv (Zpos x + Zpos y = Zpos (pos_add x y));
  reflexivity; rewrite e;
  rewrite pa_comm; reflexivity;
  reflexivity;

  assume x;
  induction;
  reflexivity;
  reflexivity;
  assume y; have e : tEv (Zneg x + Zneg y = Zneg (pos_add x y));
  reflexivity; rewrite e;
  rewrite pa_comm; reflexivity;
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

symbol succ_def x : tEv (succ x = x + one)
≔ begin reflexivity; end;

symbol pd_succ x : tEv (pred_double (succ x) = succ_double x)
≔ begin
  induction;
  reflexivity;
  assume x;
  have e : tEv (pred_double (succ (Zpos x)) = Zpos (pos_pred_double (pos_add x xH)));
  reflexivity; rewrite e;
  rewrite pa_xH_right;
  rewrite ppd_succ;
  reflexivity;
  induction;
  assume p _;
  reflexivity;
  assume p _;
  reflexivity;
  reflexivity;
end;

symbol succ_pd x : tEv (succ (pred_double x) = double x)
≔ begin
  induction;
  reflexivity;
  assume x;
  have e : tEv (succ (pred_double (Zpos x)) = Zpos (pos_add (pos_pred_double x) xH));
  reflexivity; rewrite e;
  rewrite pa_xH_right;
  rewrite succ_ppd;
  reflexivity;
  reflexivity;
end;

symbol d_succ x : tEv (double (succ x) = succ (succ_double x))
≔ begin
  induction;
  reflexivity;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol succ_d x : tEv (succ (double x) = succ_double x)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

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
  ind_Z (λ _, DZ)
     zero
     (λ x', ind_Z (λ _, DZ)
        zero
        (λ y', Zpos (pos_mul x' y'))
        (λ y', Zneg (pos_mul x' y'))
        y)
     (λ x', ind_Z (λ _, DZ)
        zero
        (λ y', Zneg (pos_mul x' y'))
        (λ y', Zpos (pos_mul x' y'))
        y)
     x;
notation * infix right 42;

symbol distr_opp x y : tEv (~ (x + y) = ~ x + ~ y)
≔ begin
  induction;
  reflexivity;

  assume p; induction;
  reflexivity;
  reflexivity;
  assume q; refine ps_opp p q;

  assume p; induction;
  reflexivity;
  assume q; refine ps_opp q p;
  reflexivity;
end;

symbol ps_succ x y : tEv (pos_sub (pos_succ x) y = succ (pos_sub x y))
≔ begin
  induction;
  assume p prec;
  induction;
  // Case xI - xI
  assume q _;
  have e : tEv (pos_sub (pos_succ (xI p)) (xI q) = pred_double (pos_sub (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec; rewrite pd_succ;
  rewrite left succ_d;
  reflexivity;
  // Case xI - xO
  assume q _;
  have e : tEv (pos_sub (pos_succ (xI p)) (xO q) = double (pos_sub (pos_succ p) q));
  reflexivity; rewrite e;
  rewrite prec; rewrite d_succ;
  reflexivity;
  // Case xI - xH
  have e : tEv (pos_sub (pos_succ (xI p)) xH = Zpos (pos_pred_double (pos_succ p)));
  reflexivity; rewrite e;
  rewrite ppd_succ;
  reflexivity;

  assume p prec;
  induction;
  // Case xO - xI
  assume q _;
  symmetry;
  refine succ_pd (pos_sub p q);
  // Case xO - xO
  assume q _;
  symmetry;
  refine succ_d (pos_sub p q);
  // Case xO - xH
  have e : tEv (succ (pos_sub (xO p) xH) = Zpos (pos_add (pos_pred_double p) xH));
  reflexivity; rewrite e;
  rewrite pa_xH_right; rewrite succ_ppd;
  reflexivity;

  induction;
  // Case xH - xI
  assume q _; generalize q; induction;
  reflexivity;
  reflexivity;
  reflexivity;
  // Case xH - xO
  assume q _; generalize q; induction;
  reflexivity;
  reflexivity;
  reflexivity;
  // Case xH - xH
  reflexivity;
end;

symbol ps_Zpos a b c : tEv (pos_sub a b + Zpos c = pos_sub (pos_add a c) b)
≔ begin assume a b c;
  refine ind_positive_peano (λ c, (pos_sub a b + Zpos c) = pos_sub (pos_add a c) b) _ _ c;
  rewrite pa_xH_right;
  rewrite ps_succ; reflexivity;

  assume p prec;
  rewrite pa_succ_right; rewrite ps_succ;
  rewrite left prec;
  have e : tEv (Zpos (pos_succ p) = succ (Zpos p));
  rewrite left pa_xH_right; reflexivity; rewrite e;
  refine ind_Z (λ x, x + succ (Zpos p) = succ (x + Zpos p)) _ _ _ (pos_sub a b);
  reflexivity;
  assume q;
  have e2 : tEv (Zpos q + succ (Zpos p) = Zpos (pos_add q (pos_add p xH)));
  reflexivity; rewrite e2;
  rewrite pa_comm;
  rewrite pa_xH_right;
  rewrite pa_succ;
  rewrite left pa_xH_right;
  rewrite [pos_add p q] pa_comm;
  reflexivity;
  assume q;
  have e2 : tEv (Zneg q + Zpos p = pos_sub p q);
  reflexivity; rewrite e2;
  rewrite left ps_succ;
  rewrite left pa_xH_right;
  reflexivity;
end;

symbol ps_Zneg a b c : tEv (pos_sub a b + Zneg c = pos_sub a (pos_add b c))
≔ begin assume a b c;
  rewrite left ps_opp;
  have e : tEv (Zneg c = ~ Zpos c);
  reflexivity; rewrite e;
  rewrite left distr_opp;
  rewrite ps_Zpos;
  rewrite ps_opp;
  reflexivity;
end;

symbol add_assoc x y z : tEv (x + y + z = x + (y + z))
≔ begin
  induction;
  reflexivity;

  assume a; induction;
  reflexivity;

  assume b; induction;
  reflexivity;
  // Zpos - Zpos - Zpos case
  assume c;
  have e : tEv ((Zpos a + Zpos b) + Zpos c = Zpos (pos_add (pos_add a b) c));
  reflexivity; rewrite e; rewrite pa_assoc; reflexivity;
  // Zpos - Zpos - Zneg case
  assume c;
  symmetry; rewrite add_comm;
  rewrite [Zpos a + Zpos b] add_comm;
  refine ps_Zpos b c a;

  assume b; induction;
  rewrite add_Z0_right; rewrite add_Z0_right; reflexivity;
  // Zpos - Zneg - Zpos case
  assume c;
  have e : tEv (Zpos a + Zneg b = pos_sub a b);
  reflexivity; rewrite e;
  rewrite ps_Zpos a b c;
  rewrite pa_comm; symmetry;
  rewrite add_comm; refine ps_Zpos c b a;
  // Zpos - Zneg - Zpos case
  assume c;
  refine ps_Zneg a b c;

  assume a; induction;
  reflexivity;

  assume b; induction;
  rewrite add_Z0_right; rewrite add_Z0_right; reflexivity;
  // Zneg - Zpos - Zpos case
  assume c;
  refine ps_Zpos b a c;
  // Zneg - Zpos - Zneg case
  assume c;
  have e : tEv ((Zneg a + Zpos b) + Zneg c = pos_sub b a + Zneg c);
  reflexivity; rewrite e; rewrite ps_Zneg b a c;
  symmetry; rewrite pa_comm; rewrite add_comm;
  refine ps_Zneg b c a;

  assume b; induction;
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
  rewrite pa_assoc;
  reflexivity;
end;

symbol compare x y ≔
  ind_Z (λ _, Dcomparison)
     (ind_Z (λ _, Dcomparison)
         Eq
         (λ _, Lt)
         (λ _, Gt)
         y)
     (λ x', ind_Z (λ _, Dcomparison)
        Gt
        (λ y', pos_compare x' y')
        (λ _, Gt)
        y)
     (λ x', ind_Z (λ _, Dcomparison)
        Lt
        (λ _, Lt)
        (λ y', pos_compare y' x')
        y)
     x;

symbol c_decides x y : tEv (compare x y = Eq ⇒ x = y)
≔ begin
  induction;

  induction;
  reflexivity;
  assume y lteq;
  refine discr_Lt_Eq lteq _;
  assume y gteq;
  refine discr_Gt_Eq gteq _;

  assume x;
  induction;
  assume gteq;
  refine discr_Gt_Eq gteq _;
  assume y H;
  rewrite pc_decides x y H;
  reflexivity;
  assume y gteq;
  refine discr_Gt_Eq gteq _;

  assume x;
  induction;
  assume lteq;
  refine discr_Lt_Eq lteq _;
  assume y lteq;
  refine discr_Lt_Eq lteq _;
  assume y H;
  rewrite pc_decides y x H;
  reflexivity;
end;

symbol c_comm x y : tEv (compare x y = CompOpp (compare y x))
≔ begin
  induction;

  induction;
  reflexivity; reflexivity; reflexivity;

  assume x0;
  induction;
  reflexivity;
  assume x1; refine pc_comm x0 x1;
  reflexivity;

  assume x0;
  induction;
  reflexivity;
  reflexivity;
  assume x1; refine pc_comm x1 x0;
end;

symbol c_opp a b : tEv (compare (~ a) (~ b) = CompOpp (compare a b))
≔ begin
  induction;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;

  assume a;
  induction;
  reflexivity;
  assume b; refine pc_comm b a;
  reflexivity;

  assume a;
  induction;
  reflexivity;
  reflexivity;
  assume b; refine pc_comm a b;
end;

symbol c_double x : tEv (compare (double x) Z0 = compare x Z0)
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol c_pred_double x : tEv (
  compare (pred_double x) Z0 = ind_comparison (λ _, Dcomparison) Lt Lt Gt
                               (compare x Z0))
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol c_succ_double x : tEv (
  compare (succ_double x) Z0 = ind_comparison (λ _, Dcomparison) Gt Lt Gt
                               (compare x Z0))
≔ begin
  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol c_ps a b : tEv (compare (pos_sub a b) Z0 = pos_compare' a b)
≔ begin
  induction;
  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xI a) (xI b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite c_double; refine arec b;
  assume b _;
  have e : tEv (pos_sub (xI a) (xO b) = succ_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite c_succ_double;
  rewrite arec;
  reflexivity;
  reflexivity;

  assume a arec;
  induction;
  assume b _;
  have e : tEv (pos_sub (xO a) (xI b) = pred_double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite c_pred_double;
  rewrite arec;
  reflexivity;
  assume b _;
  have e : tEv (pos_sub (xO a) (xO b) = double (pos_sub a b));
  reflexivity; rewrite e;
  rewrite c_double;
  refine arec b;
  reflexivity;

  induction;
  reflexivity;
  reflexivity;
  reflexivity;
end;

symbol c_sub a b : tEv (compare a b = compare (a - b) Z0)
≔ begin
  induction;
  induction;
  reflexivity;
  reflexivity;
  reflexivity;

  assume a;
  induction;
  reflexivity;
  assume b;
  have e : tEv (compare (Zpos a) (Zpos b) = pos_compare a b);
  reflexivity; rewrite e;
  rewrite pcc';
  symmetry; refine c_ps a b;
  assume b;
  reflexivity;

  assume a;
  induction;
  reflexivity;
  reflexivity;
  assume b;
  have e : tEv (compare (Zneg a) (Zneg b) = pos_compare b a);
  reflexivity; rewrite e;
  rewrite pcc';
  symmetry; refine c_ps b a;
end;

symbol c_Zpos_add a b :
  tEv (compare (Zpos (pos_add a b)) (Zpos a) = Gt)
≔ begin assume a b;
  have e : tEv (compare (Zpos (pos_add a b)) (Zpos a) = pos_compare (pos_add a b) a);
  reflexivity; rewrite e; rewrite pcc';
  refine pc'_add_Gt a b;
end;

symbol c_compat_add a b c : tEv (compare a b = compare (a + c) (b + c))
≔ begin assume a b c;
  rewrite [x in x = _] c_sub;
  rewrite [x in _ = x] c_sub;
  rewrite [(a + c) - (b + c)] sub_def;
  rewrite distr_opp;
  rewrite add_assoc;
  rewrite [~ b + ~ c] add_comm;
  rewrite left add_assoc c;
  rewrite left sub_def c;
  rewrite add_opp;
  reflexivity;
end;

symbol leb x y ≔
  ind_comparison (λ _, Dboolean)
      True
      True
      False
      (compare x y);
symbol leb_def x y : tEv (leb x y = (ind_comparison (λ _, Dboolean) True True False (compare x y)))
≔ begin reflexivity; end;

symbol ltb x y ≔
  ind_comparison (λ _, Dboolean)
      False
      True
      False
      (compare x y);
symbol ltb_def x y : tEv (ltb x y = (ind_comparison (λ _, Dboolean) False True False (compare x y)))
≔ begin reflexivity; end;

symbol geb x y ≔
  ind_comparison (λ _, Dboolean)
      True
      False
      True
      (compare x y);
symbol geb_def x y : tEv (geb x y = (ind_comparison (λ _, Dboolean) True False True (compare x y)))
≔ begin reflexivity; end;

symbol gtb x y ≔
  ind_comparison (λ _, Dboolean)
      False
      False
      True
      (compare x y);
symbol gtb_def x y : tEv (gtb x y = (ind_comparison (λ _, Dboolean) False False True (compare x y)))
≔ begin reflexivity; end;

symbol ≤ x y ≔ is_True (leb x y);
notation ≤ infix 30;
symbol < x y ≔ is_True (ltb x y);
notation < infix 30;
symbol ≥ x y ≔ is_True (geb x y);
notation ≥ infix 30;
symbol > x y ≔ is_True (gtb x y);
notation > infix 30;

builtin "0"  ≔  zero;
builtin "+1" ≔  succ;

symbol Zpos_pos_succ a : tEv (Zpos (pos_succ a) = Zpos a + 1)
≔ begin
  induction;
  reflexivity; reflexivity; reflexivity;
end;

// assert ⊢ 3 < ~ 2 ≡ ⊥;
// assert ⊢ 3 < 3 ≡ ⊥;
// assert ⊢ 3 < 5 ≡ ⊤;

// assert ⊢ 4 ≥ ~ 3 ≡ ⊤;
// assert ⊢ 4 ≥ 4 ≡ ⊤;
// assert ⊢ 4 ≥ 7 ≡ ⊥;

symbol natlike_rec P : tEv (
  P 0 ⇒
  (`∀ z, 0 ≤ z ⇒ P z ⇒ P (z + 1)) ⇒
  `∀ z, 0 ≤ z ⇒ P z)
≔ begin assume P p0 prec z Hz;
  have posrec : tEv (`∀ p, P (Zpos p));
  refine ind_positive_peano (λ p, P (Zpos p)) _ _;
  refine prec 0 _ p0;
  refine tt;

  assume a ha;
  rewrite Zpos_pos_succ a;
  refine prec (Zpos a) _ ha;
  refine tt;

  refine ind_Z (λ z, 0 ≤ z ⇒ P z) _ _ _ z Hz;
  assume _; refine p0;
  assume p _; refine posrec p;
  assume p Hp; refine Hp (P (Zneg p));
end;

symbol simpl_right x a : tEv (x + a - a = x)
≔ begin assume x a;
  rewrite sub_def;
  rewrite add_assoc;
  rewrite left sub_def;
  rewrite add_opp;
  rewrite add_comm;
  reflexivity;
end;

symbol simpl_inv_right x a : tEv (x - a + a = x)
≔ begin assume x a;
  rewrite sub_def;
  rewrite add_assoc;
  rewrite [~ a + a] add_comm;
  // have e : Π u v, tEv (u - v = u + ~ v);
  // refine sub_def;
  // apply sub_def ? (apply almost never works)
  rewrite left sub_def;
  rewrite add_opp;
  rewrite add_comm;
  reflexivity;
end;

symbol le_compat_add x y a : tEv (x ≤ y) → tEv (x + a ≤ y + a)
≔ begin assume x y a;
  refine ind_comparison (λ c, compare x y = c ⇒ x ≤ y ⇒ x + a ≤ y + a) _ _ _ (compare x y) _;
  assume exy _;
  refine eq_True_is_True (leb (x + a) (y + a)) _;
  have e : tEv (compare (x + a) (y + a) = Eq);
  rewrite left c_compat_add; refine exy;
  rewrite leb_def; rewrite e; reflexivity;

  assume lxy _;
  refine eq_True_is_True (leb (x + a) (y + a)) _;
  have e : tEv (compare (x + a) (y + a) = Lt);
  rewrite left c_compat_add; refine lxy;
  rewrite leb_def; rewrite e; reflexivity;

  assume gxy H;
  refine eq_False_not_is_True (leb x y) _ H _;
  rewrite leb_def; rewrite gxy;
  reflexivity;

  reflexivity;
end;

symbol lt_compat_add x y a : tEv (x < y) → tEv (x + a < y + a)
≔ begin assume x y a;
  refine ind_comparison (λ c, compare x y = c ⇒ x < y ⇒ x + a < y + a) _ _ _ (compare x y) _;
  assume exy H;
  refine eq_False_not_is_True (ltb x y) _ H _;
  rewrite ltb_def; rewrite exy; reflexivity;

  assume lxy _;
  refine eq_True_is_True (ltb (x + a) (y + a)) _;
  have e : tEv (compare (x + a) (y + a) = Lt);
  rewrite left c_compat_add; refine lxy;
  rewrite ltb_def; rewrite e; reflexivity;

  assume gxy H;
  refine eq_False_not_is_True (ltb x y) _ H _;
  rewrite ltb_def; rewrite gxy; reflexivity;

  reflexivity;
end;

symbol le_add_compat x y a : tEv (x + a ≤ y + a) → tEv (x ≤ y)
≔ begin assume x y a leq;
  rewrite left simpl_right x a;
  rewrite left simpl_right y a;
  rewrite sub_def;
  rewrite sub_def;
  refine le_compat_add (x + a) (y + a) (~ a) leq;
end;

symbol lt_add_compat x y a : tEv (x + a < y + a) → tEv (x < y)
≔ begin assume x y a ltq;
  rewrite left simpl_right x a;
  rewrite left simpl_right y a;
  rewrite sub_def;
  rewrite sub_def;
  refine lt_compat_add (x + a) (y + a) (~ a) ltq;
end;

symbol case u bound : tEv (u ≤ bound) → tEv (bound = u ∨ u < bound)
≔ begin assume u z luz;
  refine ind_comparison (λ c, compare u z = c ⇒ z = u ∨ u < z) _ _ _ (compare u z) _;
  assume euz; refine Left (z = u) (u < z) _;
  symmetry;
  refine c_decides u z euz;

  assume ltuz; refine Right (z = u) (u < z) _;
  refine eq_True_is_True (ltb u z) _;
  rewrite ltb_def; rewrite ltuz; reflexivity;

  assume gtuz;
  refine eq_False_not_is_True (leb u z) _ luz (z = u ∨ u < z);
  rewrite leb_def; rewrite gtuz; reflexivity;

  reflexivity;
end;

symbol lt_le_Z0 z : tEv (0 < succ z ⇒ 0 ≤ z)
≔ begin
  induction;
  assume _; refine tt;
  assume z _; refine tt;
  assume z f;
  generalize z;
  induction;
  assume x _ f;
  refine f ⊥;
  assume x _ f;
  refine f ⊥;
  assume f;
  refine f ⊥;
end;

symbol lt_le u z : tEv (u < succ z ⇒ u ≤ z)
≔ begin assume u z H;
  refine le_add_compat u z (~ u) _;
  rewrite left sub_def;
  rewrite left sub_def;
  rewrite add_opp;
  have e : tEv (0 < succ (z - u));
  refine lt_add_compat 0 (succ (z - u)) u _;
  rewrite succ_def;
  rewrite add_assoc;
  rewrite [one + u] add_comm;
  rewrite left add_assoc (z - u) u one;
  rewrite simpl_inv_right;
  refine H;
  refine lt_le_Z0 (z - u) e;
end;

symbol le_lt_Z0 z : tEv (0 ≤ z ⇒ 0 < succ z)
≔ begin
  induction;
  assume _; refine tt;
  assume z _; refine tt;
  assume z f;
  refine f (0 < succ (Zneg z));
end;

symbol le_lt u z : tEv (u ≤ z) → tEv (u < succ z)
≔ begin assume u z H;
  refine lt_add_compat u (succ z) (~ u) _;
  rewrite left sub_def;
  rewrite add_opp;
  rewrite succ_def;
  rewrite add_assoc;
  rewrite [one + ~ u] add_comm;
  rewrite left add_assoc;
  have e : tEv (0 ≤ z - u);
  refine le_add_compat 0 (z - u) u _;
  rewrite simpl_inv_right;
  refine H;
  refine le_lt_Z0 (z - u) e;
end;

symbol max (x y : Z)
≔ if DZ (leb x y) y x;

symbol max_def x y : tEv (max x y = if DZ (leb x y) y x)
≔ begin reflexivity; end;

symbol max_is_greater_1 x y : tEv (x ≤ max x y)
≔ begin assume x y;
  refine ind_boolean (λ b, leb x y = b ⇒ x ≤ max x y) _ _ (leb x y) _;
  assume lxy;
  rewrite max_def;
  rewrite lxy;
  refine eq_True_is_True (leb x y) lxy;

  assume nlxy;
  rewrite max_def;
  rewrite nlxy;
  refine le_add_compat x x (~ x) _;
  rewrite left sub_def;
  rewrite add_opp; refine tt;

  reflexivity;
end;

symbol max_is_greater_2 x y : tEv (y ≤ max x y)
≔ begin assume x y;
  refine ind_boolean (λ b, leb x y = b ⇒ y ≤ max x y) _ _ (leb x y) _;
  assume lxy;
  rewrite max_def;
  rewrite lxy;
  refine le_add_compat y y (~ y) _;
  rewrite left sub_def;
  rewrite add_opp; refine tt;

  assume nlxy; rewrite max_def; rewrite nlxy; generalize nlxy;
  refine ind_comparison (λ c, compare x y = c ⇒ leb x y = False ⇒ y ≤ x)
         _ _ _ (compare x y) _;
  assume eq; rewrite leb_def; rewrite eq;
  assume f;
  have e : tEv (False = True); symmetry; refine f;
  refine discr_False_True e _;

  assume lt; rewrite leb_def; rewrite lt;
  assume f;
  have e : tEv (False = True); symmetry; refine f;
  refine discr_False_True e _;

  assume gt _;
  have lt : tEv (CompOpp (compare x y) = CompOpp Gt);
  rewrite gt; reflexivity;
  generalize lt;
  have g : tEv (CompOpp (compare x y) = Lt ⇒ y ≤ x);
  rewrite left c_comm;
  assume lt;
  refine eq_True_is_True (leb y x) _;
  rewrite leb_def; rewrite lt; reflexivity;
  refine g;

  reflexivity;
  reflexivity;
end;

// Prove strong induction


symbol strong_bound_0_alt_rec P : tEv (
  (`∀ z, z ≤ 0 ⇒ P z) ⇒
  (`∀ z, 0 ≤ z ⇒ (`∀ v, v ≤ z ⇒ P v) ⇒ P (z + 1)) ⇒
   `∀ z, P z)
≔ begin assume P p0 prec;

  have q : tEv (`∀ z, 0 ≤ z ⇒ `∀ u, u ≤ z ⇒ P u);
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

symbol strong_induction a P : tEv (
  (`∀ x, x ≤ a ⇒ P x) ⇒
  (`∀ x, a < x ⇒ (`∀ v, v < x ⇒ P v) ⇒ P x) ⇒
   `∀ x, P x)
≔ begin assume a P p0 prec;

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


symbol ListDType : Kind;

symbol ∅ : kEv ListDType;

symbol ∙ : kEv (DType ⇀ ListDType ⇀ ListDType);
notation ∙ infix right 13;

symbol ⊧  : kEv (ListDType ⇀ ListDType ⇀ DType);
notation ⊧ infix 12;

symbol ⟹  ≔ @⇒;
notation ⟹  infix right 11;

rule $A ∙ $B ⊧ $C ↪ $A ⟹  $B ⊧ $C
with ∅ ⊧ $A ∙ $B  ↪ ¬ $A ⟹  ∅ ⊧ $B
with ∅ ⊧ ∅        ↪ ⊥;

// A task < t | x : t | H1 : A1, H2 : A2 ⊢ G : B > is encoded by
// <`π t : Type, ∀ x : t, tr A1 ∙ tr A2 ∙ ∅ ⊧ tr A ∙ ∅ >
// where < tr > is the function encoding terms


// KERNEL CERTIFICATE RULES

symbol Axiom A : tEv (
  A ∙ ∅ ⊧ A ∙ ∅)
≔ λ a na, na a;

symbol TrivialHyp : tEv (
  ⊥ ∙ ∅ ⊧ ∅)
≔ λ f, f;

symbol TrivialGoal : tEv (
  ∅ ⊧ ⊤ ∙ ∅)
≔ λ ntt, ntt tt;

symbol EqRefl T (t : tEv T) : tEv (
  ∅ ⊧ t = t ∙ ∅)
≔ λ neqtt, neqtt (=_refl T t);

symbol Assert A : tEv (
  ∅ ⊧ A ∙ ∅ ⟹
  A ∙ ∅ ⊧ ∅ ⟹
  ∅ ⊧ ∅)
≔ λ nna na, nna na;

symbol SplitHyp' A B : tEv (
  A ∙ ∅ ⊧ ∅ ⟹
  B ∙ ∅ ⊧ ∅ ⟹
  A ∨ B ∙ ∅ ⊧ ∅)
≔ begin assume A B s1 s2 H;
  refine DestructDisj A B ⊥ H s1 s2; end;
symbol SplitHyp A B H s1 s2 ≔ SplitHyp' A B s1 s2 H;

symbol SplitGoal' A B : tEv (
  ∅ ⊧ A ∙ ∅ ⟹
  ∅ ⊧ B ∙ ∅ ⟹
  ∅ ⊧ A ∧ B ∙ ∅)
≔ begin assume A B nna nnb;
  refine to_nn (A ∧ B) _; refine SplitConj A B _ _;
  refine from_nn A nna;
  refine from_nn B nnb;
end;
symbol SplitGoal A B H s1 s2 ≔ SplitGoal' A B s1 s2 H;

symbol UnfoldIffHyp' A B : tEv (
  (A ⇒ B) ∧ (B ⇒ A) ∙ ∅ ⊧ ∅ ⟹
  A ⇔ B ∙ ∅ ⊧ ∅)
≔ λ s, s;
symbol UnfoldIffHyp A B H s ≔ UnfoldIffHyp' A B s H;

symbol UnfoldIffGoal' A B : tEv (
  ∅ ⊧ (A ⇒ B) ∧ (B ⇒ A) ∙ ∅ ⟹
  ∅ ⊧ A ⇔ B ∙ ∅)
≔ λ s, s;
symbol UnfoldIffGoal A B H s ≔ UnfoldIffGoal' A B s H;

symbol UnfoldArrHyp' A B : tEv (
  ¬ A ∨ B ∙ ∅ ⊧ ∅ ⟹
  A ⇒ B ∙ ∅ ⊧ ∅)
≔ begin assume A B s ab;
  refine s _; refine Right (¬ A) B _; refine ab _;
  refine from_nn A _; assume na;
  refine s _; refine Left (¬ A) B _; refine na;
end;
symbol UnfoldArrHyp A B H s ≔ UnfoldArrHyp' A B s H;

symbol UnfoldArrGoal' A B : tEv (
  ∅ ⊧ ¬ A ∨ B ∙ ∅ ⟹
  ∅ ⊧ A ⇒ B ∙ ∅)
≔ begin assume A B s ab;
  refine ab _; assume a;
  refine DestructDisj (¬ A) B B (from_nn (¬ A ∨ B) s) _ _;
  assume na; refine na a _;
  refine λ x, x;
end;
symbol UnfoldArrGoal A B H s ≔ UnfoldArrGoal' A B s H;

symbol SwapHyp' A : tEv (
  ∅ ⊧ ¬ A ∙ ∅ ⟹
  A ∙ ∅ ⊧ ∅)
≔ λ nnna, from_nn (¬ A) nnna;
symbol SwapHyp A H s ≔ SwapHyp' A s H;

symbol SwapGoal' A : tEv (
  ¬ A ∙ ∅ ⊧ ∅ ⟹
  ∅ ⊧ A ∙ ∅)
≔ λ s, s;
symbol SwapGoal A H s ≔ SwapGoal' A s H;

symbol DestructHyp' A B : tEv (
  A ∙ B ∙ ∅ ⊧ ∅ ⟹
  A ∧ B ∙ ∅ ⊧ ∅)
≔ begin assume A B s ab;
  refine DestructConj A B ⊥ ab s;
end;
symbol DestructHyp A B H s ≔ DestructHyp' A B s H;

symbol DestructGoal' A B : tEv (
  ∅ ⊧ A ∙ B ∙ ∅ ⟹
  ∅ ⊧ A ∨ B ∙ ∅)
≔ begin assume A B s ab;
  refine s _ _;
  assume a; refine ab _; refine Left A B _; refine a;
  assume b; refine ab _; refine Right A B _; refine b;
end;
symbol DestructGoal A B H s ≔ DestructGoal' A B s H;

symbol ClearHyp' A : tEv (
  ∅ ⊧ ∅ ⟹
  A ∙ ∅ ⊧ ∅)
≔ λ f _, f;
symbol ClearHyp A HA s ≔ ClearHyp' A s HA;

symbol ClearGoal' A : tEv (
  ∅ ⊧ ∅ ⟹
  ∅ ⊧ A ∙ ∅)
≔ λ f _, f;
symbol ClearGoal A HA s ≔ ClearGoal' A s HA;

symbol Forget : tEv (
  ∅ ⊧ ∅ ⟹
  ∅ ⊧ ∅)
≔ λ f, f;

symbol IntroQuantHyp' T (P : tEv T → Type) : tEv (
  (`∀ x, P x ∙ ∅ ⊧ ∅) ⟹
  (`∃ x, P x) ∙ ∅ ⊧ ∅)
≔ begin assume T P s ep; refine ep ⊥ s; end;
symbol IntroQuantHyp {T} P H s ≔ IntroQuantHyp' T P s H;

symbol IntroQuantGoal' T (P : tEv T → Type) : tEv (
  (`∀ x, ∅ ⊧ P x ∙ ∅) ⟹
  ∅ ⊧ (`∀ x, P x) ∙ ∅)
≔ λ s nfp, nfp (λ t, from_nn (P t) (s t));
symbol IntroQuantGoal {T} P H s ≔ IntroQuantGoal' T P s H;

symbol InstQuantHyp' T (P : tEv T → Type) t : tEv (
  (`∀ x, P x) ∙ P t ∙ ∅ ⊧ ∅ ⟹
  (`∀ x, P x) ∙ ∅ ⊧ ∅)
≔ λ s h, s h (h t);
symbol InstQuantHyp {T} P t H s ≔ InstQuantHyp' T P t s H;

symbol InstQuantGoal' T (P : tEv T → Type) t : tEv (
  ∅ ⊧ (`∃ x, P x) ∙ P t ∙ ∅ ⟹
  ∅ ⊧ (`∃ x, P x) ∙ ∅)
≔ begin assume T P t s nep;
  refine nep _;
  assume C f;
  refine f t (from_nn (P t) (s nep));
end;
symbol InstQuantGoal {T} P t H s ≔ InstQuantGoal' T P t s H;

symbol RewriteHyp' T a b (P : tEv T → Type) : tEv (
  a = b ∙ P b ∙ ∅ ⊧ ∅ ⟹
  a = b ∙ P a ∙ ∅ ⊧ ∅)
≔ begin
  assume T a b P s eq pa;
  refine s eq _;
  rewrite left eq;
  refine pa;
end;
symbol RewriteHyp {T} a b P eab pa s ≔ RewriteHyp' T a b P s eab pa;

symbol RewriteGoal' T a b (P : tEv T → Type) : tEv (
  a = b ∙ ∅ ⊧ P b ∙ ∅ ⟹
  a = b ∙ ∅ ⊧ P a ∙ ∅)
≔ begin
  assume T a b P s eq pa;
  refine s eq _;
  rewrite left eq;
  refine pa;
end;
symbol RewriteGoal {T} a b P eab pa s ≔ RewriteGoal' T a b P s eab pa;

symbol RewriteFmlaHyp' A B P : tEv (
  A ⇔ B ∙ P B ∙ ∅ ⊧ ∅ ⟹
  A ⇔ B ∙ P A ∙ ∅ ⊧ ∅)
≔ λ s eab pa, s eab (iff_eq A B eab (λ x, P x) pa);
symbol RewriteFmlaHyp a b P eab pa s ≔ RewriteFmlaHyp' a b P s eab pa;

symbol RewriteFmlaGoal' A B P : tEv (
  (A ⇔ B) ∙ ∅ ⊧ P B ∙ ∅ ⟹
  (A ⇔ B) ∙ ∅ ⊧ P A ∙ ∅)
≔ λ s eab pa, s eab (iff_eq A B eab (λ x, ¬ P x) pa);
symbol RewriteFmlaGoal a b P eab pa s ≔ RewriteFmlaGoal' a b P s eab pa;

symbol Induction' a P : tEv (
  (`∀ x, x ≤ a ∙ ∅ ⊧ P x ∙ ∅) ⟹
  (`∀ x, a < x ∙ (`∀ n : Z, n < x ⇒ P n) ∙ ∅ ⊧ P x ∙ ∅) ⟹
  `∀ x, ∅ ⊧ P x ∙ ∅)
≔ begin
  assume a P pbase prec x;
  refine to_nn (P x) _;
  refine strong_induction a P _ _ x;
  assume z Hz;
  refine from_nn (P z) _;
  refine pbase z Hz;

  assume z Ha Hrec;
  refine from_nn (P z) _;
  refine prec z Ha Hrec;
end;
symbol Induction a P x H s1 s2 ≔ Induction' a P s1 s2 x H;


// COMPATIBILITY WITH IDENTIFIERS FROM Why3

symbol int ≔ DZ;
symbol bool ≔ Dboolean;

// symbol True ≔ True;
// symbol False ≔ False;

symbol infixspeq ≔ @=;

symbol infixsppl ≔ @+;
symbol infixspas ≔ @*;
symbol infixspmn ≔ @-;
symbol prefixspmn ≔ @~;

symbol infixsplseq ≔ @≤;
symbol infixspls ≔ @<;
symbol infixspgteq ≔ @≥;
symbol infixspgt ≔ @>;

// Also targeted, but not from an ident : quantifications and arrows, ⊤, ⊥, ¬,
// ∧, ∨, ⇒, ⇔, ~, Z, boolean, DType, Type, int litterals
