

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

symbol ¬ A ≔  A ⇒ false;
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

symbol =_ind T (x y : tEv T) : tEv (x = y) → Π P, tEv (P y) → tEv (P x);

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

// TODO : understand this
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

symbol True_eq_False_exfalso F : tEv (False = True) → tEv F
≔ begin
  assume F H;
  have H2 : tEv (is_True False);
  rewrite H; refine tt;
  refine H2 _;
end;

symbol is_True_eq_True b : tEv (is_True b) → tEv (b = True)
≔ begin
  induction;
  assume _; reflexivity;
  assume f; refine f _;
end;

symbol eq_True_is_True b : tEv (b = True) → tEv (is_True b)
≔ begin
  induction;
  assume _ f; refine f;
  assume f;
  refine True_eq_False_exfalso false f;
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

// Naturals

// inductive nat : TYPE ≔
// | O : nat
// | S : nat → nat;

// symbol Dnat : Type;
// rule tEv Dnat ↪ nat;
// unif_rule nat ≡ tEv $t ↪ [ $t ≡ Dnat ];

// // symbol Dnat : Type;
// // symbol nat ≔ tEv Dnat;

// // symbol O : nat;
// // symbol S : nat → nat;

// symbol nat_ind :
//   tEv (`π Q : nat → Type,
//        Q O ⇒
//        `∀ n : nat, Q n ⇒ Q (S n) ⇒
//        `∀ n : nat, Q n) ≔ ind_nat;

// // rule nat_ind _  $vO _   O      ↪ $vO
// // with nat_ind $Q $vO $vS (S $n) ↪ $vS $n (nat_ind $Q $vO $vS $n);

// symbol nat_add ≔
//   ind_nat (λ _, Dnat ⇒ Dnat)
//      (λ m, m)
//      (λ _ nat_add_n m, S (nat_add_n m));

// symbol nat_add_O n : tEv (nat_add O n = n)
// ≔ begin assume n; reflexivity; end;

// symbol nat_add_S m n : tEv (nat_add (S m) n = S (nat_add m n))
// ≔ begin assume m n; reflexivity; end;

// symbol nat_plus_zero (n : nat) :
//   tEv (nat_add n O = n)
// ≔ begin
//   induction;
//   reflexivity;

//   assume n Hrec;
//   rewrite left [x in _ = S x] Hrec;
//   reflexivity;
// end;

// symbol nat_add_assoc a :
//   tEv (`∀ b, `∀ c, nat_add a (nat_add b c) = nat_add (nat_add a b) c)
// ≔ begin
//   refine nat_ind (λ a, `∀ b, `∀ c, nat_add a (nat_add b c) = nat_add (nat_add a b) c)
//          _ _;
//   assume b c; reflexivity;
//   assume n Hrec b c;
//   rewrite nat_add_S;
//   rewrite nat_add_S;
//   rewrite nat_add_S;
//   rewrite Hrec;
//   reflexivity;
// end;

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

symbol pos_add_xH y : tEv (pos_add xH y = pos_succ y);

symbol pos_add_succ x y : tEv (pos_add (pos_succ x) y = pos_succ (pos_add x y));

symbol pos_add_assoc x y z : tEv (pos_add x (pos_add y z) = pos_add (pos_add x y) z)
≔ begin
  refine pos_peano_ind (λ x, `∀ y, `∀ z, pos_add x (pos_add y z) = pos_add (pos_add x y) z) _ _;
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
     (λ _ comp_p r, pos_ind (λ _, Dcomparison)
        (λ q _, comp_p r q)
        (λ q _, comp_p Gt q)
        Gt)
     (λ _ comp_p r, pos_ind (λ _, Dcomparison)
        (λ q _, comp_p Lt q)
        (λ q _, comp_p r q)
        Gt)
     (λ r, pos_ind (λ _, Dcomparison)
        (λ _ _, Lt)
        (λ _ _, Lt)
        r);

symbol pos_compare x y ≔ pos_compare_acc x Eq y;

symbol pos_compare' ≔
  pos_ind (λ _, Dpositive ⇒ Dcomparison)
     (λ _ pos_compare_p, pos_ind (λ _, Dcomparison)
        (λ q _, pos_compare_p q)
        (λ q _, comp_ind (λ _, Dcomparison)
                         Gt
                         Lt
                         Gt
                         (pos_compare_p q))
        Gt)
     (λ _ pos_compare_p, pos_ind (λ _, Dcomparison)
        (λ q _, comp_ind (λ _, Dcomparison)
                         Lt
                         Lt
                         Gt
                         (pos_compare_p q))
        (λ q _, pos_compare_p q)
        Gt)
     (pos_ind (λ _, Dcomparison)
              (λ _ _, Lt)
              (λ _ _, Lt)
              Eq);

symbol pos_compare'_sym x y : tEv (pos_compare' y x = CompOpp (pos_compare' x y));



// assert ⊢ pos_compare xH xH ≡ Eq;
// assert ⊢ pos_compare (xI xH) xH ≡ Gt;
// assert ⊢ pos_compare (xI xH) (xO xH) ≡ Gt;

// symbol left_acc ≔
//   comp_ind (λ _, Dpositive ⇒ Dpositive)
//       (λ p, p)
//       xO
//       xI;

// symbol right_acc ≔
//   comp_ind (λ _, Dpositive ⇒ Dpositive)
//       (λ p, p)
//       xI
//       xO;

// Eq = a

// fun c ⇒ comp_ind (λ _, Dcomparison)
// true
// false
// false
// c

// f Eq

// rewrite H

// f a A
// A
// symbol eq_Eq ≔ comp_rect (λ _, DType) true false false;

// symbol discr_I_O x y A : tEv (pos_compare' (xI x) (xO y) = Eq ⇒ A)
// ≔ begin
//   assume x y A;
//   have e : tEv (pos_compare' (xI x) (xO y) =
//                            comp_ind (λ _, Dcomparison) Gt Lt Gt
//                            (pos_compare' x y));
//   reflexivity;
//   refine comp_ind (λ p, pos_compare' x y = p ⇒ pos_compare' (xI x) (xO y) = Eq ⇒ A) _ _ _ (pos_compare' x y) _;


//   rewrite e;
//   assume eq;
//   refine =_ind Dcomparison (pos_compare' x y) Eq eq (λ u :comparison, (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq) ⇒ A) _;
//   assume H;
//   have f : tEv (eq_Eq Gt);
//   refine =_ind Dcomparison Gt Eq H (λ u, eq_Eq u) _;
//   refine tt;
//   refine f _;

//   rewrite e;
//   assume eq;
//   refine =_ind Dcomparison (pos_compare' x y) Lt eq (λ u :comparison, (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq) ⇒ A) _;
//   assume H;
//   have f : tEv (eq_Eq Lt);
//   refine =_ind Dcomparison Lt Eq H (λ u, eq_Eq u) _;
//   refine tt;
//   refine f _;

//   rewrite e;
//   assume eq;
//   refine =_ind Dcomparison (pos_compare' x y) Gt eq (λ u :comparison, (comp_ind (λ _, Dcomparison) Gt Lt Gt u = Eq) ⇒ A) _;
//   assume H;
//   have f : tEv (eq_Eq Gt);
//   refine =_ind Dcomparison Gt Eq H (λ u, eq_Eq u) _;
//   refine tt;
//   refine f _;

//   reflexivity;
// end;

// symbol discr_acc x y acc : tEv (pos_compare' (left_acc acc (xI x))
//                                            (right_acc acc (xO y)) =
//                                 pos_compare' (xI x) (xO y))
// ≔ begin
//   assume x y;
//   induction;
//   reflexivity;
//   refine comp_ind (λ c, pos_compare' (xI x) (xO y) = c ⇒ comp_ind (λ _, Dcomparison) Lt Lt Gt c = c) _ _ _
//                   (pos_compare' (xI x) (xO y)) _;
//   assume H; refine discr_I_O x y _ H;
//   assume _; reflexivity;
//   assume _; reflexivity;
//   reflexivity;

//   refine comp_ind (λ c, pos_compare' (xI x) (xO y) = c ⇒ comp_ind (λ _, Dcomparison) Gt Lt Gt c = c) _ _ _
//                   (pos_compare' (xI x) (xO y)) _;
//   assume H; refine discr_I_O x y _ H;
//   assume _; reflexivity;
//   assume _; reflexivity;
//   reflexivity;
// end;

// symbol pos_compare_compare'_aux x y acc :
//   tEv (pos_compare' (left_acc acc x) (right_acc acc y) = pos_compare_acc x acc y);
// ≔ begin
//   refine pos_ind (λ x, `∀ y, `∀ acc, pos_compare' (left_acc acc x) (right_acc acc y) = pos_compare_acc x acc y) _ _ _;

//   assume x xrec y acc;
//   refine pos_ind (λ y, pos_compare' (left_acc acc (xI x)) (right_acc acc y) = pos_compare_acc (xI x) acc y) _ _ _ y;
//   // xI - xI case
//   assume q _;
//   refine comp_ind (λ acc, pos_compare' (left_acc acc (xI x)) (right_acc acc (xI q)) = pos_compare_acc (xI x) acc (xI q)) _ _ _ acc;
//   refine xrec q Eq;
//   refine xrec q Lt;
//   refine xrec q Gt;
// // xI - xO case
//   assume q _;
//   refine comp_ind (λ acc, pos_compare' (left_acc acc (xI x)) (right_acc acc (xO q)) = pos_compare_acc (xI x) acc (xO q)) _ _ _ acc;
//   refine xrec q Gt;
//   rewrite discr_acc;
//   refine (xrec q Gt);

//   refine xrec q Gt;
//   refine xrec q Gt;


// end;

// symbol pos_compare_compare' x y : tEv (pos_compare' x y = pos_compare x y)
// ≔ begin
//   assume x y;
//   refine pos_compare_compare'_aux x y Eq;
// end;

// TODO (prove by saying that Eq does not propagate)
symbol pos_comp_eq x y : tEv (pos_compare_acc x Eq y = Eq ⇒ x = y);
// ≔ begin
//   refine pos_ind (λ x, `∀ y, pos_compare_acc x Eq y = Eq ⇒ x = y) _ _ _;
//   assume x Hrec;
//   induction;
//   assume y _ H; rewrite (Hrec y H); reflexivity;
//   assume y _ H;
// end;

symbol pos_comp_opp x y r :
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

symbol pos_compare_def x y : tEv (pos_compare x y = pos_compare_acc x Eq y)
≔ begin assume x y; reflexivity; end;

symbol pos_compare_opp x y : tEv (pos_compare x y = CompOpp (pos_compare y x))
≔ begin
  assume x y;
  rewrite pos_compare_def;
  rewrite pos_comp_opp;
  reflexivity;
end;

// symbol pos_to_nat_acc ≔
//   pos_ind (λ _, Dnat ⇒ Dnat)
//      (λ p pos_to_nat_p acc, nat_add acc (pos_to_nat_p (nat_add acc acc)))
//      (λ p pos_to_nat_p acc, pos_to_nat_p (nat_add acc acc))
//      (λ acc, acc);

// symbol pos_to_nat_xI p acc :
//   tEv (pos_to_nat_acc (xI p) acc = nat_add acc (pos_to_nat_acc p (nat_add acc acc)))
// ≔ begin reflexivity; end;

// symbol pos_to_nat_xO p acc :
//   tEv (pos_to_nat_acc (xO p) acc = pos_to_nat_acc p (nat_add acc acc))
// ≔ begin reflexivity; end;

// symbol pos_to_nat_xH acc :
//   tEv (pos_to_nat_acc xH acc = acc)
// ≔ begin reflexivity; end;

// symbol pos_to_nat p ≔ pos_to_nat_acc p (S O);

// symbol inj_succ : Π p,
//   tEv (`∀ acc, pos_to_nat_acc (pos_succ p) acc = nat_add acc (pos_to_nat_acc p acc))
// ≔ begin
//   refine pos_ind
//   (λ p, `∀ acc, pos_to_nat_acc (pos_succ p) acc = nat_add acc (pos_to_nat_acc p acc))
//   _ _ _;
// // Case xI
//   assume p Hrec acc;
//   rewrite pos_succ_xI;
//   rewrite pos_to_nat_xO;
//   rewrite pos_to_nat_xI;
//   rewrite nat_add_assoc;
//   refine Hrec (nat_add acc acc);
// // Case xO
//   reflexivity;
// // Case xH
//   reflexivity;
// end;

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

symbol double ≔
  Z_ind (λ _, DZ)
    zero
    (λ p, Zpos (xO p))
    (λ p, Zneg (xO p));

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

symbol ~ ≔
  Z_ind (λ _, DZ)
     zero
     (λ x, Zneg x)
     (λ x, Zpos x);
notation ~ prefix 44;

symbol succ x ≔ x + one;

symbol - x y ≔ x + ~ y;
notation - infix left 40;

symbol sub_def x y : tEv (x - y = x + ~ y)
≔ begin assume x y; reflexivity; end;

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

symbol compare_opp x y : tEv (compare x y = CompOpp (compare y x))
≔ begin
  assume x;
  refine ind_Z (λ x, `∀ y, compare x y = CompOpp (compare y x)) _ _ _ x;

  induction;
  reflexivity; reflexivity; reflexivity;

  assume x0;
  induction;
  reflexivity;
  assume x1; refine pos_compare_opp x0 x1;
  reflexivity;

  assume x0;
  induction;
  reflexivity;
  reflexivity;
  assume x1; refine pos_compare_opp x1 x0;
end;

symbol leb x y ≔
  comp_ind (λ _, Dboolean)
      True
      True
      False
      (compare x y);

symbol leb_def x y : tEv (leb x y = (comp_ind (λ _, Dboolean) True True False (compare x y)))
≔ begin reflexivity; end;

// TODO : why can't we rewrite here ?
symbol leb_eq x y : tEv (compare x y = Eq ⇒ leb x y = True);
// ≔ begin
//   assume x y eq;
//   rewrite leb_def;
//   rewrite eq;
//   reflexivity;
// end;

symbol leb_lt x y : tEv (compare x y = Lt ⇒ leb x y = True);
symbol leb_gt x y : tEv (compare x y = Gt ⇒ leb x y = False);


symbol ltb x y ≔
  comp_ind (λ _, Dboolean)
      False
      True
      False
      (compare x y);
symbol ltb_eq x y : tEv (compare x y = Eq ⇒ ltb x y = False);
symbol ltb_lt x y : tEv (compare x y = Lt ⇒ ltb x y = True);
symbol ltb_gt x y : tEv (compare x y = Gt ⇒ ltb x y = False);

symbol geb x y ≔
  comp_ind (λ _, Dboolean)
      True
      False
      True
      (compare x y);

symbol gtb x y ≔
  comp_ind (λ _, Dboolean)
      False
      False
      True
      (compare x y);


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


// TODO
symbol add_assoc x y z : tEv (x + y + z = x + (y + z));
// TODO
symbol add_comm x y : tEv (x + y = y + x);
// TODO
symbol add_opp a : tEv (a - a = 0);

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
  refine True_eq_False_exfalso (y ≤ x) e;

  assume lt; rewrite (leb_lt x y lt);
  assume f;
  have e : tEv (False = True); rewrite f; reflexivity;
  refine True_eq_False_exfalso (y ≤ x) e;

  assume gt _;
  have lt : tEv (CompOpp (compare x y) = CompOpp Gt);
  rewrite gt; reflexivity;
  generalize lt;
  have g : tEv (CompOpp (compare x y) = Lt ⇒ y ≤ x);
  rewrite left (compare_opp y x);
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
