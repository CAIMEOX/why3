

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
//        (`∀ b : boolean, Q b)) ≔ ind_boolean;

// rule bool_ind _ $vT _   True  ↪ $vT
// with bool_ind _ _   $vF False ↪ $vF;

symbol if (a : Type) b t e ≔
  ind_boolean (λ _, a) t e b;

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
       (`∀ c : comparison, Q c)) ≔ ind_comparison;

// rule comp_ind _ $vE _   _   Eq  ↪ $vE
// with comp_ind _ _   $vL _   Lt  ↪ $vL
// with comp_ind _ _   _   $vG Gt  ↪ $vG;

// Naturals

inductive nat : TYPE ≔
| O : nat
| S : nat → nat;

symbol Dnat : Type;
rule tEv Dnat ↪ nat;
unif_rule nat ≡ tEv $t ↪ [ $t ≡ Dnat ];

// symbol Dnat : Type;
// symbol nat ≔ tEv Dnat;

// symbol O : nat;
// symbol S : nat → nat;

symbol nat_ind :
  tEv (`π Q : nat → Type,
       Q O ⇒
       (`∀ n : nat, Q n ⇒ Q (S n)) ⇒
       (`∀ n : nat, Q n)) ≔ ind_nat;

// rule nat_ind _  $vO _   O      ↪ $vO
// with nat_ind $Q $vO $vS (S $n) ↪ $vS $n (nat_ind $Q $vO $vS $n);

symbol nat_add ≔
  ind_nat (λ _, Dnat ⇒ Dnat)
     (λ m, m)
     (λ _ nat_add_n m, S (nat_add_n m));

symbol nat_plus_one (n : nat) :
  tEv (nat_add O n = n);

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
       (`∀ p : positive, Q p)) ≔ ind_positive;

// rule pos_ind _  _   _   $vH xH      ↪ $vH
// with pos_ind $Q $vI $vO $vH (xI $p) ↪ $vI $p (pos_ind $Q $vI $vO $vH $p)
// with pos_ind $Q $vI $vO $vH (xO $p) ↪ $vO $p (pos_ind $Q $vI $vO $vH $p);

symbol pos_succ ≔
  pos_ind (λ _, Dpositive)
    (λ _ succ_p, xO succ_p)
    (λ p _, xI p)
    (xO xH);

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

symbol pos_compare_acc ≔
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

symbol pos_to_nat_acc ≔
  pos_ind (λ _, Dnat ⇒ Dnat)
     (λ p pos_to_nat_p acc, nat_add acc (pos_to_nat_p (nat_add acc acc)))
     (λ p pos_to_nat_p acc, pos_to_nat_p (nat_add acc acc))
     (λ acc, acc);

symbol pos_to_nat p ≔ pos_to_nat_acc p (S O);

// symbol inj_succ (p : positive) :
//   tEv (eq Dnat (pos_to_nat (pos_succ p)) (S (pos_to_nat p)));
// ≔
//   pos_ind (λ _, Type)

// N

// inductive N : TYPE ≔
// | N0 : N
// | Npos : positive → N;

// symbol DN : Type;
// rule tEv DN ↪ N;
// unif_rule N ≡ tEv $t ↪ [ $t ≡ DN ];

// symbol DN : Type;
// symbol N ≔ tEv DN;

// symbol N0 : N;
// symbol Npos : positive → N;

// symbol N_ind :
//   tEv (`π Q : N → Type,
//        Q N0 ⇒
//        (`∀ p : positive, Q (Npos p)) ⇒
//        (`∀ z : N, Q z));

// rule N_ind _ $v0 _     N0        ↪ $v0
// with N_ind _ _   $vpos (Npos $x) ↪ $vpos $x;

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
       (`∀ z : Z, Q z)) ≔ ind_Z;

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


symbol add x y ≔
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

symbol opp ≔
  Z_ind (λ _, DZ)
     zero
     (λ x, Zneg x)
     (λ x, Zpos x);

symbol succ x ≔ add x one;

symbol sub x y ≔ add x (opp y);

symbol mul x y ≔
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

symbol leb x y ≔
  comp_ind (λ _, Dboolean)
      True
      True
      False
      (compare x y);

symbol ltb x y ≔
  comp_ind (λ _, Dboolean)
      False
      True
      False
      (compare x y);

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

symbol le x y ≔ is_True (leb x y);
symbol lt x y ≔ is_True (ltb x y);
symbol ge x y ≔ is_True (geb x y);
symbol gt x y ≔ is_True (gtb x y);

// assert ⊢ lt 3 (opp 2) ≡ false;
// assert ⊢ lt 3 3 ≡ false;
// assert ⊢ lt 3 5 ≡ true;

// assert ⊢ ge 4 (opp 3) ≡ true;
// assert ⊢ ge 4 4 ≡ true;
// assert ⊢ ge 4 7 ≡ false;


// Conversions

// symbol add_assoc x y z : tEv (eq DZ (add x (add y z)) (add (add x y) z));
// symbol add_comm x y : tEv (eq DZ (add x y) (add y x));

// symbol add_opp a : tEv (eq DZ (add a (opp a)) 0);

symbol simpl_right x a : tEv (sub (add x a) a = x);
symbol simpl_inv_right x a : tEv (add (sub x a) a = x);

symbol max : Z → Z → Z;
symbol max_is_greater_1 : Π x y, tEv (le x (max x y));
symbol max_is_greater_2 : Π x y, tEv (le y (max x y));

symbol case u bound : tEv (le u bound) → tEv (bound = u ∨ lt u bound);

symbol lt_le u z : tEv (lt u (succ z)) → tEv (le u z);

symbol le_lt u z : tEv (le u z) → tEv (lt u (succ z));

symbol le_compat_add x y a : tEv (le x y) → tEv (le (add x a) (add y a));

symbol lt_compat_add x y a : tEv (lt x y) → tEv (lt (add x a) (add y a));

symbol of_nat : nat → Z ≔
  nat_ind (λ _, DZ)
     Z0
     (λ _, succ);

symbol of_nat_0_le :
  Π n,
  tEv (le 0 (of_nat n));

symbol to_nat : Z → nat;

symbol of_nat_to_nat :
  Π (z : Z),
  tEv (le 0 z) →
  tEv (of_nat (to_nat z) = z);

symbol to_nat_of_nat :
  Π (n : nat),
  tEv (n = to_nat (of_nat n));

// Prove strong induction

symbol natlike_rec : Π (P : Z → Type), tEv (P 0) →
                     (Π (z : Z), tEv (le 0 z) → tEv (P z) → tEv (P (succ z))) →
                     Π (z : Z), tEv (le 0 z) → tEv (P z) ≔
  begin
  assume P p0 prec z Hz;
  simplify;
  have e : tEv (z = of_nat (to_nat z));
  symmetry;
  refine of_nat_to_nat z Hz;
  rewrite e;
  refine nat_ind (λ n, P (of_nat n)) _ _ (to_nat z);
  apply p0;
  assume n H;
  refine prec (of_nat n) _ _;
  refine of_nat_0_le n;
  refine H;
end;
  // λ (P : Z → Type) (p0 : tEv (P 0))
  //   (prec : (Π (z : Z), tEv (le 0 z) → tEv (P z) → tEv (P (succ z))))
  //   (z : Z) (Hz : tEv (le 0 z)),
  // let Q (n : nat) : Type ≔ P (of_nat n) in
  // let qrec n : tEv (Q n) → tEv (Q (S n)) ≔
  //   prec (of_nat n) (of_nat_0_le n) in
  // let q : Π n, tEv (Q n) ≔ nat_ind Q
  //                            p0
  //                            qrec in
  // let pconv : tEv (P (of_nat (to_nat z))) ≔
  //   q (to_nat z) in
  // of_nat_to_nat z Hz P pconv;


symbol strong_bound_0_alt_rec : Π P,
                                (Π z, tEv (le z 0) → tEv (P z)) →
                                (Π z, tEv (le 0 z) →
                                      (Π v, tEv (le v z) → tEv (P v)) →
                                      tEv (P (succ z))) →
                                Π z, tEv (P z)
≔
begin
  assume P p0 prec;

// use natlike_rec on Q ≔ λz, ∀ u, u ≤ z → P u
  have q : Π z, tEv (le 0 z) → Π u, tEv (le u z) → tEv (P u);
  refine natlike_rec (λ a, `∀ u : Z, le u a ⇒ P u) _ _;
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
                    (Π x, tEv (le x a) → tEv (P x)) →
                    (Π x, tEv (lt a x) →
                          (Π v, tEv (lt v x) → tEv (P v)) →
                          tEv (P x)) →
                    Π x, tEv (P x)
≔ begin
  assume a P p0 prec;

  have q : Π z, tEv (P (add z a));
  refine strong_bound_0_alt_rec (λ z, P (add z a)) _ _;
// Base case
  assume z Hz;
  refine p0 (add z a) _;
  refine le_compat_add z 0 a Hz;
// Recursive case
  assume z Hz Hrec;
  refine prec (add (succ z) a) _ _;
  refine lt_compat_add 0 (succ z) a _;
  refine le_lt 0 z Hz;
  assume v Hv;
  have e : tEv (v = add (sub v a) a);
  symmetry;
  refine simpl_inv_right v a;
  rewrite e;
  refine Hrec (sub v a) _;
  refine lt_le (sub v a) z _;
  have eqsa : tEv (sub (add (succ z) a) a = succ z);
  refine simpl_right (succ z) a;
  rewrite left eqsa;
  refine lt_compat_add v (add (succ z) a) (opp a) Hv;

  assume x;
  have e : tEv (add (sub x a) a = x);
  refine simpl_inv_right x a;
  rewrite left e;
  refine q (sub x a);
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
   (Π x, tEv (hyp (le x a) (goal (P x) empty))) →
   (Π x, tEv (hyp (lt a x) (hyp (`∀ n : Z, lt n x ⇒ P n) (goal (P x) empty)))) →
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

symbol infixsppl ≔ add;
symbol infixspas ≔ mul;
symbol infixspmn ≔ sub;
symbol prefixspmn ≔ opp;

symbol infixsplseq ≔ le;
symbol infixspls ≔ lt;
symbol infixspgteq ≔ ge;
symbol infixspgt ≔ gt;

symbol - ≔ opp;
notation - prefix 20;

// Also targeted, but not from an ident : quantifications and arrows, true,
// false, ∧, ∨, ¬, ⇔, opp, Z, boolean, DType, Type, int litterals
