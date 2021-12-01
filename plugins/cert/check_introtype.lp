require open cert_lambdapi.preamble;

symbol to_verify :
  εₜ (`π string : Type,
      `π unit : Type,
      `π a : Type,
      `π p : Π 'a : Type,εₜ 'a → Type,
      `π b : Type,
      `∀ x : εₜ a,
      b ⇒
      ¬ b ⇒
      ⊥) →
  εₜ (`π string : Type,
      `π unit : Type,
      `π p : Π 'a : Type,εₜ 'a → Type,
      `π b : Type,
      b ⇒
      ¬ (`π a1 : Type, `∀ x1 : Π 'a : Type,εₜ 'a, b) ⇒
      ⊥)
≔ begin
  assume s string unit p b HB HG1;
  refine IntroType (λ a1 : Type, `∀ x1 : (Π 'a : Type, εₜ 'a), b) HG1 _;
  assume a HG2;
  refine IntroQuantGoal (λ x1 : εₜ a, b) HG2 _;

end;
// ≔ λ s string unit p b HB HG1,
//   IntroType (`π a1 : Type, `∀ x1 : (Π 'a : Type, εₜ 'a), b) HG1 (λ a HG1,
//   IntroQuantGoal (λ x1 : εₜ a, b) HG1 (λ x HG1,
//   s string unit a p b x HB HG1));
