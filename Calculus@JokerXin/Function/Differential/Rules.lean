import «Calculus@JokerXin».Function.Differential.Expr


/-! # Derivative Calculation Rules -/

/-!
The rules for __Multiplicative Scalar Power__ are not provided here, which can be
regarded as a composite function by the following conclusion:
```lean
example {f : ℝ → ℝ} {n : ℕ} : f ^ n = npow n ∘ f := by rfl
```
-/

/-- Derivative of Scalar Multiplication -/
theorem Deriv.SMul {F : Function} {k x₀ D₁ : ℝ}
    (h_F : Deriv F x₀ D₁)
  : Deriv (k • F) x₀ (k * D₁)
:= sorry

/-- Derivative of Scalar Multiplication (Expression) -/
theorem DerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D (k • f : ℝ → ℝ) x₀ =? the k * D f x₀
:= sorry

/-- Left Derivative of Scalar Multiplication -/
theorem LeftDeriv.SMul {F : Function} {k x₀ D₁ : ℝ}
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (k • F) x₀ (k * D₁)
:= sorry

/-- Left Derivative of Scalar Multiplication (Expression) -/
theorem LeftDerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D₋ (k • f : ℝ → ℝ) x₀ =? the k * D₋ f x₀
:= sorry

/-- Right Derivative of Scalar Multiplication -/
theorem RightDeriv.SMul {F : Function} {k x₀ D₁ : ℝ}
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (k • F) x₀ (k * D₁)
:= sorry

/-- Right Derivative of Scalar Multiplication (Expression) -/
theorem RightDerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D₊ (k • f : ℝ → ℝ) x₀ =? the k * D₊ f x₀
:= sorry

/-- N-th Order Derivative of Scalar Multiplication -/
theorem NthDeriv.SMul {n : ℕ} {F : Function} {k x₀ D₁ : ℝ}
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (k • F) x₀ (k * D₁)
:= sorry

/-- N-th Order Derivative of Scalar Multiplication (Expression) -/
theorem NthDerivExpr.SMul {n : ℕ} {f : ℝ → ℝ} {k x₀ : ℝ}
  : Dₙ n (k • f : ℝ → ℝ) x₀ =? the k * Dₙ n f x₀
:= sorry

/-- Derivative of Additive Inverse -/
theorem Deriv.Neg {F : Function} {x₀ D₁ : ℝ}
    (h_F : Deriv F x₀ D₁)
  : Deriv (-F) x₀ (-D₁)
:= sorry

/-- Derivative of Additive Inverse (Expression) -/
theorem DerivExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : D (-f : ℝ → ℝ) x₀ =? - D f x₀
:= sorry

/-- Left Derivative of Additive Inverse -/
theorem LeftDeriv.Neg {F : Function} {x₀ D₁ : ℝ}
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (-F) x₀ (-D₁)
:= sorry

/-- Left Derivative of Additive Inverse (Expression) -/
theorem LeftDerivExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (-f : ℝ → ℝ) x₀ =? - D₋ f x₀
:= sorry

/-- Right Derivative of Additive Inverse -/
theorem RightDeriv.Neg {F : Function} {x₀ D₁ : ℝ}
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (-F) x₀ (-D₁)
:= sorry

/-- Right Derivative of Additive Inverse (Expression) -/
theorem RightDerivExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (-f : ℝ → ℝ) x₀ =? - D₊ f x₀
:= sorry

/-- N-th Order Derivative of Additive Inverse -/
theorem NthDeriv.Neg {n : ℕ} {F : Function} {x₀ D₁ : ℝ}
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (-F) x₀ (-D₁)
:= sorry

/-- N-th Order Derivative of Additive Inverse (Expression) -/
theorem NthDerivExpr.Neg {n : ℕ} {f : ℝ → ℝ} {x₀ : ℝ}
  : Dₙ n (-f : ℝ → ℝ) x₀ =? - Dₙ n f x₀
:= sorry

/-- Derivative of Multiplicative Inverse -/
theorem Deriv.Inv {F : Function} {x₀ D₁ : ℝ}
    (h_F : Deriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : Deriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Derivative of Multiplicative Inverse (Expression) -/
theorem DerivExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : D (f⁻¹ : ℝ → ℝ) x₀ =? - D f x₀ / the (f x₀ ^ 2)
:= sorry

/-- Left Derivative of Multiplicative Inverse -/
theorem LeftDeriv.Inv {F : Function} {x₀ D₁ : ℝ}
    (h_F : LeftDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : LeftDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Left Derivative of Multiplicative Inverse (Expression) -/
theorem LeftDerivExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f⁻¹ : ℝ → ℝ) x₀ =? - D₋ f x₀ / the (f x₀ ^ 2)
:= sorry

/-- Right Derivative of Multiplicative Inverse -/
theorem RightDeriv.Inv {F : Function} {x₀ D₁ : ℝ}
    (h_F : RightDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : RightDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Right Derivative of Multiplicative Inverse (Expression) -/
theorem RightDerivExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f⁻¹ : ℝ → ℝ) x₀ =? - D₊ f x₀ / the (f x₀ ^ 2)
:= sorry

/-- Derivative Addition -/
theorem Deriv.Add {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Derivative Addition (Expression) -/
theorem DerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f + g : ℝ → ℝ) x₀ =? D f x₀ + D g x₀
:= sorry

/-- Left Derivative Addition -/
theorem LeftDeriv.Add {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Left Derivative Addition (Expression) -/
theorem LeftDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f + g : ℝ → ℝ) x₀ =? D₋ f x₀ + D₋ g x₀
:= sorry

/-- Right Derivative Addition -/
theorem RightDeriv.Add {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Right Derivative Addition (Expression) -/
theorem RightDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f + g : ℝ → ℝ) x₀ =? D₊ f x₀ + D₊ g x₀
:= sorry

/-- N-th Order Derivative Addition -/
theorem NthDeriv.Add {n : ℕ} {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : NthDeriv n F x₀ D₁) (h_G : NthDeriv n G x₀ D₂)
  : NthDeriv n (F + G) x₀ (D₁ + D₂)
:= sorry

/-- N-th Order Derivative Addition (Expression) -/
theorem NthDerivExpr.Add {n : ℕ} {f g : ℝ → ℝ} {x₀ : ℝ}
  : Dₙ n (f + g : ℝ → ℝ) x₀ =? Dₙ n f x₀ + Dₙ n g x₀
:= sorry

/-- Derivative Subtraction -/
theorem Deriv.Sub {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Derivative Subtraction (Expression) -/
theorem DerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f - g : ℝ → ℝ) x₀ =? D f x₀ - D g x₀
:= sorry

/-- Left Derivative Subtraction -/
theorem LeftDeriv.Sub {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Left Derivative Subtraction (Expression) -/
theorem LeftDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f - g : ℝ → ℝ) x₀ =? D₋ f x₀ - D₋ g x₀
:= sorry

/-- Right Derivative Subtraction -/
theorem RightDeriv.Sub {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Right Derivative Subtraction (Expression) -/
theorem RightDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f - g : ℝ → ℝ) x₀ =? D₊ f x₀ - D₊ g x₀
:= sorry

/-- N-th Order Derivative Subtraction -/
theorem NthDeriv.Sub {n : ℕ} {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : NthDeriv n F x₀ D₁) (h_G : NthDeriv n G x₀ D₂)
  : NthDeriv n (F - G) x₀ (D₁ - D₂)
:= sorry

/-- N-th Order Derivative Subtraction (Expression) -/
theorem NthDerivExpr.Sub {n : ℕ} {f g : ℝ → ℝ} {x₀ : ℝ}
  : Dₙ n (f - g : ℝ → ℝ) x₀ =? Dₙ n f x₀ - Dₙ n g x₀
:= sorry

/-- Derivative Multiplication -/
theorem Deriv.Mul {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Derivative Multiplication (Expression) -/
theorem DerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f * g : ℝ → ℝ) x₀ =? D f x₀ * the (g x₀) + the (f x₀) * D g x₀
:= sorry

/-- Left Derivative Multiplication -/
theorem LeftDeriv.Mul {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Left Derivative Multiplication (Expression) -/
theorem LeftDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f * g : ℝ → ℝ) x₀ =? D₋ f x₀ * the (g x₀) + the (f x₀) * D₋ g x₀
:= sorry

/-- Right Derivative Multiplication -/
theorem RightDeriv.Mul {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Right Derivative Multiplication (Expression) -/
theorem RightDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f * g : ℝ → ℝ) x₀ =? D₊ f x₀ * the (g x₀) + the (f x₀) * D₊ g x₀
:= sorry

/-- Derivative Division -/
theorem Deriv.Div {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : Deriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Derivative Division (Expression) -/
theorem DerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f / g : ℝ → ℝ) x₀
    =? (D f x₀ * the (g x₀) - the (f x₀) * D g x₀) / the ((g x₀) ^ 2)
:= sorry

/-- Left Derivative Division -/
theorem LeftDeriv.Div {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : LeftDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Left Derivative Division (Expression) -/
theorem LeftDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f / g : ℝ → ℝ) x₀
    =? (D₋ f x₀ * the (g x₀) - the (f x₀) * D₋ g x₀) / the ((g x₀) ^ 2)
:= sorry

/-- Right Derivative Division -/
theorem RightDeriv.Div {F G : Function} {x₀ D₁ D₂ : ℝ}
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : RightDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Right Derivative Division (Expression) -/
theorem RightDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f / g : ℝ → ℝ) x₀
    =? (D₊ f x₀ * the (g x₀) - the (f x₀) * D₊ g x₀) / the ((g x₀) ^ 2)
:= sorry

/-- Derivative's Chain Rule -/
theorem Deriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : Deriv G x₀ G') (h_F : Deriv F (G.map x₀) F')
  : Deriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- Derivative's Chain Rule (Expression) -/
theorem DerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f ∘ g : ℝ → ℝ) x₀ =? D f (g x₀) * D g x₀
:= sorry

/-- Left Derivative's Chain Rule -/
theorem LeftDeriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : LeftDeriv G x₀ G') (h_F : LeftDeriv F (G.map x₀) F')
  : LeftDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- Left Derivative's Chain Rule (Expression) -/
theorem LeftDerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f ∘ g : ℝ → ℝ) x₀ =? D₋ f (g x₀) * D₋ g x₀
:= sorry

/-- Right Derivative's Chain Rule -/
theorem RightDeriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : RightDeriv G x₀ G') (h_F : RightDeriv F (G.map x₀) F')
  : RightDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- Right Derivative's Chain Rule (Expression) -/
theorem RightDerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f ∘ g : ℝ → ℝ) x₀ =? D₊ f (g x₀) * D₊ g x₀
:= sorry
