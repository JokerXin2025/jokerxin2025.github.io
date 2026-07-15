import «Calculus@JokerXin».Limit.Expr


/-! # Basic Limits -/

/-! For more _limits, please refer to `Function.Continuity.Elementary`. -/

/- # To be Modified ↓ -/
/-- Constant Sequence's Limit (Expression) -/
lemma SeqLimitExpr.Constant {C : ℝ}
  : _limₙ (fun _ ↦ C) = the C
:= sorry


/-! # Limit Calculation Rules -/

/-!
The rules for __Function's Multiplicative Scalar Power__ are not provided here,
which can be regarded as a composite function by the following conclusion:
```lean
example {f : ℝ → ℝ} {n : ℕ} : f ^ n = npow n ∘ f := by rfl
```
-/

/-- Sequence Limit of Scalar Multiplication -/
theorem SeqLimit.SMul {A : Sequence} {k L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (k • A) (k * L₁)
:= sorry

/-- Sequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul {a : ℕ → ℝ} {k : ℝ}
  : _limₙ (k • a : ℕ → ℝ) =? the k * _limₙ a
:= sorry

/-- Function Limit of Scalar Multiplication -/
theorem FuncLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Function Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : _lim (k • f : ℝ → ℝ) x₀ =? the k * _lim f x₀
:= sorry

/-- Left Limit of Scalar Multiplication -/
theorem LeftLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : _lim₋ (k • f : ℝ → ℝ) x₀ =? the k * _lim₋ f x₀
:= sorry

/-- Right Limit of Scalar Multiplication -/
theorem RightLimit.SMul {F G : Function} {k x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (k • F) x₀ (k * L₁)
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : _lim₊ (k • f : ℝ → ℝ) x₀ =? the k * _lim₊ f x₀
:= sorry

/-- Sequence Limit of Additive Inverse -/
theorem SeqLimit.Neg {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (-A) (-L₁)
:= sorry

/-- Sequence Limit of Additive Inverse (Expression) -/
theorem SeqLimitExpr.Neg {a : ℕ → ℝ}
  : _limₙ (-a : ℕ → ℝ) =? - _limₙ a
:= sorry

/-- Function Limit of Additive Inverse -/
theorem FuncLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (-F) x₀ (-L₁)
:= sorry

/-- Function Limit of Additive Inverse (Expression) -/
theorem FuncLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim (-f : ℝ → ℝ) x₀ =? - _lim f x₀
:= sorry

/-- Left Limit of Additive Inverse -/
theorem LeftLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (-F) x₀ (-L₁)
:= sorry

/-- Left Limit of Additive Inverse (Expression) -/
theorem LeftLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (-f : ℝ → ℝ) x₀ =? - _lim₋ f x₀
:= sorry

/-- Right Limit of Additive Inverse -/
theorem RightLimit.Neg {F G : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (-F) x₀ (-L₁)
:= sorry

/-- Right Limit of Additive Inverse (Expression) -/
theorem RightLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (-f : ℝ → ℝ) x₀ =? - _lim₊ f x₀
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power -/
theorem SeqLimit.MSPow {A : Sequence} {n : ℕ} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (A ^ n) (L₁ ^ n)
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power (Expression) -/
theorem SeqLimitExpr.MSPow {a : ℕ → ℝ} {n : ℕ}
  : _limₙ (a ^ n : ℕ → ℝ) =? _limₙ a ^ the (n : ℝ)
:= sorry

/-- Sequence Limit of Multiplicative Inverse -/
theorem SeqLimit.Inv {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit A⁻¹ L₁⁻¹
:= sorry

/-- Sequence Limit of Multiplicative Inverse (Expression) -/
theorem SeqLimitExpr.Inv {a : ℕ → ℝ}
  : _limₙ (a⁻¹ : ℕ → ℝ) =? (_limₙ a)⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse -/
theorem FuncLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse (Expression) -/
theorem FuncLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim (f⁻¹ : ℝ → ℝ) x₀ =? (_lim f x₀)⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse -/
theorem LeftLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse (Expression) -/
theorem LeftLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (f⁻¹ : ℝ → ℝ) x₀ =? (_lim₋ f x₀)⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse -/
theorem RightLimit.Inv {F G : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse (Expression) -/
theorem RightLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (f⁻¹ : ℝ → ℝ) x₀ =? (_lim₊ f x₀)⁻¹
:= sorry

/-- Sequence Limit Addition -/
theorem SeqLimit.Add {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A + B) (L₁ + L₂)
:= sorry

/-- Sequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add {a b : ℕ → ℝ}
  : _limₙ (a + b : ℕ → ℝ) =? _limₙ a + _limₙ b
:= sorry

/-- Function Limit Addition -/
theorem FuncLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Function Limit Addition (Expression) -/
theorem FuncLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim (f + g : ℝ → ℝ) x₀ =? _lim f x₀ + _lim g x₀
:= sorry

/-- Left Limit Addition -/
theorem LeftLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (f + g : ℝ → ℝ) x₀ =? _lim₋ f x₀ + _lim₋ g x₀
:= sorry

/-- Right Limit Addition -/
theorem RightLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F + G) x₀ (L₁ + L₂)
:= sorry

/-- Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (f + g : ℝ → ℝ) x₀ =? _lim₊ f x₀ + _lim₊ g x₀
:= sorry

/-- Sequence Limit Subtraction -/
theorem SeqLimit.Sub {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A - B) (L₁ - L₂)
:= sorry

/-- Sequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub {a b : ℕ → ℝ}
  : _limₙ (a - b : ℕ → ℝ) =? _limₙ a - _limₙ b
:= sorry

/-- Function Limit Subtraction -/
theorem FuncLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Function Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim (f - g : ℝ → ℝ) x₀ =? _lim f x₀ - _lim g x₀
:= sorry

/-- Left Limit Subtraction -/
theorem LeftLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (f - g : ℝ → ℝ) x₀ =? _lim₋ f x₀ - _lim₋ g x₀
:= sorry

/-- Right Limit Subtraction -/
theorem RightLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F - G) x₀ (L₁ - L₂)
:= sorry

/-- Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (f - g : ℝ → ℝ) x₀ =? _lim₊ f x₀ - _lim₊ g x₀
:= sorry

/-- Sequence Limit Multiplication -/
theorem SeqLimit.Mul {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A * B) (L₁ * L₂)
:= sorry

/-- Sequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul {a b : ℕ → ℝ}
  : _limₙ (a * b : ℕ → ℝ) =? _limₙ a * _limₙ b
:= sorry

/-- Function Limit Multiplication -/
theorem FuncLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Function Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim (f * g : ℝ → ℝ) x₀ =? _lim f x₀ * _lim g x₀
:= sorry

/-- Left Limit Multiplication -/
theorem LeftLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (f * g : ℝ → ℝ) x₀ =? _lim₋ f x₀ * _lim₋ g x₀
:= sorry

/-- Right Limit Multiplication -/
theorem RightLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F * G) x₀ (L₁ * L₂)
:= sorry

/-- Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (f * g : ℝ → ℝ) x₀ =? _lim₊ f x₀ * _lim₊ g x₀
:= sorry

/-- Sequence Limit Division -/
theorem SeqLimit.Div {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : SeqLimit (A / B) (L₁ / L₂)
:= sorry

/-- Sequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div {a b : ℕ → ℝ}
  : _limₙ (a / b : ℕ → ℝ) =? _limₙ a / _limₙ b
:= sorry

/-- Function Limit Division -/
theorem FuncLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : FuncLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Function Limit Division (Expression) -/
theorem FuncLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim (f / g : ℝ → ℝ) x₀ =? _lim f x₀ / _lim g x₀
:= sorry

/-- Left Limit Division -/
theorem LeftLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : LeftLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₋ (f / g : ℝ → ℝ) x₀ =? _lim₋ f x₀ / _lim₋ g x₀
:= sorry

/-- Right Limit Division -/
theorem RightLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : RightLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Right Limit Division (Expression) -/
theorem RightLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : _lim₊ (f / g : ℝ → ℝ) x₀ =? _lim₊ f x₀ / _lim₊ g x₀
:= sorry

/-- Function Limit Composition -/
theorem FuncLimit.Comp {x₀ u₀ L₁ : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_G_ne_u₀ : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, G.map x ≠ u₀)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_L : FuncLimit F u₀ L₁)
  : FuncLimit (F ⊙ G) x₀ L₁
:= sorry

/-- Squeeze Theorem for Sequence Limit (Expression) -/
theorem SeqLimit.Squeeze {a b c : ℕ → ℝ} {L₁ : ℝ}
    (h_a : _limₙ a = the L₁) (h_c : _limₙ c = the L₁)
    (h_chain : ∀ n, a n ≤ b n ∧ b n ≤ c n)
  : _limₙ b = the L₁
:= sorry

/-- Squeeze Theorem for Function Limit (Expression) -/
theorem FuncLimit.Squeeze {f g h : ℝ → ℝ} {x₀ L₁ : ℝ}
    (h_F : _lim f x₀ = the L₁) (h_h : _lim h x₀ = the L₁)
    (h_chain : ∀ x, f x ≤ g x ∧ g x ≤ h x)
  : _lim g x₀ = the L₁
:= sorry
