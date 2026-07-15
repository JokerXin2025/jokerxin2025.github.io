import «Calculus@JokerXin».Tactics
import «Calculus@JokerXin».Expr.Tactics
import «Calculus@JokerXin».Function.Continuity.Elementary


/-! # Preparations -/

private class AutoLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim f x₀ = the val

private instance funclimit_patch₁ {k x₀ : ℝ}
  : AutoLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intro _
    calc
            lim (k + ·) x₀
         =? lim (const k) x₀ + lim id x₀
            := FuncLimitExpr.Add
      _  =  the k + the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k + x₀)
            := rfl

private instance funclimit_patch₁' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance funclimit_patch₂ {k x₀ : ℝ}
  : AutoLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intro _
    calc
            lim (k - ·) x₀
         =? lim (const k) x₀ - lim id x₀
            := FuncLimitExpr.Sub
      _  =  the k - the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k - x₀)
            := rfl

private instance funclimit_patch₂' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance funclimit_patch₃ {k x₀ : ℝ}
  : AutoLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intro _
    calc
            lim (k * ·) x₀
         =? lim (const k) x₀ * lim id x₀
            := FuncLimitExpr.Mul
      _  =  the k * the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k * x₀)
            := rfl

private instance funclimit_patch₃' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance funclimit_patch₄ {k x₀ : ℝ}
  : AutoLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (k / ·) x₀
         =? lim (const k) x₀ / lim id x₀
            := FuncLimitExpr.Div
      _  =  the k / the x₀
            := by rw [FuncLimitExpr.Constant, FuncLimitExpr.Identity]
      _  =  the (k / x₀)
            := by rw [UdEqual.calc_div h_x₀_ne0]

private instance funclimit_patch₄' {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k / ·) ∘ f) x₀ (k / L₁) c where
  eq := sorry

private instance funclimit_patch₅ {x₀ : ℝ}
  : AutoLimit (-·) x₀ (-x₀) True where
  eq := by
    intro _
    calc
            lim (-·) x₀
         =? - lim id x₀
            := FuncLimitExpr.Neg
      _  =  - the x₀
            := by rw [FuncLimitExpr.Identity]
      _  =  the (-x₀)
            := rfl

private instance funclimit_patch₅' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance funclimit_patch₆ {x₀ : ℝ}
  : AutoLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (·⁻¹) x₀
         =? (lim id x₀)⁻¹
            := FuncLimitExpr.Inv
      _  =  (the x₀)⁻¹
            := by rw [FuncLimitExpr.Identity]
      _  =  the x₀⁻¹
            := by rw [UdEqual.calc_inv h_x₀_ne0]

private instance funclimit_patch₆' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance funclimit_Constant {C x₀ : ℝ}
  : AutoLimit (const C) x₀ C True where
  eq := directly FuncLimitExpr.Constant

private instance funclimit_Constant' {C x₀ : ℝ}
  : AutoLimit (fun _ ↦ C) x₀ C True where
  eq := funclimit_Constant.eq

private instance funclimit_Identity {x₀ : ℝ}
  : AutoLimit id x₀ x₀ True where
  eq := directly FuncLimitExpr.Identity

private instance funclimit_Identity' {x₀ : ℝ}
  : AutoLimit (·) x₀ x₀ True where
  eq := funclimit_Identity.eq

private instance funclimit_SMul {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim (k • f) x₀
         =? the k * lim f x₀
            := FuncLimitExpr.SMul
      _  =  the k * the L₁
            := by rw [AutoLimit.eq h_cond]
      _  =  the (k * L₁)
            := rfl

private instance funclimit_Neg {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim (-f) x₀
         =? - lim f x₀
            := FuncLimitExpr.Neg
      _  =  - the L₁
            := by rw [AutoLimit.eq h_cond]
      _  =  the (-L₁)
            := rfl

private instance funclimit_Neg' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := funclimit_Neg.eq

private instance funclimit_Inv {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim f⁻¹ x₀
         =? (lim f x₀)⁻¹
            := FuncLimitExpr.Inv
      _  =  (the L₁)⁻¹
            := by rw [AutoLimit.eq h_cond]
      _  =  the L₁⁻¹
            := by rw [UdEqual.calc_inv h_L_ne0]

private instance funclimit_Inv' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := funclimit_Inv.eq

private instance funclimit_Add {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f + g) x₀
         =? lim f x₀ + lim g x₀
            := FuncLimitExpr.Add
      _  =  the L₁ + the L₂
            := by rw [AutoLimit.eq h_cond₁, AutoLimit.eq h_cond₂]
      _  =  the (L₁ + L₂)
            := rfl

private instance funclimit_Add' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := funclimit_Add.eq

private instance funclimit_Sub {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f - g) x₀
         =? lim f x₀ - lim g x₀
            := FuncLimitExpr.Sub
      _  =  the L₁ - the L₂
            := by rw [AutoLimit.eq h_cond₁, AutoLimit.eq h_cond₂]
      _  =  the (L₁ - L₂)
            := rfl

private instance funclimit_Sub' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := funclimit_Sub.eq

private instance funclimit_Mul {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f * g) x₀
         =? lim f x₀ * lim g x₀
            := FuncLimitExpr.Mul
      _  =  the L₁ * the L₂
            := by rw [AutoLimit.eq h_cond₁, AutoLimit.eq h_cond₂]
      _  =  the (L₁ * L₂)
            := rfl

private instance funclimit_Mul' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := funclimit_Mul.eq

private instance funclimit_Div {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h_cond₁, h_cond₂, h_L₂_ne0⟩
    calc
            lim (f / g) x₀
         =? lim f x₀ / lim g x₀
            := FuncLimitExpr.Div
      _  =  the L₁ / the L₂
            := by rw [AutoLimit.eq h_cond₁, AutoLimit.eq h_cond₂]
      _  =  the (L₁ / L₂)
            := by rw [UdEqual.calc_div h_L₂_ne0]

private instance funclimit_Div' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := funclimit_Div.eq

private instance funclimit_Abs {x₀ : ℝ}
  : AutoLimit abs x₀ |x₀| True where
  eq := directly FuncLimitExpr.Abs

private instance funclimit_Sqrt {x₀ : ℝ}
  : AutoLimit sqrt x₀ √x₀ (x₀ > 0) where
  eq := FuncLimitExpr.Sqrt

private instance funclimit_Power {a x₀ : ℝ}
  : AutoLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  eq := FuncLimitExpr.Power

private instance funclimit_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := FuncLimitExpr.Power_ℤ

private instance funclimit_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply FuncLimitExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance funclimit_Exp {x₀ : ℝ}
  : AutoLimit exp x₀ (exp x₀) True where
  eq := directly FuncLimitExpr.Exp

private instance funclimit_Expow {a x₀ : ℝ}
  : AutoLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := FuncLimitExpr.Expow

private instance funclimit_Ln {x₀ : ℝ}
  : AutoLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := FuncLimitExpr.Ln

private instance funclimit_Log {a x₀ : ℝ}
  : AutoLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := FuncLimitExpr.Log

private instance funclimit_Sin {x₀ : ℝ}
  : AutoLimit sin x₀ (sin x₀) True where
  eq := directly FuncLimitExpr.Sin

private instance funclimit_Cos {x₀ : ℝ}
  : AutoLimit cos x₀ (cos x₀) True where
  eq := directly FuncLimitExpr.Cos

private instance funclimit_Tan {x₀ : ℝ}
  : AutoLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := FuncLimitExpr.Tan

private instance funclimit_Cot {x₀ : ℝ}
  : AutoLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := FuncLimitExpr.Cot

private instance funclimit_Sec {x₀ : ℝ}
  : AutoLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := FuncLimitExpr.Sec

private instance funclimit_Csc {x₀ : ℝ}
  : AutoLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := FuncLimitExpr.Csc

private instance funclimit_Sinh {x₀ : ℝ}
  : AutoLimit sinh x₀ (sinh x₀) True where
  eq := directly FuncLimitExpr.Sinh

private instance funclimit_Cosh {x₀ : ℝ}
  : AutoLimit cosh x₀ (cosh x₀) True where
  eq := directly FuncLimitExpr.Cosh

private instance funclimit_Tanh {x₀ : ℝ}
  : AutoLimit tanh x₀ (tanh x₀) True where
  eq := directly FuncLimitExpr.Tanh

private instance funclimit_Coth {x₀ : ℝ}
  : AutoLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := FuncLimitExpr.Coth

private instance funclimit_Sech {x₀ : ℝ}
  : AutoLimit sech x₀ (sech x₀) True where
  eq := directly FuncLimitExpr.Sech

private instance funclimit_Csch {x₀ : ℝ}
  : AutoLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := FuncLimitExpr.Csch

private instance funclimit_Arcsin {x₀ : ℝ}
  : AutoLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := FuncLimitExpr.Arcsin

private instance funclimit_Arccos {x₀ : ℝ}
  : AutoLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := FuncLimitExpr.Arccos

private instance funclimit_Arctan {x₀ : ℝ}
  : AutoLimit arctan x₀ (arctan x₀) True where
  eq := directly FuncLimitExpr.Arctan

private instance funclimit_Arccot {x₀ : ℝ}
  : AutoLimit arccot x₀ (arccot x₀) True where
  eq := directly FuncLimitExpr.Arccot

private instance funclimit_Arcsec {x₀ : ℝ}
  : AutoLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := FuncLimitExpr.Arcsec

private instance funclimit_Arccsc {x₀ : ℝ}
  : AutoLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := FuncLimitExpr.Arccsc

private instance funclimit_compAbs {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance funclimit_compAbs' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := funclimit_compAbs.eq

private instance funclimit_compSqrt {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance funclimit_compSqrt' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := funclimit_compSqrt.eq

private instance funclimit_compPower {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance funclimit_compPower' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance funclimit_compPower'' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance funclimit_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance funclimit_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance funclimit_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance funclimit_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp Nat.cast_pos.mpr id

private instance funclimit_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance funclimit_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance funclimit_compExp {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance funclimit_compExp' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := funclimit_compExp.eq

private instance funclimit_compExpow {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance funclimit_compExpow' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := funclimit_compExpow.eq

private instance funclimit_compLn {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance funclimit_compLn' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := funclimit_compLn.eq

private instance funclimit_compLog {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance funclimit_compLog' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := funclimit_compLog.eq

private instance funclimit_compSin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance funclimit_compSin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := funclimit_compSin.eq

private instance funclimit_compCos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance funclimit_compCos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := funclimit_compCos.eq

private instance funclimit_compTan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance funclimit_compTan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compTan.eq

private instance funclimit_compCot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance funclimit_compCot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCot.eq

private instance funclimit_compSec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance funclimit_compSec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compSec.eq

private instance funclimit_compCsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance funclimit_compCsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCsc.eq

private instance funclimit_compSinh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance funclimit_compSinh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := funclimit_compSinh.eq

private instance funclimit_compCosh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance funclimit_compCosh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := funclimit_compCosh.eq

private instance funclimit_compTanh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance funclimit_compTanh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := funclimit_compTanh.eq

private instance funclimit_compCoth {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance funclimit_compCoth' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCoth.eq

private instance funclimit_compSech {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance funclimit_compSech' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := funclimit_compSech.eq

private instance funclimit_compCsch {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance funclimit_compCsch' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCsch.eq

private instance funclimit_compArcsin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance funclimit_compArcsin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArcsin.eq

private instance funclimit_compArccos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance funclimit_compArccos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArccos.eq

private instance funclimit_compArctan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance funclimit_compArctan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := funclimit_compArctan.eq

private instance funclimit_compArccot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance funclimit_compArccot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := funclimit_compArccot.eq

private instance funclimit_compArcsec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance funclimit_compArcsec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArcsec.eq

private instance funclimit_compArccsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance funclimit_compArccsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArccsc.eq

lemma autoFuncLimit {f : ℝ → ℝ} {x₀ : ℝ} {L₁ : ℝ} {cond : Prop}
    [AutoLimit f x₀ L₁ cond] (h_cond : cond)
  : lim f x₀ = the L₁
:= AutoLimit.eq h_cond


/-! # Tactics -/

/-- ## Limit Expression Simplifier

    __Usage__ `lim_simp`

    - `lim_simp` calculates limit expressions as much as possible in standard forms.

    - Only used for limit expression, including
      - `SeqLimitExpr`
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`
      - `NegInftyLimitExpr`
      - `PosInftyLimitExpr`
      - `InftyLimitExpr`
-/
macro "lim_simp" : tactic => `(tactic| (
  repeat
    rw [autoFuncLimit]
    any_goals
      repeat any_goals apply And.intro
      try recover_form
      all_goals first
      | trivial
      | tauto
      | positivity
      | nlinarith
      | norm_num  -- the last choice
))


variable {x a b C : ℝ} {n : ℤ}

example
  : lim (const C) x = the C
:= by lim_simp

example
  : lim (fun _ ↦ 5) x = the 5
:= by lim_simp

example
  : lim id x = the x
:= by lim_simp

example
  : lim (·) x = the x
:= by lim_simp

example
  : lim (-·) x = the (-x)
:= by lim_simp

example (_ : x ≠ 0)
  : lim (·⁻¹) x = the (x⁻¹)
:= by lim_simp

example
  : lim abs x = the |x|
:= by lim_simp

example (_ : x > 0)
  : lim sqrt x = the √x
:= by lim_simp

example (_ : n > 0)
  : lim (· ^ n) x = the (x ^ n)
:= by lim_simp

example (_ : x > 0)
  : lim (· ^ a) x = the (x ^ a)
:= by lim_simp

example
  : lim exp x = the (exp x)
:= by lim_simp

example (_ : a > 0)
  : lim (a ^ ·) x = the (a ^ x)
:= by lim_simp

example (_ : x > 0)
  : lim ln x = the (ln x)
:= by lim_simp

example (_ : a > 0 ∧ a ≠ 1) (_ : x > 0)
  : lim (log a) x = the (log a x)
:= by lim_simp

example
  : lim sin x = the (sin x)
:= by lim_simp

example
  : lim cos x = the (cos x)
:= by lim_simp

example (_ : cos x ≠ 0)
  : lim tan x = the (tan x)
:= by lim_simp

example (_ : sin x ≠ 0)
  : lim cot x = the (cot x)
:= by lim_simp

example (_ : cos x ≠ 0)
  : lim sec x = the (sec x)
:= by lim_simp

example (_ : sin x ≠ 0)
  : lim csc x = the (csc x)
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim arcsin x = the (arcsin x)
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim arccos x = the (arccos x)
:= by lim_simp

example
  : lim arctan x = the (arctan x)
:= by lim_simp

example
  : lim arccot x = the (arccot x)
:= by lim_simp

example (_ : x < -1 ∨ x > 1)
  : lim arcsec x = the (arcsec x)
:= by lim_simp

example (_ : x < -1 ∨ x > 1)
  : lim arccsc x = the (arccsc x)
:= by lim_simp

example
  : lim sinh x = the (sinh x)
:= by lim_simp

example
  : lim cosh x = the (cosh x)
:= by lim_simp

example
  : lim tanh x = the (tanh x)
:= by lim_simp

example (_ : x ≠ 0)
  : lim coth x = the (coth x)
:= by lim_simp

example
  : lim sech x = the (sech x)
:= by lim_simp

example (_ : x ≠ 0)
  : lim csch x = the (csch x)
:= by lim_simp

example
  : lim (fun t ↦ sinh t) x = the (sinh x)
:= by lim_simp

example
  : lim (fun t ↦ cosh t) x = the (cosh x)
:= by lim_simp

example
  : lim (fun t ↦ tanh t) x = the (tanh x)
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim (fun t ↦ arcsin t) x = the (arcsin x)
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim (fun t ↦ arccos t) x = the (arccos x)
:= by lim_simp

example
  : lim (fun t ↦ arctan t) x = the (arctan x)
:= by lim_simp

example
  : lim (fun t ↦ |t|) x = the |x|
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ √t) x = the √x
:= by lim_simp

example (_ : x ≠ 0)
  : lim (fun t ↦ t⁻¹) x = the (x⁻¹)
:= by lim_simp

example
  : lim (fun t ↦ exp t) x = the (exp x)
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ ln t) x = the (ln x)
:= by lim_simp

example (_ : a > 0)
  : lim (fun t ↦ a ^ t) x = the (a ^ x)
:= by lim_simp

example
  : lim (sin + cos) x = the (sin x + cos x)
:= by lim_simp

example
  : lim (exp - id) x = the (exp x - x)
:= by lim_simp

example (_ : x > 0)
  : lim (id * ln) x = the (x * ln x)
:= by lim_simp

example (_ : x ≠ 0 ∧ cos x ≠ 0)
  : lim (tan / id) x = the (tan x / x)
:= by lim_simp

example
  : lim (fun t ↦ t + 3) x = the (x + 3)
:= by lim_simp

example
  : lim (fun t ↦ 2 * t) x = the (2 * x)
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ t - √t) x = the (x - √x)
:= by lim_simp

example
  : lim (fun t ↦ exp t * sin t) x = the (exp x * sin x)
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ ln t / t) x = the (ln x / x)
:= by lim_simp

example
  : lim (fun t ↦ t^2 + 5*t + 6) x = the (x^2 + 5*x + 6)
:= by lim_simp

example (_ : x - 1 ≠ 0)
  : lim (fun t ↦ (t + 1) / (t - 1)) x = the ((x + 1) / (x - 1))
:= by lim_simp

example
  : lim (fun t ↦ a * sin t + C * cos t) x = the (a * sin x + C * cos x)
:= by lim_simp

example
  : lim (fun t ↦ |t| + t) x = the (|x| + x)
:= by lim_simp

example
  : lim (fun t ↦ t^3 - 2*t^2 + t) x = the (x^3 - 2*x^2 + x)
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim (fun t ↦ arcsin t + arccos t) x = the (arcsin x + arccos x)
:= by lim_simp

example
  : lim (fun t ↦ sinh t + cosh t) x = the (sinh x + cosh x)
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ exp t + 2 ^ t) x = the (exp x + 2 ^ x)
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ log 10 t * ln t) x = the (log 10 x * ln x)
:= by lim_simp

example (_ : x ≠ 0)
  : lim (fun t ↦ t⁻¹ + t) x = the (x⁻¹ + x)
:= by lim_simp

example (_ : cos x ≠ 0) (_ : sin x ≠ 0)
  : lim (fun t ↦ sec t * csc t) x = the (sec x * csc x)
:= by lim_simp

example
  : lim (exp ∘ sin) x = the (exp (sin x))
:= by lim_simp

example (_ : cos x > 0)
  : lim (ln ∘ cos) x = the (ln (cos x))
:= by lim_simp

example
  : lim (sqrt ∘ exp) x = the (√(exp x))
:= by lim_simp

example (_ : x > 0)
  : lim (abs ∘ ln) x = the (|ln x|)
:= by lim_simp

example
  : lim (sin ∘ id) x = the (sin x)
:= by lim_simp

example
  : lim (cos ∘ (· ^ 2)) x = the (cos (x ^ 2))
:= by lim_simp

example (_ : x > 0 ∧ cos √x ≠ 0)
  : lim (tan ∘ sqrt) x = the (tan √x)
:= by lim_simp

example (_ : exp x > -1 ∧ exp x < 1)
  : lim (arcsin ∘ exp) x = the (arcsin (exp x))
:= by lim_simp

example (_ : x > 0 ∧ ln x > -1 ∧ ln x < 1)
  : lim (arccos ∘ ln) x = the (arccos (ln x))
:= by lim_simp

example
  : lim (arctan ∘ id) x = the (arctan x)
:= by lim_simp

example
  : lim (sinh ∘ cosh) x = the (sinh (cosh x))
:= by lim_simp

example (_ : x ≠ 0)
  : lim (log 2 ∘ abs) x = the (log 2 |x|)
:= by lim_simp

example
  : lim ((3 ^ ·) ∘ sin) x = the (3 ^ sin x)
:= by lim_simp

example (_ : cos x ≠ 0)
  : lim ((· ^ 3) ∘ tan) x = the (tan x ^ 3)
:= by lim_simp

example
  : lim ((C + ·) ∘ cos) x = the (C + cos x)
:= by lim_simp

example
  : lim ((-·) ∘ cos) x = the (-cos x)
:= by lim_simp

example
  : lim ((·⁻¹) ∘ sin) x = the ((sin x)⁻¹)
:= by lim_simp

example (_ : cos x ≠ 0 ∧ cos (tan x) ≠ 0)
  : lim (sec ∘ tan) x = the (sec (tan x))
:= by lim_simp

example (_ : sin x ≠ 0 ∧ sin (cot x) ≠ 0)
  : lim (csc ∘ cot) x = the (csc (cot x))
:= by lim_simp

example (_ : x > 0)
  : lim (sqrt ∘ sqrt) x = the (√(√x))
:= by lim_simp

example
  : lim (exp ∘ exp) x = the (exp (exp x))
:= by lim_simp

example
  : lim (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x))
:= by lim_simp

example
  : lim (fun t ↦ ln (t^2 + 1)) x = the (ln (x^2 + 1))
:= by lim_simp

example (_ : x > -1 ∧ x < 1)
  : lim (fun t ↦ √(1 - t^2)) x = the (√(1 - x^2))
:= by lim_simp

example (_ : n > 0)
  : lim (fun t ↦ (sin t)^n * (cos t)^n) x = the ((sin x)^n * (cos x)^n)
:= by lim_simp

example
  : lim (fun t ↦ t * exp (-t)) x = the (x * exp (-x))
:= by lim_simp

example (_ : sin x ≠ 0)
  : lim (fun t ↦ log 2 (abs (sin t))) x = the (log 2 (|sin x|))
:= by lim_simp

example
  : lim (fun t ↦ (t + a) ^ 5) x = the ((x + a) ^ 5)
:= by lim_simp

example (_ : a ≠ 0) (_ : x / a > -1 ∧ x / a < 1)
  : lim (fun t ↦ arcsin (t / a)) x = the (arcsin (x / a))
:= by lim_simp

example
  : lim (fun t ↦ arctan (exp t)) x = the (arctan (exp x))
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ cosh (ln t)) x = the (cosh (ln x))
:= by lim_simp

example (_ : a > 0)
  : lim (fun t ↦ a ^ (b * t)) x = the (a ^ (b * x))
:= by lim_simp

example (_ : π > 0)
  : lim (fun t ↦ 1 / √(2 * π) * exp (-t^2 / 2)) x = the (1 / √(2 * π) * exp (-x^2 / 2))
:= by lim_simp

example (_ : x > 0)
  : lim (fun t ↦ (ln t) / (t ^ a)) x = the ((ln x) / (x ^ a))
:= by lim_simp

example (_ : cos x ≠ 0)
  : lim (fun t ↦ sin (cos (tan t))) x = the (sin (cos (tan x)))
:= by lim_simp

example
  : lim (fun t ↦ |t ^ 3 - t| / (t ^ 2 + 1)) x = the (|x ^ 3 - x| / (x ^ 2 + 1))
:= by lim_simp
