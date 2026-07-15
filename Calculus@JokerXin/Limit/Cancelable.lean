import «Calculus@JokerXin».Tactics
import «Calculus@JokerXin».Expr.Tactics
import «Calculus@JokerXin».Function.Continuity.Elementary


/- # To be Modified ↓ -/
/-! # Preparations -/

private class AutoCancelable (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  prop : cond → ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≠ 0

private instance cancelable_Constant {C x₀ : ℝ}
  : AutoCancelable (const C) x₀ C (C ≠ 0) where
  prop := sorry

private instance cancelable_Constant' {C x₀ : ℝ}
  : AutoCancelable (fun _ ↦ C) x₀ C (C ≠ 0) where
  prop := cancelable_Constant.prop

private instance cancelable_Identity {x₀ : ℝ}
  : AutoCancelable id x₀ x₀ True where
  prop := sorry

private instance cancelable_Identity' {x₀ : ℝ}
  : AutoCancelable (·) x₀ x₀ True where
  prop := cancelable_Identity.prop

private instance cancelable_SMul {f : ℝ → ℝ} {k x₀ L₁ : ℝ} {c : Prop}
    [AutoCancelable f x₀ L₁ c]
  : AutoCancelable (k • f) x₀ (k * L₁) (c ∧ k ≠ 0) where
  prop := sorry

private instance cancelable_Neg {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoCancelable f x₀ L₁ c]
  : AutoCancelable (-f) x₀ (-L₁) c where
  prop := sorry

private instance cancelable_Neg' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ - f x) x₀ (-L₁) c where
  prop := cancelable_Neg.prop

private instance cancelable_Inv {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoCancelable f x₀ L₁ c]
  : AutoCancelable f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  prop := sorry

private instance cancelable_Inv' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  prop := cancelable_Inv.prop

private instance cancelable_Add {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  prop := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f + g) x₀
         =? lim f x₀ + lim g x₀
            := FuncLimitExpr.Add
      _  =  the L₁ + the L₂
            := by rw [AutoCancelable.prop h_cond₁, AutoCancelable.prop h_cond₂]
      _  =  the (L₁ + L₂)
            := rfl

private instance cancelable_Add' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  prop := cancelable_Add.prop

private instance cancelable_Sub {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  prop := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f - g) x₀
         =? lim f x₀ - lim g x₀
            := FuncLimitExpr.Sub
      _  =  the L₁ - the L₂
            := by rw [AutoCancelable.prop h_cond₁, AutoCancelable.prop h_cond₂]
      _  =  the (L₁ - L₂)
            := rfl

private instance cancelable_Sub' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  prop := cancelable_Sub.prop

private instance cancelable_Mul {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  prop := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            lim (f * g) x₀
         =? lim f x₀ * lim g x₀
            := FuncLimitExpr.Mul
      _  =  the L₁ * the L₂
            := by rw [AutoCancelable.prop h_cond₁, AutoCancelable.prop h_cond₂]
      _  =  the (L₁ * L₂)
            := rfl

private instance cancelable_Mul' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  prop := cancelable_Mul.prop

private instance cancelable_Div {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  prop := by
    intro ⟨h_cond₁, h_cond₂, h_L₂_ne0⟩
    calc
            lim (f / g) x₀
         =? lim f x₀ / lim g x₀
            := FuncLimitExpr.Div
      _  =  the L₁ / the L₂
            := by rw [AutoCancelable.prop h_cond₁, AutoCancelable.prop h_cond₂]
      _  =  the (L₁ / L₂)
            := by rw [UdEqual.calc_div h_L₂_ne0]

private instance cancelable_Div' {f g : ℝ → ℝ} {x₀ L₁ L₂ : ℝ} {c₁ c₂ : Prop}
    [AutoCancelable f x₀ L₁ c₁] [AutoCancelable g x₀ L₂ c₂]
  : AutoCancelable (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  prop := cancelable_Div.prop

private instance cancelable_Abs {x₀ : ℝ}
  : AutoCancelable abs x₀ |x₀| True where
  prop := directly FuncLimitExpr.Abs

private instance cancelable_Sqrt {x₀ : ℝ}
  : AutoCancelable sqrt x₀ √x₀ (x₀ > 0) where
  prop := FuncLimitExpr.Sqrt

private instance cancelable_Power {a x₀ : ℝ}
  : AutoCancelable (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  prop := FuncLimitExpr.Power

private instance cancelable_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoCancelable (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  prop := FuncLimitExpr.Power_ℤ

private instance cancelable_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoCancelable (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  prop := by
    intro h_dom
    apply FuncLimitExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance cancelable_Exp {x₀ : ℝ}
  : AutoCancelable exp x₀ (exp x₀) True where
  prop := directly FuncLimitExpr.Exp

private instance cancelable_Expow {a x₀ : ℝ}
  : AutoCancelable (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  prop := FuncLimitExpr.Expow

private instance cancelable_Ln {x₀ : ℝ}
  : AutoCancelable ln x₀ (ln x₀) (x₀ > 0) where
  prop := FuncLimitExpr.Ln

private instance cancelable_Log {a x₀ : ℝ}
  : AutoCancelable (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  prop := FuncLimitExpr.Log

private instance cancelable_Sin {x₀ : ℝ}
  : AutoCancelable sin x₀ (sin x₀) True where
  prop := directly FuncLimitExpr.Sin

private instance cancelable_Cos {x₀ : ℝ}
  : AutoCancelable cos x₀ (cos x₀) True where
  prop := directly FuncLimitExpr.Cos

private instance cancelable_Tan {x₀ : ℝ}
  : AutoCancelable tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  prop := FuncLimitExpr.Tan

private instance cancelable_Cot {x₀ : ℝ}
  : AutoCancelable cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  prop := FuncLimitExpr.Cot

private instance cancelable_Sec {x₀ : ℝ}
  : AutoCancelable sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  prop := FuncLimitExpr.Sec

private instance cancelable_Csc {x₀ : ℝ}
  : AutoCancelable csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  prop := FuncLimitExpr.Csc

private instance cancelable_Sinh {x₀ : ℝ}
  : AutoCancelable sinh x₀ (sinh x₀) True where
  prop := directly FuncLimitExpr.Sinh

private instance cancelable_Cosh {x₀ : ℝ}
  : AutoCancelable cosh x₀ (cosh x₀) True where
  prop := directly FuncLimitExpr.Cosh

private instance cancelable_Tanh {x₀ : ℝ}
  : AutoCancelable tanh x₀ (tanh x₀) True where
  prop := directly FuncLimitExpr.Tanh

private instance cancelable_Coth {x₀ : ℝ}
  : AutoCancelable coth x₀ (coth x₀) (x₀ ≠ 0) where
  prop := FuncLimitExpr.Coth

private instance cancelable_Sech {x₀ : ℝ}
  : AutoCancelable sech x₀ (sech x₀) True where
  prop := directly FuncLimitExpr.Sech

private instance cancelable_Csch {x₀ : ℝ}
  : AutoCancelable csch x₀ (csch x₀) (x₀ ≠ 0) where
  prop := FuncLimitExpr.Csch

private instance cancelable_Arcsin {x₀ : ℝ}
  : AutoCancelable arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ < 1) where
  prop := FuncLimitExpr.Arcsin

private instance cancelable_Arccos {x₀ : ℝ}
  : AutoCancelable arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ < 1) where
  prop := FuncLimitExpr.Arccos

private instance cancelable_Arctan {x₀ : ℝ}
  : AutoCancelable arctan x₀ (arctan x₀) True where
  prop := directly FuncLimitExpr.Arctan

private instance cancelable_Arccot {x₀ : ℝ}
  : AutoCancelable arccot x₀ (arccot x₀) True where
  prop := directly FuncLimitExpr.Arccot

private instance cancelable_Arcsec {x₀ : ℝ}
  : AutoCancelable arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ > 1) where
  prop := FuncLimitExpr.Arcsec

private instance cancelable_Arccsc {x₀ : ℝ}
  : AutoCancelable arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ > 1) where
  prop := FuncLimitExpr.Arccsc

private instance cancelable_compAbs {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (abs ∘ f) x₀ (|L₁|) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Abs

private instance cancelable_compAbs' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ |f x|) x₀ |L₁| c where
  prop := cancelable_compAbs.prop

private instance cancelable_compSqrt {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance cancelable_compSqrt' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  prop := cancelable_compSqrt.prop

private instance cancelable_compPower {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Power h_dom

private instance cancelable_compPower' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  prop := cancelable_compPower.prop

private instance cancelable_compPower'' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  prop := cancelable_compPower.prop

private instance cancelable_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance cancelable_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := cancelable_compPower_ℤ.prop

private instance cancelable_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := cancelable_compPower_ℤ.prop

private instance cancelable_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp Nat.cast_pos.mpr id

private instance cancelable_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := cancelable_compPower_ℕ.prop

private instance cancelable_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  prop := cancelable_compPower_ℕ.prop

private instance cancelable_compExp {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (exp ∘ f) x₀ (exp L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Exp

private instance cancelable_compExp' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  prop := cancelable_compExp.prop

private instance cancelable_compExpow {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance cancelable_compExpow' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  prop := cancelable_compExpow.prop

private instance cancelable_compLn {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance cancelable_compLn' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  prop := cancelable_compLn.prop

private instance cancelable_compLog {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Log h_dom

private instance cancelable_compLog' {f : ℝ → ℝ} {a x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  prop := cancelable_compLog.prop

private instance cancelable_compSin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (sin ∘ f) x₀ (sin L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Sin

private instance cancelable_compSin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  prop := cancelable_compSin.prop

private instance cancelable_compCos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (cos ∘ f) x₀ (cos L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Cos

private instance cancelable_compCos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  prop := cancelable_compCos.prop

private instance cancelable_compTan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance cancelable_compTan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  prop := cancelable_compTan.prop

private instance cancelable_compCot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance cancelable_compCot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  prop := cancelable_compCot.prop

private instance cancelable_compSec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance cancelable_compSec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  prop := cancelable_compSec.prop

private instance cancelable_compCsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance cancelable_compCsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  prop := cancelable_compCsc.prop

private instance cancelable_compSinh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (sinh ∘ f) x₀ (sinh L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Sinh

private instance cancelable_compSinh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  prop := cancelable_compSinh.prop

private instance cancelable_compCosh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (cosh ∘ f) x₀ (cosh L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Cosh

private instance cancelable_compCosh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  prop := cancelable_compCosh.prop

private instance cancelable_compTanh {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (tanh ∘ f) x₀ (tanh L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Tanh

private instance cancelable_compTanh' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  prop := cancelable_compTanh.prop

private instance cancelable_compCoth {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance cancelable_compCoth' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  prop := cancelable_compCoth.prop

private instance cancelable_compSech {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (sech ∘ f) x₀ (sech L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Sech

private instance cancelable_compSech' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  prop := cancelable_compSech.prop

private instance cancelable_compCsch {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance cancelable_compCsch' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  prop := cancelable_compCsch.prop

private instance cancelable_compArcsin {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance cancelable_compArcsin' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  prop := cancelable_compArcsin.prop

private instance cancelable_compArccos {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance cancelable_compArccos' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  prop := cancelable_compArccos.prop

private instance cancelable_compArctan {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arctan ∘ f) x₀ (arctan L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arctan

private instance cancelable_compArctan' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  prop := cancelable_compArctan.prop

private instance cancelable_compArccot {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arccot ∘ f) x₀ (arccot L₁) c where
  prop := by
    intro h_cond
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arccot

private instance cancelable_compArccot' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  prop := cancelable_compArccot.prop

private instance cancelable_compArcsec {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance cancelable_compArcsec' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  prop := cancelable_compArcsec.prop

private instance cancelable_compArccsc {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  prop := by
    intro ⟨h_cond, h_dom⟩
    apply FuncLimitExpr.CompSV
    · exact h_f.prop h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance cancelable_compArccsc' {f : ℝ → ℝ} {x₀ L₁ : ℝ} {c : Prop}
    [h_f : AutoCancelable f x₀ L₁ c]
  : AutoCancelable (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  prop := cancelable_compArccsc.prop

lemma autoFuncLimit {f : ℝ → ℝ} {x₀ : ℝ} {L₁ : ℝ} {cond : Prop}
    [AutoCancelable f x₀ L₁ cond] (h_cond : cond)
  : lim f x₀ = the L₁
:= AutoCancelable.prop h_cond


/-! # Tactics -/

/-- ## Limit Expression Simplifier

    __Usage__ `lim_simp`

    - `lim_simp` calculates limit expressions as much as possible in standard forms.

    - Only used for limit expression, including
      - `SpropLimitExpr`
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`
      - `NegInftyLimitExpr`
      - `PosInftyLimitExpr`
      - `InftyLimitExpr`
-/
macro "lim_simp" : tactic => `(tactic| (
  try simp
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
