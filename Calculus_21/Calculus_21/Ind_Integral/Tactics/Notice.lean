/-
    «Calculus_21».Ind_Integral.Tactics.Notice
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Ind_Integral.Expr
import «Calculus_21».Differential.Tactic
set_option linter.style.header false


/-! # Preparations -/

class AutoIndefIntegral (F : ℝ → ℝ)
    (f : outParam (ℝ → ℝ)) (cond : outParam Prop) where
  eq : cond → ∫ f = the ⟦F⟧

private instance indefIntegral_patch₁ {k : ℝ}
  : AutoIndefIntegral (k + ·) (fun _ ↦ 1) True where
  eq := sorry

private instance indefIntegral_patch₁' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((k + ·) ∘ F) (fun x ↦ f x) c where
  eq := sorry

private instance indefIntegral_patch₂ {k : ℝ}
  : AutoIndefIntegral (k - ·) (fun _ ↦ -1) True where
  eq := sorry

private instance indefIntegral_patch₂' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((k - ·) ∘ F) (fun x ↦ - f x) c where
  eq := sorry

private instance indefIntegral_patch₃ {k : ℝ}
  : AutoIndefIntegral (k * ·) (fun _ ↦ k) True where
  eq := sorry

private instance indefIntegral_patch₃' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((k * ·) ∘ F) (fun x ↦ k * f x) c where
  eq := sorry

private instance indefIntegral_patch₄ {k : ℝ}
  : AutoIndefIntegral (k / ·) (fun x ↦ -k / x ^ 2) True where
  eq := sorry

private instance indefIntegral_patch₄' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((k / ·) ∘ F) (fun x ↦ -k * f x / F x ^ 2) c where
  eq := sorry

private instance indefIntegral_patch₅
  : AutoIndefIntegral (-·) (fun _ ↦ -1) True where
  eq := sorry

private instance indefIntegral_patch₅' {f F : ℝ → ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((-·) ∘ F) (fun x ↦ - f x) c where
  eq := sorry

private instance indefIntegral_patch₆
  : AutoIndefIntegral (·⁻¹) (fun x ↦ -1 / x ^ 2) True where
  eq := sorry

private instance indefIntegral_patch₆' {f F : ℝ → ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral ((·⁻¹) ∘ F) (fun x ↦ - f x / F x ^ 2) c where
  eq := sorry

private instance indefIntegral_is_Constant {C : ℝ}
  : AutoIndefIntegral (fun _ ↦ C) (fun _ ↦ 0) True where
  eq := sorry

private instance indefIntegral_is_Identity
  : AutoIndefIntegral (·) (fun _ ↦ 1) True where
  eq := sorry

private instance indefIntegral_SMul {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral (fun x ↦ k * F x) (fun x ↦ k * f x) c where
  eq := sorry

private instance indefIntegral_Neg {f F : ℝ → ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral (fun x ↦ - F x) (fun x ↦ - f x) c where
  eq := sorry

private instance indefIntegral_Inv {f F : ℝ → ℝ} {c : Prop}
    [AutoIndefIntegral F f c]
  : AutoIndefIntegral (fun x ↦ (F x)⁻¹) (fun x ↦ - f x / F x ^ 2) c where
  eq := sorry

private instance indefIntegral_Add {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoIndefIntegral F f c₁] [AutoIndefIntegral G g c₂]
  : AutoIndefIntegral (fun x ↦ F x + G x) (fun x ↦ f x + g x) (c₁ ∧ c₂) where
  eq := sorry

private instance indefIntegral_Sub {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoIndefIntegral F f c₁] [AutoIndefIntegral G g c₂]
  : AutoIndefIntegral (fun x ↦ F x - G x) (fun x ↦ f x - g x) (c₁ ∧ c₂) where
  eq := sorry

private instance indefIntegral_Mul {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoIndefIntegral F f c₁] [AutoIndefIntegral G g c₂]
  : AutoIndefIntegral (fun x ↦ F x * G x) (fun x ↦ f x * G x + F x * g x) (c₁ ∧ c₂) where
  eq := sorry

private instance indefIntegral_Div {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoIndefIntegral F f c₁] [AutoIndefIntegral G g c₂]
  : AutoIndefIntegral (fun x ↦ F x / G x)
    (fun x ↦ (f x * G x - F x * g x) / G x ^ 2) (c₁ ∧ c₂) where
  eq := sorry

private instance indefIntegral_is_Abs
  : AutoIndefIntegral (|·|) (fun x ↦ x / |x|) True where
  eq := sorry

private instance indefIntegral_is_Sqrt
  : AutoIndefIntegral (√·) (fun x ↦ 1 / (2 * √x)) True where
  eq := sorry

private instance indefIntegral_is_Power {a : ℝ}
  : AutoIndefIntegral (· ^ a) (fun x ↦ a * x ^ (a - 1)) True where
  eq := sorry

private instance indefIntegral_is_Power_ℤ {n : ℤ}
  : AutoIndefIntegral (· ^ n) (fun x ↦ n * x ^ (n - 1)) True where
  eq := sorry

private instance indefIntegral_is_Power_ℕ {n : ℕ}
  : AutoIndefIntegral (· ^ n) (fun x ↦ n * x ^ (n - 1)) True where
  eq := sorry

private instance indefIntegral_is_Exp
  : AutoIndefIntegral exp (fun x ↦ exp x) True where
  eq := sorry

private instance indefIntegral_is_Expow {a : ℝ}
  : AutoIndefIntegral (a ^ ·) (fun x ↦ ln a * a ^ x) (a > 0) where
  eq := sorry

private instance indefIntegral_is_Ln
  : AutoIndefIntegral ln (fun x ↦ x⁻¹) True where
  eq := sorry

private instance indefIntegral_is_LnAbs
  : AutoIndefIntegral (ln |·|) (fun x ↦ x⁻¹) True where
  eq := sorry

private instance indefIntegral_is_Log {a : ℝ}
  : AutoIndefIntegral (log a) (fun x ↦ (ln a * x)⁻¹) (a > 0 ∧ a ≠ 1) where
  eq := sorry

private instance indefIntegral_is_LogAbs {a : ℝ}
  : AutoIndefIntegral (log a |·|) (fun x ↦ (ln a * x)⁻¹) (a > 0 ∧ a ≠ 1) where
  eq := sorry

private instance indefIntegral_is_Sin
  : AutoIndefIntegral sin (fun x ↦ cos x) True where
  eq := sorry

private instance indefIntegral_is_Cos
  : AutoIndefIntegral cos (fun x ↦ - sin x) True where
  eq := sorry

private instance indefIntegral_is_Tan
  : AutoIndefIntegral tan (fun x ↦ sec x ^ 2) True where
  eq := sorry

private instance indefIntegral_is_Cot
  : AutoIndefIntegral cot (fun x ↦ - csc x ^ 2) True where
  eq := sorry

private instance indefIntegral_is_Sec
  : AutoIndefIntegral sec (fun x ↦ tan x * sec x) True where
  eq := sorry

private instance indefIntegral_is_Csc
  : AutoIndefIntegral csc (fun x ↦ - cot x * csc x) True where
  eq := sorry

lemma autoIndefIntegral {f F : ℝ → ℝ} {cond : Prop}
    [AutoIndefIntegral F f cond] (h_cond : cond)
  : ∫ f = the ⟦F⟧
:= AutoIndefIntegral.eq h_cond


/-! # Tactics -/

macro "int_notice" : tactic => `(tactic| (
  intros
  try simp only [except_bind_ok, except_pure_ok, addC_val, addC_func]
  repeat rw [← autoIndefIntegral]
  all_goals try {auto_side_condition}
  all_goals try {congr; auto_eq}
))

/- 经典写法 -/
example
  : ∫ cos = the (sin +C)
 := by sorry

/- 等价类写法 -/
example
  : ∫ exp = the ⟦exp⟧
 := by sorry

/- 记号 `+C` 与常数 `C` 兼容性 -/
example {C : ℝ}
  : ∫ (fun _ ↦ 1) = the (fun x ↦ x + C +C)
 := by sorry

/- 牛刀小试 -/
example {n : ℕ}
  : ∫ (fun x ↦ x ^ n) = the (fun x ↦ x ^ (n + 1) / (n + 1 : ℝ) +C)
:= by sorry

/- 上点强度 -/
example
  : ∫ (fun x ↦ exp x * (x * (sin x + cos x) - sin x) / x ^ 2)
    = the (fun x ↦ exp x * sin x / x +C)
:= by sorry

page_end
