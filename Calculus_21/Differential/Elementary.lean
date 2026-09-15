/-
    «Calculus_21».Differential.Elementary
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Rules
set_option linter.style.header false


/-! # Elementary Functions' Derivatives -/

/-- Constant Function's Derivative -/
theorem Constant_Deriv {C : ℝ}
  : ∀ x, Deriv (Constant C) x 0
:= by sorry

/-- Constant Function's Derivative (Expression) -/
theorem DerivExpr.Constant {C x₀ : ℝ}
  : D (const C) x₀ = the 0
:= by sorry

/-- Constant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Constant {C x₀ : ℝ}
  : D₋ (const C) x₀ = the 0
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Constant

/-- Constant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Constant {C x₀ : ℝ}
  : D₊ (const C) x₀ = the 0
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Constant

/-- Identity Function's Derivative -/
theorem Identity_Deriv
  : ∀ x, Deriv Identity x 1
:= by sorry

/-- Identity Function's Derivative (Expression) -/
theorem DerivExpr.Identity {x₀ : ℝ}
  : D id x₀ = the 1
:= by sorry

/-- Identity Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Identity {x₀ : ℝ}
  : D₋ id x₀ = the 1
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Identity

/-- Identity Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Identity {x₀ : ℝ}
  : D₊ id x₀ = the 1
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Identity

/-- Absolute Value Function's Derivative -/
theorem Abs_Deriv
  : ∀ x ≠ 0, Deriv Abs x (x / |x|)
:= by sorry

/-- Absolute Value Function's Derivative (Expression) -/
theorem DerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D abs x₀ = the (x₀ / |x₀|)
:= by sorry

/-- Absolute Value Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ abs x₀ = the (x₀ / |x₀|)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Abs h_dom)

/-- Absolute Value Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ abs x₀ = the (x₀ / |x₀|)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Abs h_dom)

/-- Square Root Function's Derivative -/
theorem Sqrt_Deriv
  : ∀ x > 0, Deriv Sqrt x (1 / (2 * √x))
:= by sorry

/-- Square Root Function's Derivative (Expression) -/
theorem DerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D sqrt x₀ = the (1 / (2 * √x₀))
:= by sorry

/-- Square Root Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ sqrt x₀ = the (1 / (2 * √x₀))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Sqrt h_dom)

/-- Square Root Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ sqrt x₀ = the (1 / (2 * √x₀))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Sqrt h_dom)

/-- Power Function's Derivative for `x > 0` -/
theorem Power_Deriv {a : ℝ}
  : ∀ x > 0, Deriv (Power a) x (a * x ^ (a - 1))
:= by sorry

/-- Power Function's Right Derivative at `0` -/
theorem Power_RightDeriv_0 {a : ℝ}
    (h_a : a > 0)
  : Deriv (Power a) 0 0
:= by sorry

/-- Power Function's Derivative for `n : ℤ`
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x = 0`. -/
theorem Power_Deriv_ℤ {n : ℤ}
  : ∀ x ∈ { x : ℝ | n > 0 ∨ x ≠ 0 }, Deriv (Power n) x (n * x ^ (n - 1))
:= by sorry

/-- Power Function's Derivative (Expression) -/
theorem DerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= by sorry

/-- Power Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Power h_dom)

/-- Power Function's Right Derivative (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `a = 1 ∧ x₀ = 0`. -/
theorem RightDerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∨ (a > 0 ∧ x₀ = 0))
  : D₊ (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= by sorry

/-- Power Function's Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
theorem DerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= by sorry

/-- Power Function's Left Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
theorem LeftDerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₋ (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Power_ℤ h_dom)

/-- Power Function's Right Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
theorem RightDerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₊ (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Power_ℤ h_dom)

/-- Natural Exponential Function's Derivative -/
theorem Exp_Deriv
  : ∀ x, Deriv Exp x (exp x)
:= by sorry

/-- Natural Exponential Function's Derivative (Expression) -/
theorem DerivExpr.Exp {x₀ : ℝ}
  : D exp x₀ = the (exp x₀)
:= by sorry

/-- Natural Exponential Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Exp {x₀ : ℝ}
  : D₋ exp x₀ = the (exp x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Exp

/-- Natural Exponential Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Exp {x₀ : ℝ}
  : D₊ exp x₀ = the (exp x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Exp

/-- Exponential Function's Derivative -/
theorem Expow_Deriv {a : ℝ}
    (h_a : a > 0)
  : ∀ x, Deriv (Expow a) x (ln a * a ^ x)
:= by sorry

/-- Exponential Function's Derivative (Expression) -/
theorem DerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= by sorry

/-- Exponential Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D₋ (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Expow h_dom)

/-- Exponential Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D₊ (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Expow h_dom)

/-- Natural Logarithm Function's Derivative -/
theorem Ln_Deriv
  : ∀ x > 0, Deriv Ln x x⁻¹
:= by sorry

/-- Natural Logarithm Function's Derivative (Expression) -/
theorem DerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D ln x₀ = the x₀⁻¹
:= by sorry

/-- Natural Logarithm Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ ln x₀ = the x₀⁻¹
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Ln h_dom)

/-- Natural Logarithm Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ ln x₀ = the x₀⁻¹
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Ln h_dom)

/-- Logarithm Function's Derivative -/
theorem Log_Deriv {a : ℝ}
    (h_a : a > 0 ∧ a ≠ 1)
  : ∀ x > 0, Deriv (Log a) x (ln a * x)⁻¹
:= by sorry

/-- Logarithm Function's Derivative (Expression) -/
theorem DerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D (log a) x₀ = the (ln a * x₀)⁻¹
:= by sorry

/-- Logarithm Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₋ (log a) x₀ = the (ln a * x₀)⁻¹
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Log h_dom)

/-- Logarithm Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₊ (log a) x₀ = the (ln a * x₀)⁻¹
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Log h_dom)

/-- Sine Function's Derivative -/
theorem Sin_Deriv
  : ∀ x, Deriv Sin x (cos x)
:= by sorry

/-- Sine Function's Derivative (Expression) -/
theorem DerivExpr.Sin {x₀ : ℝ}
  : D sin x₀ = the (cos x₀)
:= by sorry

/-- Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sin {x₀ : ℝ}
  : D₋ sin x₀ = the (cos x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Sin

/-- Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sin {x₀ : ℝ}
  : D₊ sin x₀ = the (cos x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Sin

/-- Cosine Function's Derivative -/
theorem Cos_Deriv
  : ∀ x, Deriv Cos x (- sin x)
:= by sorry

/-- Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Cos {x₀ : ℝ}
  : D cos x₀ = the (- sin x₀)
:= by sorry

/-- Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cos {x₀ : ℝ}
  : D₋ cos x₀ = the (- sin x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Cos

/-- Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cos {x₀ : ℝ}
  : D₊ cos x₀ = the (- sin x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Cos

/-- Tangent Function's Derivative -/
theorem Tan_Deriv
  : ∀ x ∈ Tan.domain, Deriv Tan x (sec x ^ 2)
:= by sorry

/-- Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D tan x₀ = the (sec x₀ ^ 2)
:= by sorry

/-- Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ tan x₀ = the (sec x₀ ^ 2)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Tan h_dom)

/-- Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ tan x₀ = the (sec x₀ ^ 2)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Tan h_dom)

/-- Cotangent Function's Derivative -/
theorem Cot_Deriv
  : ∀ x ∈ Cot.domain, Deriv Cot x (- csc x ^ 2)
:= by sorry

/-- Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D cot x₀ = the (- csc x₀ ^ 2)
:= by sorry

/-- Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ cot x₀ = the (- csc x₀ ^ 2)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Cot h_dom)

/-- Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ cot x₀ = the (- csc x₀ ^ 2)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Cot h_dom)

/-- Secant Function's Derivative -/
theorem Sec_Deriv
  : ∀ x ∈ Sec.domain, Deriv Sec x (tan x * sec x)
:= by sorry

/-- Secant Function's Derivative (Expression) -/
theorem DerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D sec x₀ = the (tan x₀ * sec x₀)
:= by sorry

/-- Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ sec x₀ = the (tan x₀ * sec x₀)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Sec h_dom)

/-- Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ sec x₀ = the (tan x₀ * sec x₀)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Sec h_dom)

/-- Cosecant Function's Derivative -/
theorem Csc_Deriv
  : ∀ x ∈ Csc.domain, Deriv Csc x (- cot x * csc x)
:= by sorry

/-- Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D csc x₀ = the (- cot x₀ * csc x₀)
:= by sorry

/-- Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ csc x₀ = the (- cot x₀ * csc x₀)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Csc h_dom)

/-- Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ csc x₀ = the (- cot x₀ * csc x₀)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Csc h_dom)

/-- Hyp-Sine Function's Derivative -/
theorem Sinh_Deriv
  : ∀ x, Deriv Sinh x (cosh x)
:= by sorry

/-- Hyp-Sine Function's Derivative (Expression) -/
theorem DerivExpr.Sinh {x₀ : ℝ}
  : D sinh x₀ = the (cosh x₀)
:= by sorry

/-- Hyp-Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sinh {x₀ : ℝ}
  : D₋ sinh x₀ = the (cosh x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Sinh

/-- Hyp-Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sinh {x₀ : ℝ}
  : D₊ sinh x₀ = the (cosh x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Sinh

/-- Hyp-Cosine Function's Derivative -/
theorem Cosh_Deriv
  : ∀ x, Deriv Cosh x (sinh x)
:= by sorry

/-- Hyp-Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Cosh {x₀ : ℝ}
  : D cosh x₀ = the (sinh x₀)
:= by sorry

/-- Hyp-Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cosh {x₀ : ℝ}
  : D₋ cosh x₀ = the (sinh x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Cosh

/-- Hyp-Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cosh {x₀ : ℝ}
  : D₊ cosh x₀ = the (sinh x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Cosh

/-- Hyp-Tangent Function's Derivative -/
theorem Tanh_Deriv
  : ∀ x, Deriv Tanh x (sech x ^ 2)
:= by sorry

/-- Hyp-Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Tanh {x₀ : ℝ}
  : D tanh x₀ = the (sech x₀ ^ 2)
:= by sorry

/-- Hyp-Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Tanh {x₀ : ℝ}
  : D₋ tanh x₀ = the (sech x₀ ^ 2)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Tanh

/-- Hyp-Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Tanh {x₀ : ℝ}
  : D₊ tanh x₀ = the (sech x₀ ^ 2)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Tanh

/-- Hyp-Cotangent Function's Derivative -/
theorem Coth_Deriv
  : ∀ x ≠ 0, Deriv Coth x (- csch x ^ 2)
:= by sorry

/-- Hyp-Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D coth x₀ = the (- csch x₀ ^ 2)
:= by sorry

/-- Hyp-Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ coth x₀ = the (- csch x₀ ^ 2)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Coth h_dom)

/-- Hyp-Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ coth x₀ = the (- csch x₀ ^ 2)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Coth h_dom)

/-- Hyp-Secant Function's Derivative -/
theorem Sech_Deriv
  : ∀ x, Deriv Sech x (- tanh x * sech x)
:= by sorry

/-- Hyp-Secant Function's Derivative (Expression) -/
theorem DerivExpr.Sech {x₀ : ℝ}
  : D sech x₀ = the (- tanh x₀ * sech x₀)
:= by sorry

/-- Hyp-Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sech {x₀ : ℝ}
  : D₋ sech x₀ = the (- tanh x₀ * sech x₀)
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Sech

/-- Hyp-Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sech {x₀ : ℝ}
  : D₊ sech x₀ = the (- tanh x₀ * sech x₀)
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Sech

/-- Hyp-Cosecant Function's Derivative -/
theorem Csch_Deriv
  : ∀ x ≠ 0, Deriv Csch x (- coth x * csch x)
:= by sorry

/-- Hyp-Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D csch x₀ = the (- coth x₀ * csch x₀)
:= by sorry

/-- Hyp-Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ csch x₀ = the (- coth x₀ * csch x₀)
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Csch h_dom)

/-- Hyp-Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ csch x₀ = the (- coth x₀ * csch x₀)
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Csch h_dom)

/-- Arc-Sine Function's Derivative -/
theorem Arcsin_Deriv
  : ∀ x ∈ Ioo (-1) 1, Deriv Arcsin x (1 / √(1 - x ^ 2))
:= by sorry

/-- Arc-Sine Function's Derivative (Expression) -/
theorem DerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= by sorry

/-- Arc-Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Arcsin h_dom)

/-- Arc-Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Arcsin h_dom)

/-- Arc-Cosine Function's Derivative -/
theorem Arccos_Deriv
  : ∀ x ∈ Ioo (-1) 1, Deriv Arccos x (-1 / √(1 - x ^ 2))
:= by sorry

/-- Arc-Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= by sorry

/-- Arc-Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Arccos h_dom)

/-- Arc-Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Arccos h_dom)

/-- Arc-Tangent Function's Derivative -/
theorem Arctan_Deriv
  : ∀ x, Deriv Arctan x (1 / (1 + x ^ 2))
:= by sorry

/-- Arc-Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Arctan {x₀ : ℝ}
  : D arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= by sorry

/-- Arc-Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arctan {x₀ : ℝ}
  : D₋ arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Arctan

/-- Arc-Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arctan {x₀ : ℝ}
  : D₊ arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Arctan

/-- Arc-Cotangent Function's Derivative -/
theorem Arccot_Deriv
  : ∀ x, Deriv Arccot x (-1 / (1 + x ^ 2))
:= by sorry

/-- Arc-Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Arccot {x₀ : ℝ}
  : D arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= by sorry

/-- Arc-Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccot {x₀ : ℝ}
  : D₋ arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= by exact leftDerivExpr_of_derivExpr DerivExpr.Arccot

/-- Arc-Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccot {x₀ : ℝ}
  : D₊ arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= by exact rightDerivExpr_of_derivExpr DerivExpr.Arccot

/-- Arc-Secant Function's Derivative -/
theorem Arcsec_Deriv
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arcsec x (1 / (|x| * √(x ^ 2 - 1)))
:= by sorry

/-- Arc-Secant Function's Derivative (Expression) -/
theorem DerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by sorry

/-- Arc-Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Arcsec h_dom)

/-- Arc-Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Arcsec h_dom)

/-- Arc-Cosecant Function's Derivative -/
theorem Arccsc_Deriv
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arccsc x (-1 / (|x| * √(x ^ 2 - 1)))
:= by sorry

/-- Arc-Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by sorry

/-- Arc-Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by exact leftDerivExpr_of_derivExpr (DerivExpr.Arccsc h_dom)

/-- Arc-Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by exact rightDerivExpr_of_derivExpr (DerivExpr.Arccsc h_dom)

page_end
