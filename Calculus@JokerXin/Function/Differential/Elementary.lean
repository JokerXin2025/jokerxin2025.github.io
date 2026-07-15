import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Function.Differential.Rules


/-! # Elementary Functions' Derivatives -/

/-- Constant Function's Derivative -/
lemma Constant_Deriv {C : ℝ}
  : ∀ x, Deriv (Constant C) x 0
:= sorry

/-- Constant Function's Derivative (Expression) -/
lemma DerivExpr.Constant {C x₀ : ℝ}
  : D (const C) x₀ = the 0
:= sorry

/-- Constant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Constant {C x₀ : ℝ}
  : D₋ (const C) x₀ = the 0
:= by
  calc
    D₋ (const C) x₀  =? D (const C) x₀
                        := DerivExpr.toLeft
    _                =  the 0
                        := DerivExpr.Constant

/-- Constant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Constant {C x₀ : ℝ}
  : D₊ (const C) x₀ = the 0
:= by
  calc
    D₊ (const C) x₀  =? D (const C) x₀
                        := DerivExpr.toRight
    _                =  the 0
                        := DerivExpr.Constant

/-- Identity Function's Derivative -/
lemma Identity_Deriv
  : ∀ x, Deriv Identity x 1
:= sorry

/-- Identity Function's Derivative (Expression) -/
lemma DerivExpr.Identity {x₀ : ℝ}
  : D (id : ℝ → ℝ) x₀ = the 1
:= sorry

/-- Identity Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Identity {x₀ : ℝ}
  : D₋ (id : ℝ → ℝ) x₀ = the 1
:= by
  calc
    D₋ (id : ℝ → ℝ) x₀  =? D (id : ℝ → ℝ) x₀
                           := DerivExpr.toLeft
    _                   =  the 1
                           := DerivExpr.Identity

/-- Identity Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Identity {x₀ : ℝ}
  : D₊ (id : ℝ → ℝ) x₀ = the 1
:= by
  calc
    D₊ (id : ℝ → ℝ) x₀  =? D (id : ℝ → ℝ) x₀
                           := DerivExpr.toRight
    _                   =  the 1
                           := DerivExpr.Identity

/-- Absolute Value Function's Derivative -/
lemma Abs_Deriv
  : ∀ x ≠ 0, Deriv Abs x (x / |x|)
:= sorry

/-- Absolute Value Function's Derivative (Expression) -/
lemma DerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D (abs : ℝ → ℝ) x₀ = the (x₀ / |x₀|)
:= sorry

/-- Absolute Value Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ (abs : ℝ → ℝ) x₀ = the (x₀ / |x₀|)
:= by
  calc
    D₋ (abs : ℝ → ℝ) x₀  =? D (abs : ℝ → ℝ) x₀
                            := DerivExpr.toLeft
    _                    =  the (x₀ / |x₀|)
                            := DerivExpr.Abs h_dom

/-- Absolute Value Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ (abs : ℝ → ℝ) x₀ = the (x₀ / |x₀|)
:= by
  calc
    D₊ (abs : ℝ → ℝ) x₀  =? D (abs : ℝ → ℝ) x₀
                            := DerivExpr.toRight
    _                    =  the (x₀ / |x₀|)
                            := DerivExpr.Abs h_dom

/-- Square Root Function's Derivative -/
lemma Sqrt_Deriv
  : ∀ x > 0, Deriv Sqrt x (1 / (2 * √x))
:= sorry

/-- Square Root Function's Derivative (Expression) -/
lemma DerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D sqrt x₀ = the (1 / (2 * √x₀))
:= sorry

/-- Square Root Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ sqrt x₀ = the (1 / (2 * √x₀))
:= by
  calc
    D₋ sqrt x₀  =? D sqrt x₀
                   := DerivExpr.toLeft
    _           =  the (1 / (2 * √x₀))
                   := DerivExpr.Sqrt h_dom

/-- Square Root Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ sqrt x₀ = the (1 / (2 * √x₀))
:= by
  calc
    D₊ sqrt x₀  =? D sqrt x₀
                   := DerivExpr.toRight
    _           =  the (1 / (2 * √x₀))
                   := DerivExpr.Sqrt h_dom

/-- Power Function's Derivative for `x > 0` -/
lemma Power_Deriv {a : ℝ}
  : ∀ x > 0, Deriv (Power a) x (a * x ^ (a - 1))
:= sorry

/-- Power Function's Right Derivative at `0` -/
lemma Power_RightDeriv_0 {a : ℝ}
    (h_a : a > 0)
  : Deriv (Power a) 0 0
:= sorry

/-- Power Function's Derivative for `n : ℤ`
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x = 0`. -/
lemma Power_Deriv_ℤ {n : ℤ}
  : ∀ x ∈ { x : ℝ | n > 0 ∨ x ≠ 0 }, Deriv (Power n) x (n * x ^ (n - 1))
:= sorry

/-- Power Function's Derivative (Expression) -/
lemma DerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- Power Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= by
  calc
    D₋ (pow a) x₀  =? D (pow a) x₀
                      := DerivExpr.toLeft
    _              =  the (a * x₀ ^ (a - 1))
                      := DerivExpr.Power h_dom

/-- Power Function's Right Derivative (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `a = 1 ∧ x₀ = 0`. -/
lemma RightDerivExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∨ (a > 0 ∧ x₀ = 0))
  : D₊ (pow a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry /-by
  calc
    D₊ (pow a) x₀  =? D (pow a) x₀
                      := DerivExpr.toRight
    _              =  the (a * x₀ ^ (a - 1))
                      := DerivExpr.Power h_dom-/

/-- Power Function's Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
lemma DerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= sorry

/-- Power Function's Left Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
lemma LeftDerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₋ (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= by
  calc
    D₋ (npow n) x₀  =? D (npow n) x₀
                       := DerivExpr.toLeft
    _               =  the (n * x₀ ^ (n - 1))
                       := DerivExpr.Power_ℤ h_dom

/-- Power Function's Right Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 = 1` will be used if `n = 1 ∧ x₀ = 0`. -/
lemma RightDerivExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₊ (npow n) x₀ = the (n * x₀ ^ (n - 1))
:= by
  calc
    D₊ (npow n) x₀  =? D (npow n) x₀
                       := DerivExpr.toRight
    _               =  the (n * x₀ ^ (n - 1))
                       := DerivExpr.Power_ℤ h_dom

/-- Natural Exponential Function's Derivative -/
lemma Exp_Deriv
  : ∀ x, Deriv Exp x (exp x)
:= sorry

/-- Natural Exponential Function's Derivative (Expression) -/
lemma DerivExpr.Exp {x₀ : ℝ}
  : D exp x₀ = the (exp x₀)
:= sorry

/-- Natural Exponential Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Exp {x₀ : ℝ}
  : D₋ exp x₀ = the (exp x₀)
:= by
  calc
    D₋ exp x₀  =? D exp x₀
                  := DerivExpr.toLeft
    _          =  the (exp x₀)
                  := DerivExpr.Exp

/-- Natural Exponential Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Exp {x₀ : ℝ}
  : D₊ exp x₀ = the (exp x₀)
:= by
  calc
    D₊ exp x₀  =? D exp x₀
                  := DerivExpr.toRight
    _          =  the (exp x₀)
                  := DerivExpr.Exp

/-- Exponential Function's Derivative -/
lemma Expow_Deriv {a : ℝ}
    (h_a : a > 0)
  : ∀ x, Deriv (Expow a) x (ln a * a ^ x)
:= sorry

/-- Exponential Function's Derivative (Expression) -/
lemma DerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= sorry

/-- Exponential Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D₋ (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= by
  calc
    D₋ (a ^ ·) x₀  =? D (a ^ ·) x₀
                        := DerivExpr.toLeft
    _                =  the (ln a * a ^ x₀)
                        := DerivExpr.Expow h_dom

/-- Exponential Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : D₊ (a ^ ·) x₀ = the (ln a * a ^ x₀)
:= by
  calc
    D₊ (a ^ ·) x₀  =? D (a ^ ·) x₀
                        := DerivExpr.toRight
    _                =  the (ln a * a ^ x₀)
                        := DerivExpr.Expow h_dom

/-- Natural Logarithm Function's Derivative -/
lemma Ln_Deriv
  : ∀ x > 0, Deriv Ln x (1 / x)
:= sorry

/-- Natural Logarithm Function's Derivative (Expression) -/
lemma DerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D ln x₀ = the (1 / x₀)
:= sorry

/-- Natural Logarithm Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ ln x₀ = the (1 / x₀)
:= by
  calc
    D₋ ln x₀  =? D ln x₀
                 := DerivExpr.toLeft
    _         =  the (1 / x₀)
                 := DerivExpr.Ln h_dom

/-- Natural Logarithm Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ ln x₀ = the (1 / x₀)
:= by
  calc
    D₊ ln x₀  =? D ln x₀
                 := DerivExpr.toRight
    _         =  the (1 / x₀)
                 := DerivExpr.Ln h_dom

/-- Logarithm Function's Derivative -/
lemma Log_Deriv {a : ℝ}
    (h_a : a > 0 ∧ a ≠ 1)
  : ∀ x > 0, Deriv (Log a) x (1 / (ln a * x))
:= sorry

/-- Logarithm Function's Derivative (Expression) -/
lemma DerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D (log a) x₀ = the (1 / (ln a * x₀))
:= sorry

/-- Logarithm Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₋ (log a) x₀ = the (1 / (ln a * x₀))
:= by
  calc
    D₋ (log a) x₀  =? D (log a) x₀
                      := DerivExpr.toLeft
    _              =  the (1 / (ln a * x₀))
                      := DerivExpr.Log h_dom

/-- Logarithm Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₊ (log a) x₀ = the (1 / (ln a * x₀))
:= by
  calc
    D₊ (log a) x₀  =? D (log a) x₀
                      := DerivExpr.toRight
    _              =  the (1 / (ln a * x₀))
                      := DerivExpr.Log h_dom

/-- Sine Function's Derivative -/
lemma Sin_Deriv
  : ∀ x, Deriv Sin x (cos x)
:= sorry

/-- Sine Function's Derivative (Expression) -/
lemma DerivExpr.Sin {x₀ : ℝ}
  : D sin x₀ = the (cos x₀)
:= sorry

/-- Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sin {x₀ : ℝ}
  : D₋ sin x₀ = the (cos x₀)
:= by
  calc
    D₋ sin x₀  =? D sin x₀
                  := DerivExpr.toLeft
    _          =  the (cos x₀)
                  := DerivExpr.Sin

/-- Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sin {x₀ : ℝ}
  : D₊ sin x₀ = the (cos x₀)
:= by
  calc
    D₊ sin x₀  =? D sin x₀
                  := DerivExpr.toRight
    _          =  the (cos x₀)
                  := DerivExpr.Sin

/-- Cosine Function's Derivative -/
lemma Cos_Deriv
  : ∀ x, Deriv Cos x (- sin x)
:= sorry

/-- Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Cos {x₀ : ℝ}
  : D cos x₀ = the (- sin x₀)
:= sorry

/-- Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cos {x₀ : ℝ}
  : D₋ cos x₀ = the (- sin x₀)
:= by
  calc
    D₋ cos x₀  =? D cos x₀
                  := DerivExpr.toLeft
    _          =  the (- sin x₀)
                  := DerivExpr.Cos

/-- Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cos {x₀ : ℝ}
  : D₊ cos x₀ = the (- sin x₀)
:= by
  calc
    D₊ cos x₀  =? D cos x₀
                  := DerivExpr.toRight
    _          =  the (- sin x₀)
                  := DerivExpr.Cos

/-- Tangent Function's Derivative -/
lemma Tan_Deriv
  : ∀ x ∈ Tan.domain, Deriv Tan x (sec x ^ 2)
:= sorry

/-- Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D tan x₀ = the (sec x₀ ^ 2)
:= sorry

/-- Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ tan x₀ = the (sec x₀ ^ 2)
:= by
  calc
    D₋ tan x₀  =? D tan x₀
                  := DerivExpr.toLeft
    _          =  the (sec x₀ ^ 2)
                  := DerivExpr.Tan h_dom

/-- Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ tan x₀ = the (sec x₀ ^ 2)
:= by
  calc
    D₊ tan x₀  =? D tan x₀
                  := DerivExpr.toRight
    _          =  the (sec x₀ ^ 2)
                  := DerivExpr.Tan h_dom

/-- Cotangent Function's Derivative -/
lemma Cot_Deriv
  : ∀ x ∈ Cot.domain, Deriv Cot x (- csc x ^ 2)
:= sorry

/-- Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D cot x₀ = the (- csc x₀ ^ 2)
:= sorry

/-- Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ cot x₀ = the (- csc x₀ ^ 2)
:= by
  calc
    D₋ cot x₀  =? D cot x₀
                  := DerivExpr.toLeft
    _          =  the (- csc x₀ ^ 2)
                  := DerivExpr.Cot h_dom

/-- Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ cot x₀ = the (- csc x₀ ^ 2)
:= by
  calc
    D₊ cot x₀  =? D cot x₀
                  := DerivExpr.toRight
    _          =  the (- csc x₀ ^ 2)
                  := DerivExpr.Cot h_dom

/-- Secant Function's Derivative -/
lemma Sec_Deriv
  : ∀ x ∈ Sec.domain, Deriv Sec x (tan x * sec x)
:= sorry

/-- Secant Function's Derivative (Expression) -/
lemma DerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D sec x₀ = the (tan x₀ * sec x₀)
:= sorry

/-- Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ sec x₀ = the (tan x₀ * sec x₀)
:= by
  calc
    D₋ sec x₀  =? D sec x₀
                  := DerivExpr.toLeft
    _          =  the (tan x₀ * sec x₀)
                  := DerivExpr.Sec h_dom

/-- Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ sec x₀ = the (tan x₀ * sec x₀)
:= by
  calc
    D₊ sec x₀  =? D sec x₀
                  := DerivExpr.toRight
    _          =  the (tan x₀ * sec x₀)
                  := DerivExpr.Sec h_dom

/-- Cosecant Function's Derivative -/
lemma Csc_Deriv
  : ∀ x ∈ Csc.domain, Deriv Csc x (- cot x * csc x)
:= sorry

/-- Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D csc x₀ = the (- cot x₀ * csc x₀)
:= sorry

/-- Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ csc x₀ = the (- cot x₀ * csc x₀)
:= by
  calc
    D₋ csc x₀  =? D csc x₀
                  := DerivExpr.toLeft
    _          =  the (- cot x₀ * csc x₀)
                  := DerivExpr.Csc h_dom

/-- Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ csc x₀ = the (- cot x₀ * csc x₀)
:= by
  calc
    D₊ csc x₀  =? D csc x₀
                  := DerivExpr.toRight
    _          =  the (- cot x₀ * csc x₀)
                  := DerivExpr.Csc h_dom

/-- Hyp-Sine Function's Derivative -/
lemma Sinh_Deriv
  : ∀ x, Deriv Sinh x (cosh x)
:= sorry

/-- Hyp-Sine Function's Derivative (Expression) -/
lemma DerivExpr.Sinh {x₀ : ℝ}
  : D sinh x₀ = the (cosh x₀)
:= sorry

/-- Hyp-Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sinh {x₀ : ℝ}
  : D₋ sinh x₀ = the (cosh x₀)
:= by
  calc
    D₋ sinh x₀  =? D sinh x₀
                   := DerivExpr.toLeft
    _           =  the (cosh x₀)
                   := DerivExpr.Sinh

/-- Hyp-Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sinh {x₀ : ℝ}
  : D₊ sinh x₀ = the (cosh x₀)
:= by
  calc
    D₊ sinh x₀  =? D sinh x₀
                   := DerivExpr.toRight
    _           =  the (cosh x₀)
                   := DerivExpr.Sinh

/-- Hyp-Cosine Function's Derivative -/
lemma Cosh_Deriv
  : ∀ x, Deriv Cosh x (sinh x)
:= sorry

/-- Hyp-Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Cosh {x₀ : ℝ}
  : D cosh x₀ = the (sinh x₀)
:= sorry

/-- Hyp-Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cosh {x₀ : ℝ}
  : D₋ cosh x₀ = the (sinh x₀)
:= by
  calc
    D₋ cosh x₀  =? D cosh x₀
                   := DerivExpr.toLeft
    _           =  the (sinh x₀)
                   := DerivExpr.Cosh

/-- Hyp-Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cosh {x₀ : ℝ}
  : D₊ cosh x₀ = the (sinh x₀)
:= by
  calc
    D₊ cosh x₀  =? D cosh x₀
                   := DerivExpr.toRight
    _           =  the (sinh x₀)
                   := DerivExpr.Cosh

/-- Hyp-Tangent Function's Derivative -/
lemma Tanh_Deriv
  : ∀ x, Deriv Tanh x (sech x ^ 2)
:= sorry

/-- Hyp-Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Tanh {x₀ : ℝ}
  : D tanh x₀ = the (sech x₀ ^ 2)
:= sorry

/-- Hyp-Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Tanh {x₀ : ℝ}
  : D₋ tanh x₀ = the (sech x₀ ^ 2)
:= by
  calc
    D₋ tanh x₀  =? D tanh x₀
                   := DerivExpr.toLeft
    _           =  the (sech x₀ ^ 2)
                   := DerivExpr.Tanh

/-- Hyp-Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Tanh {x₀ : ℝ}
  : D₊ tanh x₀ = the (sech x₀ ^ 2)
:= by
  calc
    D₊ tanh x₀  =? D tanh x₀
                   := DerivExpr.toRight
    _           =  the (sech x₀ ^ 2)
                   := DerivExpr.Tanh

/-- Hyp-Cotangent Function's Derivative -/
lemma Coth_Deriv
  : ∀ x ≠ 0, Deriv Coth x (- csch x ^ 2)
:= sorry

/-- Hyp-Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D coth x₀ = the (- csch x₀ ^ 2)
:= sorry

/-- Hyp-Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ coth x₀ = the (- csch x₀ ^ 2)
:= by
  calc
    D₋ coth x₀  =? D coth x₀
                   := DerivExpr.toLeft
    _           =  the (- csch x₀ ^ 2)
                   := DerivExpr.Coth h_dom

/-- Hyp-Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ coth x₀ = the (- csch x₀ ^ 2)
:= by
  calc
    D₊ coth x₀  =? D coth x₀
                   := DerivExpr.toRight
    _           =  the (- csch x₀ ^ 2)
                   := DerivExpr.Coth h_dom

/-- Hyp-Secant Function's Derivative -/
lemma Sech_Deriv
  : ∀ x, Deriv Sech x (- tanh x * sech x)
:= sorry

/-- Hyp-Secant Function's Derivative (Expression) -/
lemma DerivExpr.Sech {x₀ : ℝ}
  : D sech x₀ = the (- tanh x₀ * sech x₀)
:= sorry

/-- Hyp-Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sech {x₀ : ℝ}
  : D₋ sech x₀ = the (- tanh x₀ * sech x₀)
:= by
  calc
    D₋ sech x₀  =? D sech x₀
                   := DerivExpr.toLeft
    _           =  the (- tanh x₀ * sech x₀)
                   := DerivExpr.Sech

/-- Hyp-Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sech {x₀ : ℝ}
  : D₊ sech x₀ = the (- tanh x₀ * sech x₀)
:= by
  calc
    D₊ sech x₀  =? D sech x₀
                   := DerivExpr.toRight
    _           =  the (- tanh x₀ * sech x₀)
                   := DerivExpr.Sech

/-- Hyp-Cosecant Function's Derivative -/
lemma Csch_Deriv
  : ∀ x ≠ 0, Deriv Csch x (- coth x * csch x)
:= sorry

/-- Hyp-Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D csch x₀ = the (- coth x₀ * csch x₀)
:= sorry

/-- Hyp-Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ csch x₀ = the (- coth x₀ * csch x₀)
:= by
  calc
    D₋ csch x₀  =? D csch x₀
                   := DerivExpr.toLeft
    _           =  the (- coth x₀ * csch x₀)
                   := DerivExpr.Csch h_dom

/-- Hyp-Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ csch x₀ = the (- coth x₀ * csch x₀)
:= by
  calc
    D₊ csch x₀  =? D csch x₀
                   := DerivExpr.toRight
    _           =  the (- coth x₀ * csch x₀)
                   := DerivExpr.Csch h_dom

/-- Arc-Sine Function's Derivative -/
lemma Arcsin_Deriv
  : ∀ x ∈ Ioo (-1) 1, Deriv Arcsin x (1 / √(1 - x ^ 2))
:= sorry

/-- Arc-Sine Function's Derivative (Expression) -/
lemma DerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= sorry

/-- Arc-Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= by
  calc
    D₋ arcsin x₀  =? D arcsin x₀
                     := DerivExpr.toLeft
    _             =  the (1 / √(1 - x₀ ^ 2))
                     := DerivExpr.Arcsin h_dom

/-- Arc-Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arcsin x₀ = the (1 / √(1 - x₀ ^ 2))
:= by
  calc
    D₊ arcsin x₀  =? D arcsin x₀
                     := DerivExpr.toRight
    _             =  the (1 / √(1 - x₀ ^ 2))
                     := DerivExpr.Arcsin h_dom

/-- Arc-Cosine Function's Derivative -/
lemma Arccos_Deriv
  : ∀ x ∈ Ioo (-1) 1, Deriv Arccos x (-1 / √(1 - x ^ 2))
:= sorry

/-- Arc-Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= sorry

/-- Arc-Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= by
  calc
    D₋ arccos x₀  =? D arccos x₀
                     := DerivExpr.toLeft
    _             =  the (-1 / √(1 - x₀ ^ 2))
                     := DerivExpr.Arccos h_dom

/-- Arc-Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arccos x₀ = the (-1 / √(1 - x₀ ^ 2))
:= by
  calc
    D₊ arccos x₀  =? D arccos x₀
                     := DerivExpr.toRight
    _             =  the (-1 / √(1 - x₀ ^ 2))
                     := DerivExpr.Arccos h_dom

/-- Arc-Tangent Function's Derivative -/
lemma Arctan_Deriv
  : ∀ x, Deriv Arctan x (1 / (1 + x ^ 2))
:= sorry

/-- Arc-Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Arctan {x₀ : ℝ}
  : D arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= sorry

/-- Arc-Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arctan {x₀ : ℝ}
  : D₋ arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= by
  calc
    D₋ arctan x₀  =? D arctan x₀
                     := DerivExpr.toLeft
    _             =  the (1 / (1 + x₀ ^ 2))
                     := DerivExpr.Arctan

/-- Arc-Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arctan {x₀ : ℝ}
  : D₊ arctan x₀ = the (1 / (1 + x₀ ^ 2))
:= by
  calc
    D₊ arctan x₀  =? D arctan x₀
                     := DerivExpr.toRight
    _             =  the (1 / (1 + x₀ ^ 2))
                     := DerivExpr.Arctan

/-- Arc-Cotangent Function's Derivative -/
lemma Arccot_Deriv
  : ∀ x, Deriv Arccot x (-1 / (1 + x ^ 2))
:= sorry

/-- Arc-Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Arccot {x₀ : ℝ}
  : D arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= sorry

/-- Arc-Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccot {x₀ : ℝ}
  : D₋ arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= by
  calc
    D₋ arccot x₀  =? D arccot x₀
                     := DerivExpr.toLeft
    _             =  the (-1 / (1 + x₀ ^ 2))
                     := DerivExpr.Arccot

/-- Arc-Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccot {x₀ : ℝ}
  : D₊ arccot x₀ = the (-1 / (1 + x₀ ^ 2))
:= by
  calc
    D₊ arccot x₀  =? D arccot x₀
                     := DerivExpr.toRight
    _             =  the (-1 / (1 + x₀ ^ 2))
                     := DerivExpr.Arccot

/-- Arc-Secant Function's Derivative -/
lemma Arcsec_Deriv
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arcsec x (1 / (|x| * √(x ^ 2 - 1)))
:= sorry

/-- Arc-Secant Function's Derivative (Expression) -/
lemma DerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= sorry

/-- Arc-Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by
  calc
    D₋ arcsec x₀  =? D arcsec x₀
                     := DerivExpr.toLeft
    _             =  the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
                     := DerivExpr.Arcsec h_dom

/-- Arc-Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arcsec x₀ = the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by
  calc
    D₊ arcsec x₀  =? D arcsec x₀
                     := DerivExpr.toRight
    _             =  the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
                     := DerivExpr.Arcsec h_dom

/-- Arc-Cosecant Function's Derivative -/
lemma Arccsc_Deriv
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arccsc x (-1 / (|x| * √(x ^ 2 - 1)))
:= sorry

/-- Arc-Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= sorry

/-- Arc-Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by
  calc
    D₋ arccsc x₀  =? D arccsc x₀
                     := DerivExpr.toLeft
    _             =  the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
                     := DerivExpr.Arccsc h_dom

/-- Arc-Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arccsc x₀ = the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by
  calc
    D₊ arccsc x₀  =? D arccsc x₀
                     := DerivExpr.toRight
    _             =  the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
                     := DerivExpr.Arccsc h_dom
