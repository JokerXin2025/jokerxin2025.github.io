/-
    «Calculus_21».Limit.Expr.Elementary
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.BasicRules
import «Calculus_21».Limit.Elementary
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


section
variable {n : ℤ} {C a x₀ : ℝ}

/-- Constant Function's Limit (Expression) -/
lemma FuncLimitExpr.Constant
  : lim (const C) x₀ =. the C
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Constant x₀ (mem_univ x₀) |>.right

/-- Constant Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Constant
  : lim₋ (const C) x₀ =. the C
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Constant

/-- Constant Function's Right Limit (Expression) -/
lemma RightLimitExpr.Constant
  : lim₊ (const C) x₀ =. the C
:= FuncLimitExpr.toRight <| FuncLimitExpr.Constant

/-- Constant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Constant
  : lim pos_infty (const C) =. the C
:= sorry

/-- Constant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Constant
  : lim neg_infty (const C) =. the C
:= sorry

/-- Constant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Constant
  : lim infty (const C) =. the C
:= sorry

/-- Identity Function's Limit (Expression) -/
lemma FuncLimitExpr.Identity
  : lim id x₀ =. the x₀
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Identity x₀ (mem_univ x₀) |>.right

/-- Identity Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Identity
  : lim₋ id x₀ =. the x₀
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Identity

/-- Identity Function's Right Limit (Expression) -/
lemma RightLimitExpr.Identity
  : lim₊ id x₀ =. the x₀
:= FuncLimitExpr.toRight <| FuncLimitExpr.Identity

/-- Identity Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Identity
  : lim pos_infty id = pos_infty
:= sorry

/-- Identity Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Identity
  : lim neg_infty id = neg_infty
:= sorry

/-- Identity Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Identity
  : lim infty id = infty
:= sorry

/-- Absolute Value Function's Limit (Expression) -/
lemma FuncLimitExpr.Abs
  : lim abs x₀ =. the |x₀|
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Abs x₀ (mem_univ x₀) |>.right

/-- Absolute Value Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Abs
  : lim₋ abs x₀ =. the |x₀|
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Abs

/-- Absolute Value Function's Right Limit (Expression) -/
lemma RightLimitExpr.Abs
  : lim₊ abs x₀ =. the |x₀|
:= FuncLimitExpr.toRight <| FuncLimitExpr.Abs

/-- Absolute Value Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Abs
  : lim pos_infty abs = pos_infty
:= sorry

/-- Absolute Value Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Abs
  : lim neg_infty abs = pos_infty
:= sorry

/-- Absolute Value Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Abs
  : lim infty abs = pos_infty
:= sorry

/-- Square Root Function's Limit at `x₀ > 0` (Expression) -/
lemma FuncLimitExpr.Sqrt
    (h_dom : x₀ > 0)
  : lim sqrt x₀ =. the (√x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Sqrt x₀ h_dom |>.right

/-- Square Root Function's Limit at `x₀ ≤ 0` (Expression) -/
lemma FuncLimitExpr.Sqrt_diverg
    (h_dom : x₀ ≤ 0)
  : lim sqrt x₀ = diverg
:= sorry

/-- Square Root Function's Left Limit at `x₀ > 0` (Expression) -/
lemma LeftLimitExpr.Sqrt
    (h_dom : x₀ > 0)
  : lim₋ sqrt x₀ =. the (√x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Sqrt h_dom

/-- Square Root Function's Left Limit at `x₀ ≤ 0` (Expression) -/
lemma LeftLimitExpr.Sqrt_diverg
    (h_dom : x₀ ≤ 0)
  : lim₋ sqrt x₀ = diverg
:= sorry

/-- Square Root Function's Right Limit at `x₀ ≥ 0` (Expression) -/
lemma RightLimitExpr.Sqrt
    (h_dom : x₀ ≥ 0)
  : lim₊ sqrt x₀ =. the (√x₀)
:= sorry

/-- Square Root Function's Right Limit at `x₀ < 0` (Expression) -/
lemma RightLimitExpr.Sqrt_diverg
    (h_dom : x₀ < 0)
  : lim₊ sqrt x₀ = diverg
:= sorry

/-- Square Root Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Sqrt
  : lim pos_infty sqrt = pos_infty
:= sorry

/-- Square Root Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Sqrt
  : lim neg_infty sqrt = diverg  -- actually not in domine
:= sorry

/-- Square Root Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Sqrt
  : lim infty sqrt = diverg  -- actually not in domine
:= sorry

/-- Power Function's Limit (Expression) -/
lemma FuncLimitExpr.Power
    (h_dom : x₀ > 0)
  : lim (pow a) x₀ =. the (x₀ ^ a)
:= sorry

/-- Power Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Power
    (h_dom : x₀ > 0)
  : lim₋ (pow a) x₀ =. the (x₀ ^ a)
:= sorry

/-- Power Function's Right Limit (Expression) -/
lemma RightLimitExpr.Power
    (h_dom : x₀ > 0 ∨ (a ≥ 0 ∧ x₀ = 0))
  : lim₊ (pow a) x₀ =. the (x₀ ^ a)
:= sorry

/-- Power Function's Right Limit at `0` when `a < 0` (Expression) -/
lemma RightLimitExpr.Power_posInfty
    (h_a : a < 0)
  : lim₊ (pow a) 0 = pos_infty
:= sorry

/-- Power Function's Limit outside its Domain (Expression) -/
lemma FuncLimitExpr.Power_diverg
    (h_dom : x₀ ≤ 0)
  : lim (pow a) x₀ = diverg
:= sorry

/-- Power Function's Left Limit outside its Domain (Expression) -/
lemma LeftLimitExpr.Power_diverg
    (h_dom : x₀ ≤ 0)
  : lim₋ (pow a) x₀ = diverg
:= sorry

/-- Power Function's Right Limit outside its Domain (Expression) -/
lemma RightLimitExpr.Power_diverg
    (h_dom : x₀ < 0)
  : lim₊ (pow a) x₀ = diverg
:= sorry

/-- Power Function's Limit at Positive Infinity when `a > 0` (Expression) -/
lemma PosInftyLimitExpr.Power_pos
    (h_a : a > 0)
  : lim pos_infty (pow a) = pos_infty
:= sorry

/-- Power Function's Limit at Positive Infinity when `a = 0` (Expression) -/
lemma PosInftyLimitExpr.Power_zero
    (h_a : a = 0)
  : lim pos_infty (pow a) =. the 1
:= sorry

/-- Power Function's Limit at Positive Infinity when `a < 0` (Expression) -/
lemma PosInftyLimitExpr.Power_neg
    (h_a : a < 0)
  : lim pos_infty (pow a) =. the 0
:= sorry

/-- Power Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Power
  : lim neg_infty (pow a) = diverg
:= sorry

/-- Power Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Power
  : lim infty (pow a) = diverg
:= sorry

/-- Power Function's Limit for `n : ℤ` (Expression) -/
lemma FuncLimitExpr.Power_ℤ
    (h_dom : n ≥ 0 ∨ x₀ ≠ 0)
  : lim (npow n) x₀ =. the (x₀ ^ n)
:= sorry

/-- Power Function's Left Limit for `n : ℤ` (Expression) -/
lemma LeftLimitExpr.Power_ℤ
    (h_dom : n ≥ 0 ∨ x₀ ≠ 0)
  : lim₋ (npow n) x₀ =. the (x₀ ^ n)
:= sorry

/-- Power Function's Right Limit for `n : ℤ` (Expression) -/
lemma RightLimitExpr.Power_ℤ
    (h_dom : n ≥ 0 ∨ x₀ ≠ 0)
  : lim₊ (npow n) x₀ =. the (x₀ ^ n)
:= sorry

/-- Integral Power Function's Right Limit at `0` when `n < 0` (Expression) -/
lemma RightLimitExpr.Power_ℤ_posInfty
    (h_n : n < 0)
  : lim₊ (npow n) 0 = pos_infty
:= sorry

/-- Even Integral Power Function's Left Limit at `0` when `n < 0` (Expression) -/
lemma LeftLimitExpr.Power_ℤ_posInfty
    (h_n : n < 0) (h_even : Even n)
  : lim₋ (npow n) 0 = pos_infty
:= sorry

/-- Odd Integral Power Function's Left Limit at `0` when `n < 0` (Expression) -/
lemma LeftLimitExpr.Power_ℤ_negInfty
    (h_n : n < 0) (h_odd : Odd n)
  : lim₋ (npow n) 0 = neg_infty
:= sorry

/-- Even Integral Power Function's Limit at `0` when `n < 0` (Expression) -/
lemma FuncLimitExpr.Power_ℤ_posInfty
    (h_n : n < 0) (h_even : Even n)
  : lim (npow n) 0 = pos_infty
:= sorry

/-- Odd Integral Power Function's Limit at `0` when `n < 0` (Expression) -/
lemma FuncLimitExpr.Power_ℤ_unsignedInfty
    (h_n : n < 0) (h_odd : Odd n)
  : lim (npow n) 0 = infty
:= sorry

/-- Integral Power Function's Limit at Positive Infinity when `n > 0` (Expression) -/
lemma PosInftyLimitExpr.Power_ℤ_pos
    (h_n : n > 0)
  : lim pos_infty (npow n) = pos_infty
:= sorry

/-- Integral Power Function's Limit at Positive Infinity when `n = 0` (Expression) -/
lemma PosInftyLimitExpr.Power_ℤ_zero
    (h_n : n = 0)
  : lim pos_infty (npow n) =. the 1
:= sorry

/-- Integral Power Function's Limit at Positive Infinity when `n < 0` (Expression) -/
lemma PosInftyLimitExpr.Power_ℤ_neg
    (h_n : n < 0)
  : lim pos_infty (npow n) =. the 0
:= sorry

/-- Even Integral Power Function's Limit at Negative Infinity when `n > 0` (Expression) -/
lemma NegInftyLimitExpr.Power_ℤ_pos_even
    (h_n : n > 0) (h_even : Even n)
  : lim neg_infty (npow n) = pos_infty
:= sorry

/-- Odd Integral Power Function's Limit at Negative Infinity when `n > 0` (Expression) -/
lemma NegInftyLimitExpr.Power_ℤ_pos_odd
    (h_n : n > 0) (h_odd : Odd n)
  : lim neg_infty (npow n) = neg_infty
:= sorry

/-- Integral Power Function's Limit at Negative Infinity when `n = 0` (Expression) -/
lemma NegInftyLimitExpr.Power_ℤ_zero
    (h_n : n = 0)
  : lim neg_infty (npow n) =. the 1
:= sorry

/-- Integral Power Function's Limit at Negative Infinity when `n < 0` (Expression) -/
lemma NegInftyLimitExpr.Power_ℤ_neg
    (h_n : n < 0)
  : lim neg_infty (npow n) =. the 0
:= sorry

/-- Even Integral Power Function's Limit at Infinity when `n > 0` (Expression) -/
lemma InftyLimitExpr.Power_ℤ_pos_even
    (h_n : n > 0) (h_even : Even n)
  : lim infty (npow n) = pos_infty
:= sorry

/-- Odd Integral Power Function's Limit at Infinity when `n > 0` (Expression) -/
lemma InftyLimitExpr.Power_ℤ_pos_odd
    (h_n : n > 0) (h_odd : Odd n)
  : lim infty (npow n) = infty
:= sorry

/-- Integral Power Function's Limit at Infinity when `n = 0` (Expression) -/
lemma InftyLimitExpr.Power_ℤ_zero
    (h_n : n = 0)
  : lim infty (npow n) =. the 1
:= sorry

/-- Integral Power Function's Limit at Infinity when `n < 0` (Expression) -/
lemma InftyLimitExpr.Power_ℤ_neg
    (h_n : n < 0)
  : lim infty (npow n) =. the 0
:= sorry

/-- Natural Exponential Function's Limit (Expression) -/
lemma FuncLimitExpr.Exp
  : lim exp x₀ =. the (exp x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Exp x₀ (mem_univ x₀) |>.right

/-- Natural Exponential Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Exp
  : lim₋ exp x₀ =. the (exp x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Exp

/-- Natural Exponential Function's Right Limit (Expression) -/
lemma RightLimitExpr.Exp
  : lim₊ exp x₀ =. the (exp x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Exp

/-- Natural Exponential Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Exp
  : lim pos_infty exp = pos_infty
:= sorry

/-- Natural Exponential Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Exp
  : lim neg_infty exp =. the 0
:= sorry

/-- Natural Exponential Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Exp
  : lim infty exp =. diverg
:= sorry

/-- Exponential Function's Limit (Expression) -/
lemma FuncLimitExpr.Expow
    (h_dom : a > 0)
  : lim (a ^ ·) x₀ =. the (a ^ x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Expow h_dom x₀ (mem_univ x₀) |>.right

/-- Exponential Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Expow
    (h_dom : a > 0)
  : lim₋ (a ^ ·) x₀ =. the (a ^ x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Expow h_dom

/-- Exponential Function's Right Limit (Expression) -/
lemma RightLimitExpr.Expow
    (h_dom : a > 0)
  : lim₊ (a ^ ·) x₀ =. the (a ^ x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Expow h_dom

/-- Exponential Function's Limit at Positive Infinity when `a > 1` (Expression) -/
lemma PosInftyLimitExpr.Expow_gt_one
    (h_a : a > 1)
  : lim pos_infty (a ^ ·) = pos_infty
:= sorry

/-- Exponential Function's Limit at Negative Infinity when `a > 1` (Expression) -/
lemma NegInftyLimitExpr.Expow_gt_one
    (h_a : a > 1)
  : lim neg_infty (a ^ ·) =. the 0
:= sorry

/-- Exponential Function's Limit at Positive Infinity when `0 < a < 1` (Expression) -/
lemma PosInftyLimitExpr.Expow_lt_one
    (h_a : 0 < a ∧ a < 1)
  : lim pos_infty (a ^ ·) =. the 0
:= sorry

/-- Exponential Function's Limit at Negative Infinity when `0 < a < 1` (Expression) -/
lemma NegInftyLimitExpr.Expow_lt_one
    (h_a : 0 < a ∧ a < 1)
  : lim neg_infty (a ^ ·) = pos_infty
:= sorry

/-- Natural Logarithm Function's Limit at `x₀ > 0` (Expression) -/
lemma FuncLimitExpr.Ln
    (h_dom : x₀ > 0)
  : lim ln x₀ =. the (ln x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Ln x₀ h_dom |>.right

/-- Natural Logarithm Function's Left Limit at `x₀ > 0` (Expression) -/
lemma LeftLimitExpr.Ln
    (h_dom : x₀ > 0)
  : lim₋ ln x₀ =. the (ln x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Ln h_dom

/-- Natural Logarithm Function's Right Limit at `x₀ > 0` (Expression) -/
lemma RightLimitExpr.Ln
    (h_dom : x₀ > 0)
  : lim₊ ln x₀ =. the (ln x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Ln h_dom

/-- Natural Logarithm Function's Right Limit at `0` (Expression) -/
lemma RightLimitExpr.Ln_zero
  : lim₊ ln 0 = neg_infty
:= sorry

/-- Natural Logarithm Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Ln
  : lim pos_infty ln = pos_infty
:= sorry

/-- Logarithm Function's Limit (Expression) -/
lemma FuncLimitExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim (log a) x₀ =. the (log a x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Log h_dom.right x₀ h_dom.1 |>.right

/-- Logarithm Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim₋ (log a) x₀ =. the (log a x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Log h_dom

/-- Logarithm Function's Right Limit (Expression) -/
lemma RightLimitExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim₊ (log a) x₀ =. the (log a x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Log h_dom

/-- Logarithm Function's Right Limit at `0` when `a > 1` (Expression) -/
lemma RightLimitExpr.Log_zero_gt_one
    (h_a : a > 1)
  : lim₊ (log a) 0 = neg_infty
:= sorry

/-- Logarithm Function's Right Limit at `0` when `0 < a < 1` (Expression) -/
lemma RightLimitExpr.Log_zero_lt_one
    (h_a : 0 < a ∧ a < 1)
  : lim₊ (log a) 0 = pos_infty
:= sorry

/-- Logarithm Function's Limit at Positive Infinity when `a > 1` (Expression) -/
lemma PosInftyLimitExpr.Log_gt_one
    (h_a : a > 1)
  : lim pos_infty (log a) = pos_infty
:= sorry

/-- Logarithm Function's Limit at Positive Infinity when `0 < a < 1` (Expression) -/
lemma PosInftyLimitExpr.Log_lt_one
    (h_a : 0 < a ∧ a < 1)
  : lim pos_infty (log a) = neg_infty
:= sorry

/-- Sine Function's Limit (Expression) -/
lemma FuncLimitExpr.Sin
  : lim sin x₀ =. the (sin x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Sin x₀ (mem_univ x₀) |>.right

/-- Sine Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Sin
  : lim₋ sin x₀ =. the (sin x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Sin

/-- Sine Function's Right Limit (Expression) -/
lemma RightLimitExpr.Sin
  : lim₊ sin x₀ =. the (sin x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Sin

/-- Sine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Sin
  : lim pos_infty sin = diverg
:= sorry

/-- Sine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Sin
  : lim neg_infty sin = diverg
:= sorry

/-- Sine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Sin
  : lim infty sin = diverg
:= sorry

/-- Cosine Function's Limit (Expression) -/
lemma FuncLimitExpr.Cos
  : lim cos x₀ =. the (cos x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Cos x₀ (mem_univ x₀) |>.right

/-- Cosine Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Cos
  : lim₋ cos x₀ =. the (cos x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Cos

/-- Cosine Function's Right Limit (Expression) -/
lemma RightLimitExpr.Cos
  : lim₊ cos x₀ =. the (cos x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Cos

/-- Cosine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Cos
  : lim pos_infty cos = diverg
:= sorry

/-- Cosine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Cos
  : lim neg_infty cos = diverg
:= sorry

/-- Cosine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Cos
  : lim infty cos = diverg
:= sorry

/-- Tangent Function's Limit at `cos x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : lim tan x₀ =. the (tan x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Tan x₀ h_dom |>.right

/-- Tangent Function's Limit at `cos x₀ = 0` (Expression) -/
lemma FuncLimitExpr.Tan_infty
    (h_pole : cos x₀ = 0)
  : lim tan x₀ = infty
:= sorry

/-- Tangent Function's Left Limit at `cos x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : lim₋ tan x₀ =. the (tan x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Tan h_dom

/-- Tangent Function's Left Limit at `cos x₀ = 0` (Expression) -/
lemma LeftLimitExpr.Tan_infty
    (h_pole : cos x₀ = 0)
  : lim₋ tan x₀ = pos_infty
:= sorry

/-- Tangent Function's Right Limit at `cos x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : lim₊ tan x₀ =. the (tan x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Tan h_dom

/-- Tangent Function's Right Limit at `cos x₀ = 0` (Expression) -/
lemma RightLimitExpr.Tan_infty
    (h_pole : cos x₀ = 0)
  : lim₊ tan x₀ = neg_infty
:= sorry

/-- Tangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Tan
  : lim pos_infty tan = diverg
:= sorry

/-- Tangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Tan
  : lim neg_infty tan = diverg
:= sorry

/-- Tangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Tan
  : lim infty tan = diverg
:= sorry

/-- Cotangent Function's Limit at `sin x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : lim cot x₀ =. the (cot x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Cot x₀ h_dom |>.right

/-- Cotangent Function's Limit at `sin x₀ = 0` (Expression) -/
lemma FuncLimitExpr.Cot_infty
    (h_pole : sin x₀ = 0)
  : lim cot x₀ = infty
:= sorry

/-- Cotangent Function's Left Limit at `sin x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : lim₋ cot x₀ =. the (cot x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Cot h_dom

/-- Cotangent Function's Left Limit at `sin x₀ = 0` (Expression) -/
lemma LeftLimitExpr.Cot_infty
    (h_pole : sin x₀ = 0)
  : lim₋ cot x₀ = neg_infty
:= sorry

/-- Cotangent Function's Right Limit at `sin x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : lim₊ cot x₀ =. the (cot x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Cot h_dom

/-- Cotangent Function's Right Limit at `sin x₀ = 0` (Expression) -/
lemma RightLimitExpr.Cot_infty
    (h_pole : sin x₀ = 0)
  : lim₊ cot x₀ = pos_infty
:= sorry

/-- Cotangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Cot
  : lim pos_infty cot = diverg
:= sorry

/-- Cotangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Cot
  : lim neg_infty cot = diverg
:= sorry

/-- Cotangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Cot
  : lim infty cot = diverg
:= sorry

/-- Secant Function's Limit at `cos x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : lim sec x₀ =. the (sec x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Sec x₀ h_dom |>.right

/-- Secant Function's Limit at `cos x₀ = 0` (Expression) -/
lemma FuncLimitExpr.Sec_infty
    (h_pole : cos x₀ = 0)
  : lim sec x₀ = infty
:= sorry

/-- Secant Function's Left Limit at `cos x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : lim₋ sec x₀ =. the (sec x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Sec h_dom

/-- Secant Function's Left Limit at `cos x₀ = 0 ∧ sin x₀ > 0` (Expression) -/
lemma LeftLimitExpr.Sec_pos_infty
    (h_pole : cos x₀ = 0) (h_sign : sin x₀ > 0)
  : lim₋ sec x₀ = pos_infty
:= sorry

/-- Secant Function's Left Limit at `cos x₀ = 0 ∧ sin x₀ < 0` (Expression) -/
lemma LeftLimitExpr.Sec_neg_infty
    (h_pole : cos x₀ = 0) (h_sign : sin x₀ < 0)
  : lim₋ sec x₀ = neg_infty
:= sorry

/-- Secant Function's Right Limit at `cos x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : lim₊ sec x₀ =. the (sec x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Sec h_dom

/-- Secant Function's Right Limit at `cos x₀ = 0 ∧ sin x₀ < 0` (Expression) -/
lemma RightLimitExpr.Sec_pos_infty
    (h_pole : cos x₀ = 0) (h_sign : sin x₀ < 0)
  : lim₊ sec x₀ = pos_infty
:= sorry

/-- Secant Function's Right Limit at `cos x₀ = 0 ∧ sin x₀ > 0` (Expression) -/
lemma RightLimitExpr.Sec_neg_infty
    (h_pole : cos x₀ = 0) (h_sign : sin x₀ > 0)
  : lim₊ sec x₀ = neg_infty
:= sorry

/-- Secant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Sec
  : lim pos_infty sec = diverg
:= sorry

/-- Secant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Sec
  : lim neg_infty sec = diverg
:= sorry

/-- Secant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Sec
  : lim infty sec = diverg
:= sorry

/-- Cosecant Function's Limit at `sin x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : lim csc x₀ =. the (csc x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Csc x₀ h_dom |>.right

/-- Cosecant Function's Limit at `sin x₀ = 0` (Expression) -/
lemma FuncLimitExpr.Csc_infty
    (h_pole : sin x₀ = 0)
  : lim csc x₀ = infty
:= sorry

/-- Cosecant Function's Left Limit at `sin x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : lim₋ csc x₀ =. the (csc x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Csc h_dom

/-- Cosecant Function's Left Limit at `sin x₀ = 0 ∧ cos x₀ < 0` (Expression) -/
lemma LeftLimitExpr.Csc_pos_infty
    (h_pole : sin x₀ = 0) (h_sign : cos x₀ < 0)
  : lim₋ csc x₀ = pos_infty
:= sorry

/-- Cosecant Function's Left Limit at `sin x₀ = 0 ∧ cos x₀ > 0` (Expression) -/
lemma LeftLimitExpr.Csc_neg_infty
    (h_pole : sin x₀ = 0) (h_sign : cos x₀ > 0)
  : lim₋ csc x₀ = neg_infty
:= sorry

/-- Cosecant Function's Right Limit at `sin x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : lim₊ csc x₀ =. the (csc x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Csc h_dom

/-- Cosecant Function's Right Limit at `sin x₀ = 0 ∧ cos x₀ > 0` (Expression) -/
lemma RightLimitExpr.Csc_pos_infty
    (h_pole : sin x₀ = 0) (h_sign : cos x₀ > 0)
  : lim₊ csc x₀ = pos_infty
:= sorry

/-- Cosecant Function's Right Limit at `sin x₀ = 0 ∧ cos x₀ < 0` (Expression) -/
lemma RightLimitExpr.Csc_neg_infty
    (h_pole : sin x₀ = 0) (h_sign : cos x₀ < 0)
  : lim₊ csc x₀ = neg_infty
:= sorry

/-- Cosecant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Csc
  : lim pos_infty csc = diverg
:= sorry

/-- Cosecant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Csc
  : lim neg_infty csc = diverg
:= sorry

/-- Cosecant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Csc
  : lim infty csc = diverg
:= sorry

/-- Hyp-Sine Function's Limit (Expression) -/
lemma FuncLimitExpr.Sinh
  : lim sinh x₀ =. the (sinh x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Sinh x₀ (mem_univ x₀) |>.right

/-- Hyp-Sine Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Sinh
  : lim₋ sinh x₀ =. the (sinh x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Sinh

/-- Hyp-Sine Function's Right Limit (Expression) -/
lemma RightLimitExpr.Sinh
  : lim₊ sinh x₀ =. the (sinh x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Sinh

/-- Hyp-Sine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Sinh
  : lim pos_infty sinh = pos_infty
:= sorry

/-- Hyp-Sine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Sinh
  : lim neg_infty sinh = neg_infty
:= sorry

/-- Hyp-Sine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Sinh
  : lim infty sinh = infty
:= sorry

/-- Hyp-Cosine Function's Limit (Expression) -/
lemma FuncLimitExpr.Cosh
  : lim cosh x₀ =. the (cosh x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Cosh x₀ (mem_univ x₀) |>.right

/-- Hyp-Cosine Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Cosh
  : lim₋ cosh x₀ =. the (cosh x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Cosh

/-- Hyp-Cosine Function's Right Limit (Expression) -/
lemma RightLimitExpr.Cosh
  : lim₊ cosh x₀ =. the (cosh x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Cosh

/-- Hyp-Cosine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Cosh
  : lim pos_infty cosh = pos_infty
:= sorry

/-- Hyp-Cosine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Cosh
  : lim neg_infty cosh = pos_infty
:= sorry

/-- Hyp-Cosine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Cosh
  : lim infty cosh = pos_infty
:= sorry

/-- Hyp-Tangent Function's Limit (Expression) -/
lemma FuncLimitExpr.Tanh
  : lim tanh x₀ =. the (tanh x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Tanh x₀ (mem_univ x₀) |>.right

/-- Hyp-Tangent Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Tanh
  : lim₋ tanh x₀ =. the (tanh x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Tanh

/-- Hyp-Tangent Function's Right Limit (Expression) -/
lemma RightLimitExpr.Tanh
  : lim₊ tanh x₀ =. the (tanh x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Tanh

/-- Hyp-Tangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Tanh
  : lim pos_infty tanh =. the 1
:= sorry

/-- Hyp-Tangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Tanh
  : lim neg_infty tanh =. the (-1)
:= sorry

/-- Hyp-Tangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Tanh
  : lim infty tanh = diverg
:= sorry

/-- Hyp-Cotangent Function's Limit at `x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Coth
    (h_dom : x₀ ≠ 0)
  : lim coth x₀ =. the (coth x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Coth x₀ h_dom |>.right

/-- Hyp-Cotangent Function's Limit at `0` (Expression) -/
lemma FuncLimitExpr.Coth_zero
  : lim coth 0 = infty
:= sorry

/-- Hyp-Cotangent Function's Left Limit at `0` (Expression) -/
lemma LeftLimitExpr.Coth_zero
  : lim₋ coth 0 = neg_infty
:= sorry

/-- Hyp-Cotangent Function's Left Limit at `x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Coth
    (h_dom : x₀ ≠ 0)
  : lim₋ coth x₀ =. the (coth x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Coth h_dom

/-- Hyp-Cotangent Function's Right Limit at `0` (Expression) -/
lemma RightLimitExpr.Coth_zero
  : lim₊ coth 0 = pos_infty
:= sorry

/-- Hyp-Cotangent Function's Right Limit at `x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Coth
    (h_dom : x₀ ≠ 0)
  : lim₊ coth x₀ =. the (coth x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Coth h_dom

/-- Hyp-Cotangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Coth
  : lim pos_infty coth =. the 1
:= sorry

/-- Hyp-Cotangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Coth
  : lim neg_infty coth =. the (-1)
:= sorry

/-- Hyp-Cotangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Coth
  : lim infty coth = diverg
:= sorry

/-- Hyp-Secant Function's Limit (Expression) -/
lemma FuncLimitExpr.Sech
  : lim sech x₀ =. the (sech x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Sech x₀ (mem_univ x₀) |>.right

/-- Hyp-Secant Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Sech
  : lim₋ sech x₀ =. the (sech x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Sech

/-- Hyp-Secant Function's Right Limit (Expression) -/
lemma RightLimitExpr.Sech
  : lim₊ sech x₀ =. the (sech x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Sech

/-- Hyp-Secant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Sech
  : lim pos_infty sech =. the 0
:= sorry

/-- Hyp-Secant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Sech
  : lim neg_infty sech =. the 0
:= sorry

/-- Hyp-Secant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Sech
  : lim infty sech =. the 0
:= sorry

/-- Hyp-Cosecant Function's Limit at `x₀ ≠ 0` (Expression) -/
lemma FuncLimitExpr.Csch
    (h_dom : x₀ ≠ 0)
  : lim csch x₀ =. the (csch x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Csch x₀ h_dom |>.right

/-- Hyp-Cosecant Function's Limit at `0` (Expression) -/
lemma FuncLimitExpr.Csch_zero
  : lim csch 0 = infty
:= sorry

/-- Hyp-Cosecant Function's Left Limit at `x₀ ≠ 0` (Expression) -/
lemma LeftLimitExpr.Csch
    (h_dom : x₀ ≠ 0)
  : lim₋ csch x₀ =. the (csch x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Csch h_dom

/-- Hyp-Cosecant Function's Left Limit at `0` (Expression) -/
lemma LeftLimitExpr.Csch_zero
  : lim₋ csch 0 = neg_infty
:= sorry

/-- Hyp-Cosecant Function's Right Limit at `x₀ ≠ 0` (Expression) -/
lemma RightLimitExpr.Csch
    (h_dom : x₀ ≠ 0)
  : lim₊ csch x₀ =. the (csch x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Csch h_dom

/-- Hyp-Cosecant Function's Right Limit at `0` (Expression) -/
lemma RightLimitExpr.Csch_zero
  : lim₊ csch 0 = pos_infty
:= sorry

/-- Hyp-Cosecant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Csch
  : lim pos_infty csch =. the 0
:= sorry

/-- Hyp-Cosecant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Csch
  : lim neg_infty csch =. the 0
:= sorry

/-- Hyp-Cosecant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Csch
  : lim infty csch =. the 0
:= sorry

/-- Arc-Sine Function's Limit at `x₀ > -1 ∧ x₀ < 1` (Expression) -/
lemma FuncLimitExpr.Arcsin
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : lim arcsin x₀ =. the (arcsin x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arcsin x₀ h_dom |>.right

/-- Arc-Sine Function's Left Limit at `x₀ > -1 ∧ x₀ ≤ 1` (Expression) -/
lemma LeftLimitExpr.Arcsin
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
  : lim₋ arcsin x₀ =. the (arcsin x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply LeftLimit.toLeftLimitExpr
    exact LeftContinuity.Arcsin_1.right
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact h_dom.left
      · exact lt_of_le_of_ne h_dom.right h_1
    sorry

/-- Arc-Sine Function's Right Limit at `x₀ ≥ -1 ∧ x₀ < 1` (Expression) -/
lemma RightLimitExpr.Arcsin
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
  : lim₊ arcsin x₀ =. the (arcsin x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply RightLimit.toRightLimitExpr
    exact RightContinuity.Arcsin_neg1.right
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact lt_of_le_of_ne h_dom.left (Ne.symm h_neg1)
      · exact h_dom.right
    sorry

/-- Arc-Sine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arcsin
  : lim pos_infty arcsin = diverg
:= sorry

/-- Arc-Sine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arcsin
  : lim neg_infty arcsin = diverg
:= sorry

/-- Arc-Sine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arcsin
  : lim infty arcsin = diverg
:= sorry

/-- Arc-Cosine Function's Limit at `x₀ > -1 ∧ x₀ < 1` (Expression) -/
lemma FuncLimitExpr.Arccos
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : lim arccos x₀ =. the (arccos x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arccos x₀ h_dom |>.right

/-- Arc-Cosine Function's Left Limit at `x₀ > -1 ∧ x₀ ≤ 1` (Expression) -/
lemma LeftLimitExpr.Arccos
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
  : lim₋ arccos x₀ =. the (arccos x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply LeftLimit.toLeftLimitExpr
    exact LeftContinuity.Arccos_1.right
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact h_dom.left
      · exact lt_of_le_of_ne h_dom.right h_1
    sorry

/-- Arc-Cosine Function's Right Limit at `x₀ ≥ -1 ∧ x₀ < 1` (Expression) -/
lemma RightLimitExpr.Arccos
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
  : lim₊ arccos x₀ =. the (arccos x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply RightLimit.toRightLimitExpr
    exact RightContinuity.Arccos_neg1.right
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact lt_of_le_of_ne h_dom.left (Ne.symm h_neg1)
      · exact h_dom.right
    sorry

/-- Arc-Cosine Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arccos
  : lim pos_infty arccos = diverg
:= sorry

/-- Arc-Cosine Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arccos
  : lim neg_infty arccos = diverg
:= sorry

/-- Arc-Cosine Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arccos
  : lim infty arccos = diverg
:= sorry

/-- Arc-Tangent Function's Limit (Expression) -/
lemma FuncLimitExpr.Arctan
  : lim arctan x₀ =. the (arctan x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arctan x₀ (mem_univ x₀) |>.right

/-- Arc-Tangent Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Arctan
  : lim₋ arctan x₀ =. the (arctan x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Arctan

/-- Arc-Tangent Function's Right Limit (Expression) -/
lemma RightLimitExpr.Arctan
  : lim₊ arctan x₀ =. the (arctan x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Arctan

/-- Arc-Tangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arctan
  : lim pos_infty arctan =. the (π / 2)
:= sorry

/-- Arc-Tangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arctan
  : lim neg_infty arctan =. the (-π / 2)
:= sorry

/-- Arc-Tangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arctan
  : lim infty arctan = diverg
:= sorry

/-- Arc-Cotangent Function's Limit (Expression) -/
lemma FuncLimitExpr.Arccot
  : lim arccot x₀ =. the (arccot x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arccot x₀ (mem_univ x₀) |>.right

/-- Arc-Cotangent Function's Left Limit (Expression) -/
lemma LeftLimitExpr.Arccot
  : lim₋ arccot x₀ =. the (arccot x₀)
:= FuncLimitExpr.toLeft <| FuncLimitExpr.Arccot

/-- Arc-Cotangent Function's Right Limit (Expression) -/
lemma RightLimitExpr.Arccot
  : lim₊ arccot x₀ =. the (arccot x₀)
:= FuncLimitExpr.toRight <| FuncLimitExpr.Arccot

/-- Arc-Cotangent Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arccot
  : lim pos_infty arccot =. the 0
:= sorry

/-- Arc-Cotangent Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arccot
  : lim neg_infty arccot =. the π
:= sorry

/-- Arc-Cotangent Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arccot
  : lim infty arccot = diverg
:= sorry

/-- Arc-Secant Function's Limit at `x₀ < -1 ∨ x₀ > 1` (Expression) -/
lemma FuncLimitExpr.Arcsec
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : lim arcsec x₀ =. the (arcsec x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arcsec x₀ h_dom |>.right

/-- Arc-Secant Function's Left Limit at `x₀ ≤ -1 ∨ x₀ > 1` (Expression) -/
lemma LeftLimitExpr.Arcsec
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
  : lim₋ arcsec x₀ =. the (arcsec x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply LeftLimit.toLeftLimitExpr
    exact LeftContinuity.Arcsec_neg1.right
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact Std.lt_of_le_of_ne h_le h_neg1
      · right
        exact RCLike.ofReal_lt_ofReal.mp h_gt
    sorry

/-- Arc-Secant Function's Right Limit at `x₀ < -1 ∨ x₀ ≥ 1` (Expression) -/
lemma RightLimitExpr.Arcsec
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
  : lim₊ arcsec x₀ =. the (arcsec x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply RightLimit.toRightLimitExpr
    exact RightContinuity.Arcsec_1.right
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact RCLike.ofReal_lt_ofReal.mp h_le
      · right
        exact Std.lt_of_le_of_ne h_gt (fun eq ↦ h_1 (Eq.symm eq))
    sorry

/-- Arc-Secant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arcsec
  : lim pos_infty arcsec =. the (π / 2)
:= sorry

/-- Arc-Secant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arcsec
  : lim neg_infty arcsec =. the (π / 2)
:= sorry

/-- Arc-Secant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arcsec
  : lim infty arcsec =. the (π / 2)
:= sorry

/-- Arc-Cosecant Function's Limit at `x₀ < -1 ∨ x₀ > 1` (Expression) -/
lemma FuncLimitExpr.Arccsc
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : lim arccsc x₀ =. the (arccsc x₀)
:= by
  apply FuncLimit.toFuncLimitExpr
  exact Continuity.Arccsc x₀ h_dom |>.right

/-- Arc-Cosecant Function's Left Limit `x₀ ≤ -1 ∨ x₀ > 1` (Expression) -/
lemma LeftLimitExpr.Arccsc
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
  : lim₋ arccsc x₀ =. the (arccsc x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply LeftLimit.toLeftLimitExpr
    exact LeftContinuity.Arccsc_neg1.right
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact Std.lt_of_le_of_ne h_le h_neg1
      · right
        exact RCLike.ofReal_lt_ofReal.mp h_gt
    sorry

/-- Arc-Cosecant Function's Right Limit at `x₀ < -1 ∨ x₀ ≥ 1` (Expression) -/
lemma RightLimitExpr.Arccsc
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
  : lim₊ arccsc x₀ =. the (arccsc x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply RightLimit.toRightLimitExpr
    exact RightContinuity.Arccsc_1.right
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact RCLike.ofReal_lt_ofReal.mp h_le
      · right
        exact Std.lt_of_le_of_ne h_gt (fun eq ↦ h_1 (Eq.symm eq))
    sorry

/-- Arc-Cosecant Function's Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Arccsc
  : lim pos_infty arccsc =. the 0
:= sorry

/-- Arc-Cosecant Function's Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Arccsc
  : lim neg_infty arccsc =. the 0
:= sorry

/-- Arc-Cosecant Function's Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Arccsc
  : lim infty arccsc =. the 0
:= sorry

end

/-! # Expression Properties of Function's Continuity -/

/-- Function Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be continuous at `u₀` -/
theorem FuncLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim g x₀ =. the u₀)
    (h_f_cont : lim f u₀ =. the (f u₀))
  : lim (f ∘ g) x₀ =. the (f u₀)
:= by
  have hg := FuncLimit.fromFuncLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_u₀
  have hf := FuncLimit.fromFuncLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_f_cont
  have h_f_cont_prop : isContinuousAt ⟨f, Iii⟩ u₀ := ⟨mem_univ _, hf⟩
  have h_comp := FuncLimit.CompSV hg h_f_cont_prop
  exact FuncLimit.toFuncLimitExpr h_comp

/-- Left Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be left continuous at `u₀` -/
theorem LeftLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₋ g x₀ =. the u₀)
    (h_f_cont : lim f u₀ =. the (f u₀))
  : lim₋ (f ∘ g) x₀ =. the (f u₀)
:= by
  have hg := LeftLimit.fromLeftLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_u₀
  have hf := FuncLimit.fromFuncLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_f_cont
  have h_comp : LeftLimit ⟨f ∘ g, Iii⟩ x₀ (f u₀) := by
    constructor
    · exists 1 with zero_lt_one
      exact subset_univ _
    · intro ε h_ε
      rcases hf.2 ε h_ε with ⟨δ1, hδ1_pos, hδ1⟩
      rcases hg.2 δ1 hδ1_pos with ⟨δ2, hδ2_pos, hδ2⟩
      use δ2, hδ2_pos
      intro x h_x
      have hGx_nbho := hδ2 x h_x
      by_cases h_eq : g x = u₀
      · change f (g x) ∈ Nbho (f u₀) ε
        rw [h_eq]
        exact ⟨by linarith [h_ε], by linarith [h_ε]⟩
      · have hGx_nbhd : g x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
        exact hδ1 (g x) hGx_nbhd
  exact LeftLimit.toLeftLimitExpr h_comp

/-- Right Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be right continuous at `u₀` -/
theorem RightLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₊ g x₀ =. the u₀)
    (h_f_cont : lim f u₀ =. the (f u₀))
  : lim₊ (f ∘ g) x₀ =. the (f u₀)
:= by
  have hg := RightLimit.fromRightLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_u₀
  have hf := FuncLimit.fromFuncLimitExpr ⟨1, zero_lt_one, subset_univ _⟩
    h_f_cont
  have h_comp : RightLimit ⟨f ∘ g, Iii⟩ x₀ (f u₀) := by
    constructor
    · exists 1 with zero_lt_one
      exact subset_univ _
    · intro ε h_ε
      rcases hf.2 ε h_ε with ⟨δ1, hδ1_pos, hδ1⟩
      rcases hg.2 δ1 hδ1_pos with ⟨δ2, hδ2_pos, hδ2⟩
      use δ2, hδ2_pos
      intro x h_x
      have hGx_nbho := hδ2 x h_x
      by_cases h_eq : g x = u₀
      · change f (g x) ∈ Nbho (f u₀) ε
        rw [h_eq]
        exact ⟨by linarith [h_ε], by linarith [h_ε]⟩
      · have hGx_nbhd : g x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
        exact hδ1 (g x) hGx_nbhd
  exact RightLimit.toRightLimitExpr h_comp


page_end
