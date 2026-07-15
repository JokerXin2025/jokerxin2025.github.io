import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Rules
import «Calculus@JokerXin».Function.Continuity.Rules


/-! # Elementary Functions' Continuity -/

/-- Constant Function's Continuity -/
lemma Constant_isContinuous {C : ℝ}
  : isContinuous (Constant C)
:= by
  intro _ _
  unfold isContinuousAt FuncLimit
  constructor
  · exact ⟨1, by norm_num, subset_univ _⟩
  · intro ε _
    use 1
    constructor
    · norm_num
    · intro _ _
      change C ∈ Nbho C ε
      constructor <;> linarith

/-- Constant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Constant {C x₀ : ℝ}
  : lim (const C) x₀ = the C
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Constant_isContinuous x₀ (mem_univ x₀)

/-- Constant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Constant {C x₀ : ℝ}
  : lim₋ (const C) x₀ = the C
:= by
  calc
    lim₋ (const C) x₀  =? lim (const C) x₀
                          := FuncLimitExpr.toLeft
    _                  =  the C
                          := FuncLimitExpr.Constant

/-- Constant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Constant {C x₀ : ℝ}
  : lim₊ (const C) x₀ = the C
:= by
  calc
    lim₊ (const C) x₀  =? lim (const C) x₀
                          := FuncLimitExpr.toRight
    _                  =  the C
                          := FuncLimitExpr.Constant

/-- Identity Function's Continuity -/
lemma Identity_isContinuous
  : isContinuous Identity
:= by
  intro x₀ _
  unfold isContinuousAt FuncLimit
  constructor
  · exact ⟨1, by norm_num, subset_univ _⟩
  · intro ε _
    use ε
    constructor
    · assumption
    · intro x h_x
      change x ∈ Nbho x₀ ε
      exact Nbhd_subset_Nbho h_x

/-- Identity Function's Continuity (Expression) -/
lemma FuncLimitExpr.Identity {x₀ : ℝ}
  : lim id x₀ = the x₀
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Identity_isContinuous x₀ (mem_univ x₀)

/-- Identity Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Identity {x₀ : ℝ}
  : lim₋ id x₀ = the x₀
:= by
  calc
    lim₋ id x₀  =? lim id x₀
                   := FuncLimitExpr.toLeft
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- Identity Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Identity {x₀ : ℝ}
  : lim₊ id x₀ = the x₀
:= by
  calc
    lim₊ id x₀  =? lim id x₀
                   := FuncLimitExpr.toRight
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- Absolute Value Function's Continuity -/
lemma Abs_isContinuous
  : isContinuous Abs
:= sorry

/-- Absolute Value Function's Continuity (Expression) -/
lemma FuncLimitExpr.Abs {x₀ : ℝ}
  : lim abs x₀ = the |x₀|
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Abs_isContinuous x₀ (mem_univ x₀)

/-- Absolute Value Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Abs {x₀ : ℝ}
  : lim₋ abs x₀ = the |x₀|
:= by
  calc
    lim₋ abs x₀  =? lim abs x₀
                    := FuncLimitExpr.toLeft
    _            =  the |x₀|
                    := FuncLimitExpr.Abs

/-- Absolute Value Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Abs {x₀ : ℝ}
  : lim₊ abs x₀ = the |x₀|
:= by
  calc
    lim₊ abs x₀  =? lim abs x₀
                    := FuncLimitExpr.toRight
    _            =  the |x₀|
                    := FuncLimitExpr.Abs

/-- Square Root Function's Continuity for `x > 0` -/
lemma Sqrt_isContinuous
  : ∀ x > 0, isContinuousAt Sqrt x
:= sorry

/-- Square Root Function's Right Continuity at `0` -/
lemma Sqrt_isRightContinuous_0
  : isRightContinuousAt Sqrt 0
:= sorry

/-- Square Root Function's Continuity (Expression) -/
lemma FuncLimitExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim sqrt x₀ = the (√x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sqrt_isContinuous x₀ h_dom

/-- Square Root Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₋ sqrt x₀ = the (√x₀)
:= by
  calc
    lim₋ sqrt x₀  =? lim sqrt x₀
                     := FuncLimitExpr.toLeft
    _             =  the (√x₀)
                     := FuncLimitExpr.Sqrt h_dom

/-- Square Root Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ ≥ 0)
  : lim₊ sqrt x₀ = the (√x₀)
:= by
  by_cases h_0 : x₀ = 0
  · rw [h_0]
    apply RightLimit_to_RightLimitExpr
    exact Sqrt_isRightContinuous_0
  · have h_pos : x₀ > 0 := lt_of_le_of_ne h_dom (Ne.symm h_0)
    calc
      lim₊ sqrt x₀  =? lim sqrt x₀
                       := FuncLimitExpr.toRight
      _             =  the (√x₀)
                       := FuncLimitExpr.Sqrt h_pos

/-- Power Function's Continuity for `x > 0` -/
lemma Power_isContinuous {a : ℝ}
  : ∀ x > 0, isContinuousAt (Power a) x
:= sorry

/-- Power Function's Right Continuity at `0` -/
lemma Power_isRightContinuous_0 {a : ℝ}
    (h_a : a > 0)
  : isRightContinuousAt (Power a) 0
:= sorry

/-- Power Function's Continuity for `n : ℤ` -/
lemma Power_isContinuous_ℤ {n : ℤ}
  : isContinuous (Power n)
:= sorry

/-- Power Function's Continuity (Expression) -/
lemma FuncLimitExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim (pow a) x₀ = the (x₀ ^ a)
:= sorry

/-- Power Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₋ (pow a) x₀ = the (x₀ ^ a)
:= by
  calc
    lim₋ (pow a) x₀  =? lim (pow a) x₀
                        := FuncLimitExpr.toLeft
    _                =  the (x₀ ^ a)
                        := FuncLimitExpr.Power h_dom

/-- Power Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Power {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∨ (a > 0 ∧ x₀ = 0))
  : lim₊ (pow a) x₀ = the (x₀ ^ a)
:= sorry /-by
  cases h_dom with
  | inl h_pos =>
    calc
      lim₊ (pow a) x₀  =? lim (pow a) x₀
                          := FuncLimitExpr.toRight
      _                =  the (x₀ ^ a)
                          := FuncLimitExpr.Power h_pos
  | inr h_dom' =>
    rw [h_dom'.2]
    apply RightLimit_to_RightLimitExpr (I := Ici 0)
    exact Power_isRightContinuous_0 h_dom'.1-/

/-- Power Function's Continuity for `n : ℤ` (Expression) -/
lemma FuncLimitExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : lim (npow n) x₀ = the (x₀ ^ n)
:= sorry

/-- Power Function's Left Continuity for `n : ℤ` (Expression) -/
lemma LeftLimitExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : lim₋ (npow n) x₀ = the (x₀ ^ n)
:= by
  calc
    lim₋ (npow n) x₀  =? lim (npow n) x₀
                         := FuncLimitExpr.toLeft
    _                 =  the (x₀ ^ n)
                         := FuncLimitExpr.Power_ℤ h_dom

/-- Power Function's Right Continuity for `n : ℤ` (Expression) -/
lemma RightLimitExpr.Power_ℤ {n : ℤ} {x₀ : ℝ}
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : lim₊ (npow n) x₀ = the (x₀ ^ n)
:= by
  calc
    lim₊ (npow n) x₀  =? lim (npow n) x₀
                         := FuncLimitExpr.toRight
    _                 =  the (x₀ ^ n)
                         := FuncLimitExpr.Power_ℤ h_dom

/-- Natural Exponential Function's Continuity -/
lemma Exp_isContinuous
  : isContinuous Exp
:= sorry

/-- Natural Exponential Function's Continuity (Expression) -/
lemma FuncLimitExpr.Exp {x₀ : ℝ}
  : lim exp x₀ = the (exp x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Exp_isContinuous x₀ (mem_univ x₀)

/-- Natural Exponential Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Exp {x₀ : ℝ}
  : lim₋ exp x₀ = the (exp x₀)
:= by
  calc
    lim₋ exp x₀  =? lim exp x₀
                    := FuncLimitExpr.toLeft
    _            =  the (exp x₀)
                    := FuncLimitExpr.Exp

/-- Natural Exponential Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Exp {x₀ : ℝ}
  : lim₊ exp x₀ = the (exp x₀)
:= by
  calc
    lim₊ exp x₀  =? lim exp x₀
                    := FuncLimitExpr.toRight
    _            =  the (exp x₀)
                    := FuncLimitExpr.Exp

/-- Exponential Function's Continuity -/
lemma Expow_isContinuous {a : ℝ}
    (h_a : a > 0)
  : isContinuous (Expow a)
:= sorry

/-- Exponential Function's Continuity (Expression) -/
lemma FuncLimitExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : lim (a ^ ·) x₀ = the (a ^ x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Expow_isContinuous h_dom x₀ (mem_univ x₀)

/-- Exponential Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : lim₋ (a ^ ·) x₀ = the (a ^ x₀)
:= by
  calc
    lim₋ (a ^ ·) x₀  =? lim (a ^ ·) x₀
                          := FuncLimitExpr.toLeft
    _                  =  the (a ^ x₀)
                          := FuncLimitExpr.Expow h_dom

/-- Exponential Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Expow {a x₀ : ℝ}
    (h_dom : a > 0)
  : lim₊ (a ^ ·) x₀ = the (a ^ x₀)
:= by
  calc
    lim₊ (a ^ ·) x₀  =? lim (a ^ ·) x₀
                          := FuncLimitExpr.toRight
    _                  =  the (a ^ x₀)
                          := FuncLimitExpr.Expow h_dom

/-- Natural Logarithm Function's Continuity -/
lemma Ln_isContinuous
  : isContinuous Ln
:= sorry

/-- Natural Logarithm Function's Continuity (Expression) -/
lemma FuncLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim ln x₀ = the (ln x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Ln_isContinuous x₀ h_dom

/-- Natural Logarithm Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₋ ln x₀ = the (ln x₀)
:= by
  calc
    lim₋ ln x₀  =? lim ln x₀
                   := FuncLimitExpr.toLeft
    _           =  the (ln x₀)
                   := FuncLimitExpr.Ln h_dom

/-- Natural Logarithm Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₊ ln x₀ = the (ln x₀)
:= by
  calc
    lim₊ ln x₀  =? lim ln x₀
                   := FuncLimitExpr.toRight
    _           =  the (ln x₀)
                   := FuncLimitExpr.Ln h_dom

/-- Logarithm Function's Continuity -/
lemma Log_isContinuous {a : ℝ}
    (h_a : a > 0 ∧ a ≠ 1)
  : isContinuous (Log a)
:= sorry

/-- Logarithm Function's Continuity (Expression) -/
lemma FuncLimitExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim (log a) x₀ = the (log a x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Log_isContinuous h_dom.2 x₀ h_dom.1

/-- Logarithm Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim₋ (log a) x₀ = the (log a x₀)
:= by
  calc
    lim₋ (log a) x₀  =? lim (log a) x₀
                        := FuncLimitExpr.toLeft
    _                =  the (log a x₀)
                        := FuncLimitExpr.Log h_dom

/-- Logarithm Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Log {a x₀ : ℝ}
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : lim₊ (log a) x₀ = the (log a x₀)
:= by
  calc
    lim₊ (log a) x₀  =? lim (log a) x₀
                        := FuncLimitExpr.toRight
    _                =  the (log a x₀)
                        := FuncLimitExpr.Log h_dom

/-- Sine Function's Continuity -/
lemma Sin_isContinuous
  : isContinuous Sin
:= sorry

/-- Sine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Sin {x₀ : ℝ}
  : lim sin x₀ = the (sin x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sin_isContinuous x₀ (mem_univ x₀)

/-- Sine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Sin {x₀ : ℝ}
  : lim₋ sin x₀ = the (sin x₀)
:= by
  calc
    lim₋ sin x₀  =? lim sin x₀
                    := FuncLimitExpr.toLeft
    _            =  the (sin x₀)
                    := FuncLimitExpr.Sin

/-- Sine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Sin {x₀ : ℝ}
  : lim₊ sin x₀ = the (sin x₀)
:= by
  calc
    lim₊ sin x₀  =? lim sin x₀
                    := FuncLimitExpr.toRight
    _            =  the (sin x₀)
                    := FuncLimitExpr.Sin

/-- Cosine Function's Continuity -/
lemma Cos_isContinuous
  : isContinuous Cos
:= sorry

/-- Cosine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Cos {x₀ : ℝ}
  : lim cos x₀ = the (cos x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cos_isContinuous x₀ (mem_univ x₀)

/-- Cosine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Cos {x₀ : ℝ}
  : lim₋ cos x₀ = the (cos x₀)
:= by
  calc
    lim₋ cos x₀  =? lim cos x₀
                    := FuncLimitExpr.toLeft
    _            =  the (cos x₀)
                    := FuncLimitExpr.Cos

/-- Cosine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Cos {x₀ : ℝ}
  : lim₊ cos x₀ = the (cos x₀)
:= by
  calc
    lim₊ cos x₀  =? lim cos x₀
                    := FuncLimitExpr.toRight
    _            =  the (cos x₀)
                    := FuncLimitExpr.Cos

/-- Tangent Function's Continuity -/
lemma Tan_isContinuous
  : isContinuous Tan
:= sorry

/-- Tangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim tan x₀ = the (tan x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Tan_isContinuous x₀ h_dom

/-- Tangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim₋ tan x₀ = the (tan x₀)
:= by
  calc
    lim₋ tan x₀  =? lim tan x₀
                    := FuncLimitExpr.toLeft
    _            =  the (tan x₀)
                    := FuncLimitExpr.Tan h_dom

/-- Tangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim₊ tan x₀ = the (tan x₀)
:= by
  calc
    lim₊ tan x₀  =? lim tan x₀
                    := FuncLimitExpr.toRight
    _            =  the (tan x₀)
                    := FuncLimitExpr.Tan h_dom

/-- Cotangent Function's Continuity -/
lemma Cot_isContinuous
  : isContinuous Cot
:= sorry

/-- Cotangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim cot x₀ = the (cot x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cot_isContinuous x₀ h_dom

/-- Cotangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim₋ cot x₀ = the (cot x₀)
:= by
  calc
    lim₋ cot x₀  =? lim cot x₀
                    := FuncLimitExpr.toLeft
    _            =  the (cot x₀)
                    := FuncLimitExpr.Cot h_dom

/-- Cotangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim₊ cot x₀ = the (cot x₀)
:= by
  calc
    lim₊ cot x₀  =? lim cot x₀
                    := FuncLimitExpr.toRight
    _            =  the (cot x₀)
                    := FuncLimitExpr.Cot h_dom

/-- Secant Function's Continuity -/
lemma Sec_isContinuous
  : isContinuous Sec
:= sorry

/-- Secant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim sec x₀ = the (sec x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sec_isContinuous x₀ h_dom

/-- Secant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim₋ sec x₀ = the (sec x₀)
:= by
  calc
    lim₋ sec x₀  =? lim sec x₀
                    := FuncLimitExpr.toLeft
    _            =  the (sec x₀)
                    := FuncLimitExpr.Sec h_dom

/-- Secant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : lim₊ sec x₀ = the (sec x₀)
:= by
  calc
    lim₊ sec x₀  =? lim sec x₀
                    := FuncLimitExpr.toRight
    _            =  the (sec x₀)
                    := FuncLimitExpr.Sec h_dom

/-- Cosecant Function's Continuity -/
lemma Csc_isContinuous
  : isContinuous Csc
:= sorry

/-- Cosecant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim csc x₀ = the (csc x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Csc_isContinuous x₀ h_dom

/-- Cosecant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim₋ csc x₀ = the (csc x₀)
:= by
  calc
    lim₋ csc x₀  =? lim csc x₀
                    := FuncLimitExpr.toLeft
    _            =  the (csc x₀)
                    := FuncLimitExpr.Csc h_dom

/-- Cosecant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : lim₊ csc x₀ = the (csc x₀)
:= by
  calc
    lim₊ csc x₀  =? lim csc x₀
                    := FuncLimitExpr.toRight
    _            =  the (csc x₀)
                    := FuncLimitExpr.Csc h_dom

/-- Hyp-Sine Function's Continuity -/
lemma Sinh_isContinuous
  : isContinuous Sinh
:= sorry

/-- Hyp-Sine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Sinh {x₀ : ℝ}
  : lim sinh x₀ = the (sinh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sinh_isContinuous x₀ (mem_univ x₀)

/-- Hyp-Sine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Sinh {x₀ : ℝ}
  : lim₋ sinh x₀ = the (sinh x₀)
:= by
  calc
    lim₋ sinh x₀  =? lim sinh x₀
                     := FuncLimitExpr.toLeft
    _             =  the (sinh x₀)
                     := FuncLimitExpr.Sinh

/-- Hyp-Sine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Sinh {x₀ : ℝ}
  : lim₊ sinh x₀ = the (sinh x₀)
:= by
  calc
    lim₊ sinh x₀  =? lim sinh x₀
                     := FuncLimitExpr.toRight
    _             =  the (sinh x₀)
                     := FuncLimitExpr.Sinh

/-- Hyp-Cosine Function's Continuity -/
lemma Cosh_isContinuous
  : isContinuous Cosh
:= sorry

/-- Hyp-Cosine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Cosh {x₀ : ℝ}
  : lim cosh x₀ = the (cosh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cosh_isContinuous x₀ (mem_univ x₀)

/-- Hyp-Cosine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Cosh {x₀ : ℝ}
  : lim₋ cosh x₀ = the (cosh x₀)
:= by
  calc
    lim₋ cosh x₀  =? lim cosh x₀
                     := FuncLimitExpr.toLeft
    _             =  the (cosh x₀)
                     := FuncLimitExpr.Cosh

/-- Hyp-Cosine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Cosh {x₀ : ℝ}
  : lim₊ cosh x₀ = the (cosh x₀)
:= by
  calc
    lim₊ cosh x₀  =? lim cosh x₀
                     := FuncLimitExpr.toRight
    _             =  the (cosh x₀)
                     := FuncLimitExpr.Cosh

/-- Hyp-Tangent Function's Continuity -/
lemma Tanh_isContinuous
  : isContinuous Tanh
:= sorry

/-- Hyp-Tangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Tanh {x₀ : ℝ}
  : lim tanh x₀ = the (tanh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Tanh_isContinuous x₀ (mem_univ x₀)

/-- Hyp-Tangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Tanh {x₀ : ℝ}
  : lim₋ tanh x₀ = the (tanh x₀)
:= by
  calc
    lim₋ tanh x₀  =? lim tanh x₀
                     := FuncLimitExpr.toLeft
    _             =  the (tanh x₀)
                     := FuncLimitExpr.Tanh

/-- Hyp-Tangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Tanh {x₀ : ℝ}
  : lim₊ tanh x₀ = the (tanh x₀)
:= by
  calc
    lim₊ tanh x₀  =? lim tanh x₀
                     := FuncLimitExpr.toRight
    _             =  the (tanh x₀)
                     := FuncLimitExpr.Tanh

/-- Hyp-Cotangent Function's Continuity -/
lemma Coth_isContinuous
  : isContinuous Coth
:= sorry

/-- Hyp-Cotangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim coth x₀ = the (coth x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Coth_isContinuous x₀ h_dom

/-- Hyp-Cotangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim₋ coth x₀ = the (coth x₀)
:= by
  calc
    lim₋ coth x₀  =? lim coth x₀
                     := FuncLimitExpr.toLeft
    _             =  the (coth x₀)
                     := FuncLimitExpr.Coth h_dom

/-- Hyp-Cotangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim₊ coth x₀ = the (coth x₀)
:= by
  calc
    lim₊ coth x₀  =? lim coth x₀
                     := FuncLimitExpr.toRight
    _             =  the (coth x₀)
                     := FuncLimitExpr.Coth h_dom

/-- Hyp-Secant Function's Continuity -/
lemma Sech_isContinuous
  : isContinuous Sech
:= sorry

/-- Hyp-Secant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Sech {x₀ : ℝ}
  : lim sech x₀ = the (sech x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sech_isContinuous x₀ (mem_univ x₀)

/-- Hyp-Secant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Sech {x₀ : ℝ}
  : lim₋ sech x₀ = the (sech x₀)
:= by
  calc
    lim₋ sech x₀  =? lim sech x₀
                     := FuncLimitExpr.toLeft
    _             =  the (sech x₀)
                     := FuncLimitExpr.Sech

/-- Hyp-Secant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Sech {x₀ : ℝ}
  : lim₊ sech x₀ = the (sech x₀)
:= by
  calc
    lim₊ sech x₀  =? lim sech x₀
                     := FuncLimitExpr.toRight
    _             =  the (sech x₀)
                     := FuncLimitExpr.Sech

/-- Hyp-Cosecant Function's Continuity -/
lemma Csch_isContinuous
  : isContinuous Csch
:= sorry

/-- Hyp-Cosecant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim csch x₀ = the (csch x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Csch_isContinuous x₀ h_dom

/-- Hyp-Cosecant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim₋ csch x₀ = the (csch x₀)
:= by
  calc
    lim₋ csch x₀  =? lim csch x₀
                     := FuncLimitExpr.toLeft
    _             =  the (csch x₀)
                     := FuncLimitExpr.Csch h_dom

/-- Hyp-Cosecant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : lim₊ csch x₀ = the (csch x₀)
:= by
  calc
    lim₊ csch x₀  =? lim csch x₀
                     := FuncLimitExpr.toRight
    _             =  the (csch x₀)
                     := FuncLimitExpr.Csch h_dom

/-- Arc-Sine Function's Continuity for `x > -1 ∧ x < 1` -/
lemma Arcsin_isContinuous
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arcsin x
:= sorry

/-- Arc-Sine Function's Right Continuity at `-1` -/
lemma Arcsin_isRightContinuous_neg1
  : isRightContinuousAt Arcsin (-1)
:= sorry

/-- Arc-Sine Function's Left Continuity at `1` -/
lemma Arcsin_isLeftContinuous_1
  : isLeftContinuousAt Arcsin 1
:= sorry

/-- Arc-Sine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : lim arcsin x₀ = the (arcsin x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arcsin_isContinuous x₀ h_dom

/-- Arc-Sine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
  : lim₋ arcsin x₀ = the (arcsin x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply LeftLimit_to_LeftLimitExpr
    exact Arcsin_isLeftContinuous_1
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact h_dom.left
      · exact lt_of_le_of_ne h_dom.right h_1
    calc
      lim₋ arcsin x₀  =? lim arcsin x₀
                         := FuncLimitExpr.toLeft
      _               =  the (arcsin x₀)
                         := FuncLimitExpr.Arcsin h_dom'

/-- Arc-Sine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
  : lim₊ arcsin x₀ = the (arcsin x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply RightLimit_to_RightLimitExpr
    exact Arcsin_isRightContinuous_neg1
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact lt_of_le_of_ne h_dom.left (Ne.symm h_neg1)
      · exact h_dom.right
    calc
      lim₊ arcsin x₀  =? lim arcsin x₀
                         := FuncLimitExpr.toRight
      _               =  the (arcsin x₀)
                         := FuncLimitExpr.Arcsin h_dom'

/-- Arc-Cosine Function's Continuity for `x > -1 ∧ x < 1` -/
lemma Arccos_isContinuous
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arccos x
:= sorry

/-- Arc-Cosine Function's Right Continuity at `-1` -/
lemma Arccos_isRightContinuous_neg1
  : isRightContinuousAt Arccos (-1)
:= sorry

/-- Arc-Cosine Function's Left Continuity at `1` -/
lemma Arccos_isLeftContinuous_1
  : isLeftContinuousAt Arccos 1
:= sorry

/-- Arc-Cosine Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : lim arccos x₀ = the (arccos x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arccos_isContinuous x₀ h_dom

/-- Arc-Cosine Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
  : lim₋ arccos x₀ = the (arccos x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply LeftLimit_to_LeftLimitExpr
    exact Arccos_isLeftContinuous_1
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact h_dom.left
      · exact lt_of_le_of_ne h_dom.right h_1
    calc
      lim₋ arccos x₀  =? lim arccos x₀
                         := FuncLimitExpr.toLeft
      _               =  the (arccos x₀)
                         := FuncLimitExpr.Arccos h_dom'

/-- Arc-Cosine Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
  : lim₊ arccos x₀ = the (arccos x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply RightLimit_to_RightLimitExpr
    exact Arccos_isRightContinuous_neg1
  · have h_dom' : x₀ > -1 ∧ x₀ < 1 := by
      constructor
      · exact lt_of_le_of_ne h_dom.left (Ne.symm h_neg1)
      · exact h_dom.right
    calc
      lim₊ arccos x₀  =? lim arccos x₀
                         := FuncLimitExpr.toRight
      _               =  the (arccos x₀)
                         := FuncLimitExpr.Arccos h_dom'

/-- Arc-Tangent Function's Continuity -/
lemma Arctan_isContinuous
  : isContinuous Arctan
:= sorry

/-- Arc-Tangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arctan {x₀ : ℝ}
  : lim arctan x₀ = the (arctan x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arctan_isContinuous x₀ (mem_univ x₀)

/-- Arc-Tangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arctan {x₀ : ℝ}
  : lim₋ arctan x₀ = the (arctan x₀)
:= by
  calc
    lim₋ arctan x₀  =? lim arctan x₀
                       := FuncLimitExpr.toLeft
    _               =  the (arctan x₀)
                       := FuncLimitExpr.Arctan

/-- Arc-Tangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arctan {x₀ : ℝ}
  : lim₊ arctan x₀ = the (arctan x₀)
:= by
  calc
    lim₊ arctan x₀  =? lim arctan x₀
                       := FuncLimitExpr.toRight
    _               =  the (arctan x₀)
                       := FuncLimitExpr.Arctan

/-- Arc-Cotangent Function's Continuity -/
lemma Arccot_isContinuous
  : isContinuous Arccot
:= sorry

/-- Arc-Cotangent Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arccot {x₀ : ℝ}
  : lim arccot x₀ = the (arccot x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arccot_isContinuous x₀ (mem_univ x₀)

/-- Arc-Cotangent Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arccot {x₀ : ℝ}
  : lim₋ arccot x₀ = the (arccot x₀)
:= by
  calc
    lim₋ arccot x₀  =? lim arccot x₀
                       := FuncLimitExpr.toLeft
    _               =  the (arccot x₀)
                       := FuncLimitExpr.Arccot

/-- Arc-Cotangent Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arccot {x₀ : ℝ}
  : lim₊ arccot x₀ = the (arccot x₀)
:= by
  calc
    lim₊ arccot x₀  =? lim arccot x₀
                       := FuncLimitExpr.toRight
    _               =  the (arccot x₀)
                       := FuncLimitExpr.Arccot

/-- Arc-Secant Function's Continuity for `x < -1 ∨ x > 1` -/
lemma Arcsec_isContinuous
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arcsec x
:= sorry

/-- Arc-Secant Function's Left Continuity at `-1` -/
lemma Arcsec_isLeftContinuous_neg1
  : isLeftContinuousAt Arcsec (-1)
:= sorry

/-- Arc-Secant Function's Right Continuity at `1` -/
lemma Arcsec_isRightContinuous_1
  : isRightContinuousAt Arcsec 1
:= sorry

/-- Arc-Secant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : lim arcsec x₀ = the (arcsec x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arcsec_isContinuous x₀ h_dom

/-- Arc-Secant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
  : lim₋ arcsec x₀ = the (arcsec x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply LeftLimit_to_LeftLimitExpr
    exact Arcsec_isLeftContinuous_neg1
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact Std.lt_of_le_of_ne h_le h_neg1
      · right
        exact RCLike.ofReal_lt_ofReal.mp h_gt
    calc
      lim₋ arcsec x₀  =? lim arcsec x₀
                       := FuncLimitExpr.toLeft
      _             =  the (arcsec x₀)
                       := FuncLimitExpr.Arcsec h_dom'

/-- Arc-Secant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
  : lim₊ arcsec x₀ = the (arcsec x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply RightLimit_to_RightLimitExpr
    exact Arcsec_isRightContinuous_1
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact RCLike.ofReal_lt_ofReal.mp h_le
      · right
        exact Std.lt_of_le_of_ne h_gt (fun eq ↦ h_1 (Eq.symm eq))
    calc
      lim₊ arcsec x₀  =? lim arcsec x₀
                       := FuncLimitExpr.toRight
      _             =  the (arcsec x₀)
                       := FuncLimitExpr.Arcsec h_dom'

/-- Arc-Cosecant Function's Continuity for `x < -1 ∨ x > 1` -/
lemma Arccsc_isContinuous
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arccsc x
:= sorry

/-- Arc-Cosecant Function's Left Continuity at `-1` -/
lemma Arccsc_isLeftContinuous_neg1
  : isLeftContinuousAt Arccsc (-1)
:= sorry

/-- Arc-Cosecant Function's Right Continuity at `1` -/
lemma Arccsc_isRightContinuous_1
  : isRightContinuousAt Arccsc 1
:= sorry

/-- Arc-Cosecant Function's Continuity (Expression) -/
lemma FuncLimitExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : lim arccsc x₀ = the (arccsc x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Arccsc_isContinuous x₀ h_dom

/-- Arc-Cosecant Function's Left Continuity (Expression) -/
lemma LeftLimitExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
  : lim₋ arccsc x₀ = the (arccsc x₀)
:= by
  by_cases h_neg1 : x₀ = -1
  · rw [h_neg1]
    apply LeftLimit_to_LeftLimitExpr
    exact Arccsc_isLeftContinuous_neg1
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact Std.lt_of_le_of_ne h_le h_neg1
      · right
        exact RCLike.ofReal_lt_ofReal.mp h_gt
    calc
      lim₋ arccsc x₀  =? lim arccsc x₀
                       := FuncLimitExpr.toLeft
      _             =  the (arccsc x₀)
                       := FuncLimitExpr.Arccsc h_dom'

/-- Arc-Cosecant Function's Right Continuity (Expression) -/
lemma RightLimitExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
  : lim₊ arccsc x₀ = the (arccsc x₀)
:= by
  by_cases h_1 : x₀ = 1
  · rw [h_1]
    apply RightLimit_to_RightLimitExpr
    exact Arccsc_isRightContinuous_1
  · have h_dom' : x₀ < -1 ∨ x₀ > 1 := by
      rcases h_dom with h_le | h_gt
      · left
        exact RCLike.ofReal_lt_ofReal.mp h_le
      · right
        exact Std.lt_of_le_of_ne h_gt (fun eq ↦ h_1 (Eq.symm eq))
    calc
      lim₊ arccsc x₀  =? lim arccsc x₀
                       := FuncLimitExpr.toRight
      _             =  the (arccsc x₀)
                       := FuncLimitExpr.Arccsc h_dom'
