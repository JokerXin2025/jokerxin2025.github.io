/-
    «Calculus_21».Limit.Elementary
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Rules
import «Calculus_21».Continuity.Rules
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option linter.style.header false

open Real  -- TEMPORARY!
local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)
local macro "infer" steps:inferSteps : tactic => `(tactic| exact infer $steps)


/-! # Elementary Functions' Continuity -/

section
variable {F : Function} {x₀ : ℝ}

private lemma isContinuousAt_abs_lemma
    (h_dom : ∃ δ > 0, Nbho x₀ δ ⊆ F.domain)
    (h_bound : ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, |F.map x - F.map x₀| < ε)
  : isContinuousAt F x₀
:= by
  obtain ⟨δ, hδ, h_dom⟩ := h_dom
  refine ⟨h_dom ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · exists δ with hδ
    intro _ h_x
    exact h_dom (Nbhd_subset_Nbho h_x)
  · intro ε h_ε
    rcases h_bound ε h_ε with ⟨δ, hδ, h⟩
    exists δ with hδ
    intro x h_x
    rw [Nbho_abs]
    exact h x h_x

private lemma isLeftContinuousAt_abs_lemma
    (h_dom : ∃ δ > 0, Ioc (x₀ - δ) x₀ ⊆ F.domain)
    (h_bound : ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, |F.map x - F.map x₀| < ε)
  : isLeftContinuousAt F x₀
:= by
  obtain ⟨δ, hδ, h_dom⟩ := h_dom
  refine ⟨h_dom ⟨by linarith, le_rfl⟩, ?_, ?_⟩
  · exists δ with hδ
    intro _ h_x
    exact h_dom ⟨h_x.1, h_x.2.le⟩
  · intro ε h_ε
    rcases h_bound ε h_ε with ⟨δ, hδ, h⟩
    exists δ with hδ
    intro x h_x
    rw [Nbho_abs]
    exact h x h_x

private lemma isRightContinuousAt_abs_lemma
    (h_dom : ∃ δ > 0, Ico x₀ (x₀ + δ) ⊆ F.domain)
    (h_bound : ∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), |F.map x - F.map x₀| < ε)
  : isRightContinuousAt F x₀
:= by
  obtain ⟨δ, hδ, h_dom⟩ := h_dom
  refine ⟨h_dom ⟨le_rfl, by linarith⟩, ?_, ?_⟩
  · exists δ with hδ
    intro _ h_x
    exact h_dom ⟨h_x.1.le, h_x.2⟩
  · intro ε h_ε
    rcases h_bound ε h_ε with ⟨δ, hδ, h⟩
    exists δ with hδ
    intro x h_x
    rw [Nbho_abs]
    exact h x h_x

macro "prove_continuity" : tactic => `(tactic|
  first
  | apply isContinuousAt_abs_lemma
  | apply isLeftContinuousAt_abs_lemma
  | apply isRightContinuousAt_abs_lemma
)

end

private lemma inv_mem_Ioo_of_lt_neg_one {x : ℝ} (h_x : x < -1) :
    x⁻¹ ∈ Ioo (-1) 1 := by
  have h_xneg : x < 0 := by linarith
  have hinvneg : x⁻¹ < 0 := inv_neg''.mpr h_xneg
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  constructor <;> nlinarith

private lemma inv_mem_Ioo_of_one_lt {x : ℝ} (h_x : 1 < x) :
    x⁻¹ ∈ Ioo (-1) 1 := by
  have h_xpos : 0 < x := by linarith
  have hinvpos : 0 < x⁻¹ := inv_pos.mpr h_xpos
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  constructor <;> nlinarith

private lemma abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |ln (1 + t)| ≤ 2 * |t| := by
  have ht_low : -(1 / 2) ≤ t := calc
    -(1 / 2) ≤ -|t| := neg_le_neg ht
    _             ≤ t    := neg_abs_le t
  have ht_high : t ≤ 1 / 2 := calc
    t ≤ |t|   := le_abs_self t
    _ ≤ 1 / 2 := ht
  have hpos : 0 < 1 + t := by linarith
  by_cases htn : 0 ≤ t
  · have hlog_nonneg : 0 ≤ ln (1 + t) := by
      rw [← log_one]
      exact log_le_log zero_lt_one (by linarith)
    rw [abs_of_nonneg hlog_nonneg, abs_of_nonneg htn]
    have h_log_upper : ln (1 + t) ≤ (1 + t) - 1 :=
      log_le_sub_one_of_pos hpos
    auto_side_condition
  · have htneg : t < 0 := lt_of_not_ge htn
    have hlog_nonpos : ln (1 + t) ≤ 0 := by
      rw [← log_one]
      exact log_le_log hpos (by linarith)
    rw [abs_of_nonpos hlog_nonpos, abs_of_neg htneg]
    have h_log_lower : 1 - (1 + t)⁻¹ ≤ ln (1 + t) :=
      one_sub_inv_le_log_of_pos hpos
    have hden : 1 / 2 ≤ 1 + t := by linarith
    have hfrac : -t / (1 + t) ≤ 2 * (-t) := by
      apply (div_le_iff₀ hpos).2
      nlinarith
    have hid : -(ln (1 + t)) ≤ -t / (1 + t) := by
      calc
        -(ln (1 + t)) ≤ -(1 - (1 + t)⁻¹) := neg_le_neg h_log_lower
        _ = -t / (1 + t) := by field
    linarith

/-- Constant Function's Continuity -/
protected lemma Continuity.Constant {C : ℝ}
  : isContinuous (Constant C)
:= by
  intro _ h_x₀
  unfold isContinuousAt FuncLimit
  refine ⟨h_x₀, ?_⟩
  constructor
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε _
    exists 1 with zero_lt_one
    intro _ _
    change C ∈ Nbho C ε
    constructor <;> linarith

/-- Identity Function's Continuity -/
protected lemma Continuity.Identity
  : isContinuous Identity
:= by
  intro x₀ h_x₀
  unfold isContinuousAt FuncLimit
  refine ⟨h_x₀, ?_⟩
  constructor
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    exists ε with h_ε
    intro x h_x
    change x ∈ Nbho x₀ ε
    exact Nbhd_subset_Nbho h_x

/-- Absolute Value Function's Continuity -/
protected lemma Continuity.Abs
  : isContinuous Abs
:= by
  intro x₀ _
  prove_continuity
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    exists ε with h_ε
    intro x h_x
    calc
      |(|x| - |x₀|)|  ≤ |x - x₀|
                        := abs_abs_sub_abs_le x x₀
      _               < ε
                        := (Nbho_abs x).mp (Nbhd_subset_Nbho h_x)

/-- Square Root Function's Continuity for `x > 0` -/
protected lemma Continuity.Sqrt
  : ∀ x > 0, isContinuousAt Sqrt x
:= by
  intro x₀ h_x₀
  prove_continuity
  · exists x₀ / 2 with half_pos h_x₀
    intro x h_x
    change 0 ≤ x
    linarith [h_x.1]
  · intro ε h_ε
    let δ := min (x₀ / 2) (ε * √x₀)
    have hsqrt : √x₀ > 0 := by positivity
    have hδ : 0 < δ := lt_min (half_pos h_x₀) (mul_pos h_ε hsqrt)
    exists δ with hδ
    intro x h_x
    have h_dist_δ : |x - x₀| < δ := infer
      x ∈ Nbhd x₀ δ ⇒ x ∈ Nbho x₀ δ
                      := Nbhd_subset_Nbho h_x
      _             ⇒ |x - x₀| < δ
                      := (Nbho_abs x).mp ?_
    have h_dist_half : |x - x₀| < x₀ / 2 := calc
      |x - x₀| < δ      := h_dist_δ
      _         ≤ x₀ / 2 := min_le_left _ _
    have h_xpos : 0 < x := by
      rw [abs_lt] at h_dist_half
      linarith
    have hsum : √x + √x₀ > 0 := by positivity
    have hfactor : (√x - √x₀) * (√x + √x₀) = x - x₀ := by
      have h_x_sq : √x * √x = x := mul_self_sqrt h_xpos.le
      have h_x₀_sq : √x₀ * √x₀ = x₀ := mul_self_sqrt h_x₀.le
      nlinarith
    change |√x - √x₀| < ε
    calc
      |√x - √x₀| = |x - x₀| / |√x + √x₀| := by
        apply (eq_div_iff (abs_ne_zero.mpr hsum.ne')).2
        rw [← abs_mul, hfactor]
      _ ≤ |x - x₀| / √x₀ := by
        rw [abs_of_pos hsum]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hsqrt
          (by linarith [sqrt_nonneg x])
      _ < (ε * √x₀) / √x₀ := by
        gcongr
        calc
          |x - x₀| < δ        := h_dist_δ
          _         ≤ ε * √x₀ := min_le_right _ _
      _ = ε := by field

/-- Square Root Function's Right Continuity at `0` -/
protected lemma RightContinuity.Sqrt_0
  : isRightContinuousAt Sqrt 0
:= by
  prove_continuity
  · exists 1 with zero_lt_one
    intro x h_x
    exact h_x.1
  · intro ε h_ε
    exists ε ^ 2 with sq_pos_of_pos h_ε
    intro x h_x
    simp only [Sqrt, sqrt_zero, sub_zero, abs_of_nonneg (sqrt_nonneg x)]
    exact (sqrt_lt' h_ε).2 (by simpa using h_x.2)

/-- Power Function's Right Continuity at `0` -/
protected lemma RightContinuity.Power_0 {a : ℝ}
    (h_a : a > 0)
  : isRightContinuousAt (Power a) 0
:= by
  prove_continuity
  · exists 1 with zero_lt_one
    simp only [zero_add, Power, gt_iff_lt, h_a, ↓reduceIte]
    intro x h_x
    exact h_x.1
  · intro ε h_ε
    let δ := ε ^ a⁻¹
    have hδ : 0 < δ := rpow_pos_of_pos h_ε _
    exists δ with hδ
    intro x h_x
    simp only [Power, if_pos h_a]
    change |x ^ a - 0 ^ a| < ε
    rw [zero_rpow h_a.ne', sub_zero,
      abs_of_nonneg (rpow_nonneg h_x.1.le _)]
    calc
      x ^ a < δ ^ a := rpow_lt_rpow h_x.1.le (by simpa using h_x.2) h_a
      _ = ε := rpow_inv_rpow h_ε.le h_a.ne'

/-- Power Function's Continuity for `n : ℤ` -/
protected lemma Continuity.Power_ℤ {n : ℤ}
  : isContinuous (NPower n)
:= by
  intro x₀ h_x₀
  cases n with
  | ofNat m =>
    cases m with
    | zero =>
      have h_x₀_ne : x₀ ≠ 0 := by simpa [NPower] using h_x₀
      have hc : isContinuousAt (Constant 1) x₀ :=
        Continuity.Constant _ (mem_univ _)
      apply Continuity.Congr hc
      exists |x₀| with abs_pos.mpr h_x₀_ne
      constructor
      · intro x h_x
        have h_xne : x ≠ 0 := by
          intro h
          subst x
          have hzero : |0 - x₀| < |x₀| := (Nbho_abs 0).mp h_x
          rw [abs_sub_comm, sub_zero] at hzero
          exact lt_irrefl _ hzero
        simpa [NPower] using h_xne
      · intro x _
        simp [NPower, Constant, npow, const]
    | succ m =>
      have hid : isContinuousAt Identity x₀ := Continuity.Identity x₀ (mem_univ _)
      have hp : isContinuousAt (Identity ^ (m + 1)) x₀ :=
        ⟨hid.1, FuncLimit.MSPow (n := m + 1) hid.2⟩
      have hmpos : (0 : ℤ) < Int.ofNat (m + 1) :=
        Int.ofNat_lt.mpr (Nat.zero_lt_succ m)
      apply Continuity.Congr hp
      exists 1 with zero_lt_one
      constructor
      · simp [NPower]
      · intro x _
        unfold Identity NPower
        rw [if_pos hmpos]
        simp only [npow]
        change x ^ (m + 1) = x ^ ((m + 1 : ℕ) : ℤ)
        rw [zpow_natCast]
  | negSucc m =>
    have h_x₀_ne : x₀ ≠ 0 := by simpa [NPower] using h_x₀
    have hp_ne : (Identity ^ (m + 1)).map x₀ ≠ 0 := by
      change x₀ ^ (m + 1) ≠ 0
      exact pow_ne_zero _ h_x₀_ne
    have hinv : isContinuousAt (Identity ^ (m + 1))⁻¹ x₀ := infer
            isContinuousAt Identity x₀
         => isContinuousAt (Identity ^ (m + 1)) x₀
            := ⟨(Continuity.Identity x₀ (mem_univ _)).1,
          FuncLimit.MSPow (n := m + 1) (Continuity.Identity x₀ (mem_univ _)).2⟩
      _  => isContinuousAt (Identity ^ (m + 1))⁻¹ x₀
            := (fun ⟨hdom, hlim⟩ =>
          ⟨⟨hdom, hp_ne⟩, FuncLimit.Inv hp_ne hlim⟩) ?_
    apply Continuity.Congr hinv
    exists |x₀| with abs_pos.mpr h_x₀_ne
    constructor
    · intro x h_x h
      subst x
      have hzero : |0 - x₀| < |x₀| := (Nbho_abs 0).mp h_x
      rw [abs_sub_comm, sub_zero] at hzero
      exact lt_irrefl _ hzero
    · intro x _
      change (x ^ (m + 1))⁻¹ = x ^ (Int.negSucc m)
      rw [zpow_negSucc]

/-- Natural Exponential Function's Continuity -/
protected lemma Continuity.Exp
  : isContinuous Exp
:= by
  intro x₀ _
  prove_continuity
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    let δ := min 1 (ε / (2 * exp x₀))
    exists δ with by positivity
    intro x h_x
    have h_dist_δ : |x - x₀| < δ := infer
      x ∈ Nbhd x₀ δ  => x ∈ Nbho x₀ δ
                        := Nbhd_subset_Nbho h_x
      _              => |x - x₀| < δ
                        := (Nbho_abs x).mp ?_
    have h_dist_1 : |x - x₀| < 1 := calc
        |x - x₀|  < δ := h_dist_δ
        _         ≤ 1 := by apply min_le_left
    calc
      |exp x - exp x₀|  = |exp x₀ * (exp (x - x₀) - 1)|
                          := by rw [mul_sub, mul_one, ← exp_add]; congr 2; ring_nf
      _                 = exp x₀ * |exp (x - x₀) - 1|
                          := by rw [abs_mul, abs_of_pos (exp_pos _)]
      _                 ≤ exp x₀ * (2 * |x - x₀|)
                          := by
                            apply mul_le_mul_of_nonneg_left
                            · apply abs_exp_sub_one_le
                              exact le_of_lt h_dist_1
                            · positivity
      _                 < exp x₀ * (2 * δ)
                          := by gcongr
      _                 ≤ exp x₀ * (2 * (ε / (2 * exp x₀)))
                          := by gcongr; apply min_le_right
      _                 = ε
                          := by field

/-- Exponential Function's Continuity -/
protected lemma Continuity.Expow {a : ℝ}
    (h_a : a > 0)
  : isContinuous (Expow a)
:= by
  intro x₀ _
  rw [← Expow_eq h_a]
  infer
          isContinuousAt (Constant (ln a)) x₀
       => isContinuousAt (Constant (ln a) * Identity) x₀
          := Mul (Continuity.Constant x₀ (mem_univ _))
            (Continuity.Identity x₀ (mem_univ x₀))
    _  => isContinuousAt (Exp ⊙ (Constant (ln a) * Identity)) x₀
          := Comp (Continuity.Exp (ln a * x₀) (mem_univ _)) ?_

/-- Natural Logarithm Function's Continuity -/
protected lemma Continuity.Ln
  : isContinuous Ln
:= by
  intro x₀ h_x₀
  change 0 < x₀ at h_x₀
  prove_continuity
  · exists x₀ / 2 with half_pos h_x₀
    intro x h_x
    change x > 0
    linarith [h_x.1]
  · intro ε h_ε
    let δ := min (x₀ / 2) (ε * x₀ / 2)
    have hδ : 0 < δ := by positivity
    exists δ with hδ
    intro x h_x
    have h_dist_δ : |x - x₀| < δ := infer
      x ∈ Nbhd x₀ δ  => x ∈ Nbho x₀ δ
                        := Nbhd_subset_Nbho h_x
      _              => |x - x₀| < δ
                        := (Nbho_abs x).mp ?_
    have h_dist_half : |x - x₀| < x₀ / 2 := calc
      |x - x₀| < δ       := h_dist_δ
      _         ≤ x₀ / 2 := min_le_left _ _
    have h_xpos : 0 < x := by
      rw [abs_lt] at h_dist_half
      linarith
    let t := (x - x₀) / x₀
    have ht : |t| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos h_x₀]
      apply (div_le_iff₀ h_x₀).2
      linarith [h_dist_half]
    have h_log_bound : |ln (1 + t)| ≤ 2 * |t| :=
      abs_log_one_add_le ht
    have hform : ln x - ln x₀ = ln (1 + t) := by
      change Real.log x - Real.log x₀ = Real.log (1 + t)
      rw [← log_div h_xpos.ne' h_x₀.ne']
      congr 1
      field
    change |ln x - ln x₀| < ε
    rw [hform]
    calc
      |ln (1 + t)| ≤ 2 * |t| := h_log_bound
      _ = 2 * |x - x₀| / x₀ := by
        rw [abs_div, abs_of_pos h_x₀]
        ring
      _ < 2 * (ε * x₀ / 2) / x₀ := by
        gcongr
        calc
          |x - x₀| < δ            := h_dist_δ
          _         ≤ ε * x₀ / 2 := min_le_right _ _
      _ = ε := by field

/-- Logarithm Function's Continuity -/
protected lemma Continuity.Log {a : ℝ}
    (h_a : a > 0 ∧ a ≠ 1)
  : isContinuous (Log a)
:= by
  intro x₀ h_x₀
  rw [← Log_eq h_a.1 h_a.2]
  apply Div
  · exact Continuity.Ln x₀ h_x₀
  · exact Continuity.Constant x₀ (mem_univ _)
  · change Real.log a ≠ 0
    rw [log_ne_zero]
    grind only

/-- Power Function's Continuity for `x > 0` -/
protected lemma Continuity.Power {a : ℝ}
  : ∀ x > 0, isContinuousAt (Power a) x
:= by
  intro x₀ h_x₀
  have hcomp : isContinuousAt (Exp ⊙ (Ln * Constant a)) x₀ :=
    infer
            isContinuousAt Ln x₀
         => isContinuousAt (Ln * Constant a) x₀
            := Mul (Continuity.Ln _ h_x₀)
              (Continuity.Constant x₀ (mem_univ _))
      _  => isContinuousAt (Exp ⊙ (Ln * Constant a)) x₀
            := Comp (Continuity.Exp (ln x₀ * a) (mem_univ _)) ?_
  apply Continuity.Congr hcomp
  exists x₀ / 2 with half_pos h_x₀
  constructor
  · intro x h_x
    have h_xpos : 0 < x := by
      rw [Nbho_abs, abs_lt] at h_x
      linarith
    unfold Power
    split
    · exact h_xpos.le
    · exact h_xpos
  · intro x h_x
    have h_xpos : 0 < x := by
      rw [Nbho_abs, abs_lt] at h_x
      linarith
    simp only [Function_Comp, Exp, Ln, Constant, Function.comp_apply, Power]
    split <;> exact (rpow_def_of_pos h_xpos a).symm

/-- Sine Function's Continuity -/
protected lemma Continuity.Sin
  : isContinuous Sin
:= by
  intro x₀ _
  prove_continuity
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    exists ε with h_ε
    intro x h_x
    calc
      |sin x - sin x₀|  ≤ |x - x₀|
                          := abs_sin_sub_sin_le _ _
      _                 < ε
                          := (Nbho_abs _).mp (Nbhd_subset_Nbho h_x)

/-- Cosine Function's Continuity -/
protected lemma Continuity.Cos
  : isContinuous Cos
:= by
  intro x₀ _
  prove_continuity
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    exists ε with h_ε
    intro x h_x
    calc
      |cos x - cos x₀|  ≤ |x - x₀|
                          := abs_cos_sub_cos_le _ _
      _                 < ε
                          := (Nbho_abs _).mp (Nbhd_subset_Nbho h_x)

/-- Tangent Function's Continuity -/
protected lemma Continuity.Tan
  : isContinuous Tan
:= by
  intro x₀ h_x₀
  rw [← Tan_eq]
  apply Div
  · exact Continuity.Sin x₀ (mem_univ _)
  · exact Continuity.Cos x₀ (mem_univ _)
  · exact h_x₀

/-- Cotangent Function's Continuity -/
protected lemma Continuity.Cot
  : isContinuous Cot
:= by
  intro x₀ h_x₀
  rw [← Cot_eq]
  apply Div
  · exact Continuity.Cos x₀ (mem_univ _)
  · exact Continuity.Sin x₀ (mem_univ _)
  · exact h_x₀

/-- Secant Function's Continuity -/
protected lemma Continuity.Sec
  : isContinuous Sec
:= by
  intro x₀ h_x₀
  rw [← Sec_eq]
  apply Div
  · exact Continuity.Constant x₀ (mem_univ _)
  · exact Continuity.Cos x₀ (mem_univ _)
  · exact h_x₀

/-- Cosecant Function's Continuity -/
protected lemma Continuity.Csc
  : isContinuous Csc
:= by
  intro x₀ h_x₀
  rw [← Csc_eq]
  apply Div
  · exact Continuity.Constant x₀ (mem_univ _)
  · exact Continuity.Sin x₀ (mem_univ _)
  · exact h_x₀

/-- Hyp-Sine Function's Continuity -/
protected lemma Continuity.Sinh
  : isContinuous Sinh
:= by
  intro x₀ _
  rw [← Sinh_eq]
  infer
          isContinuousAt Identity x₀
       => isContinuousAt (-Identity) x₀
          := Neg (Continuity.Identity x₀ (mem_univ _))
    _  => isContinuousAt (Exp ⊙ (-Identity)) x₀
          := Comp (Continuity.Exp (-x₀) (mem_univ _)) ?_
    _  => isContinuousAt (Exp - Exp ⊙ (-Identity)) x₀
          := Sub (Continuity.Exp x₀ (mem_univ _)) ?_
    _  => isContinuousAt ((2 : ℝ)⁻¹ • (Exp - Exp ⊙ (-Identity))) x₀
          := SMul ?_

/-- Hyp-Cosine Function's Continuity -/
protected lemma Continuity.Cosh
  : isContinuous Cosh
:= by
  intro x₀ _
  rw [← Cosh_eq]
  infer
          isContinuousAt Identity x₀
       => isContinuousAt (-Identity) x₀
          := Neg (Continuity.Identity x₀ (mem_univ _))
    _  => isContinuousAt (Exp ⊙ (-Identity)) x₀
          := Comp (Continuity.Exp (-x₀) (mem_univ _)) ?_
    _  => isContinuousAt (Exp + Exp ⊙ (-Identity)) x₀
          := Add (Continuity.Exp x₀ (mem_univ _)) ?_
    _  => isContinuousAt ((2 : ℝ)⁻¹ • (Exp + Exp ⊙ (-Identity))) x₀
          := SMul ?_

/-- Hyp-Tangent Function's Continuity -/
protected lemma Continuity.Tanh
  : isContinuous Tanh
:= by
  intro x₀ _
  rw [← Tanh_eq]
  apply Div
  · exact Continuity.Sinh x₀ (mem_univ _)
  · exact Continuity.Cosh x₀ (mem_univ _)
  · linarith! [cosh_pos x₀]

/-- Hyp-Cotangent Function's Continuity -/
protected lemma Continuity.Coth
  : isContinuous Coth
:= by
  intro x₀ h_x₀
  rw [← Coth_eq]
  apply Div
  · exact Continuity.Constant x₀ (mem_univ _)
  · exact Continuity.Tanh x₀ (mem_univ _)
  · exact Tanh_ne_zero_iff.mpr h_x₀

/-- Hyp-Secant Function's Continuity -/
protected lemma Continuity.Sech
  : isContinuous Sech
:= by
  intro x₀ _
  rw [← Sech_eq]
  apply Div
  · exact Continuity.Constant x₀ (mem_univ _)
  · exact Continuity.Cosh x₀ (mem_univ _)
  · linarith! [cosh_pos x₀]

/-- Hyp-Cosecant Function's Continuity -/
protected lemma Continuity.Csch
  : isContinuous Csch
:= by
  intro x₀ h_x₀
  rw [← Csch_eq]
  apply Div
  · exact Continuity.Constant x₀ (mem_univ _)
  · exact Continuity.Sinh x₀ (mem_univ _)
  · exact Sinh_ne_zero_iff.mpr h_x₀

/-- Arc-Sine Function's Continuity for `x > -1 ∧ x < 1` -/
protected lemma Continuity.Arcsin
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arcsin x
:= by
  intro x₀ h_x₀
  let α := arcsin x₀
  have hαlo : -(π / 2) < α := neg_pi_div_two_lt_arcsin.mpr h_x₀.1
  have hαhi : α < π / 2 := arcsin_lt_pi_div_two.mpr h_x₀.2
  prove_continuity
  · let δ := min ((x₀ + 1) / 2) ((1 - x₀) / 2)
    have hδ : 0 < δ := lt_min (by linarith [h_x₀.1]) (by linarith [h_x₀.2])
    exists δ with hδ
    intro x h_x
    have h_dist : |x - x₀| < δ := (Nbho_abs x).mp h_x
    rw [abs_lt] at h_dist
    exact ⟨by linarith [min_le_left ((x₀ + 1) / 2) ((1 - x₀) / 2)],
      by linarith [min_le_right ((x₀ + 1) / 2) ((1 - x₀) / 2)]⟩
  · intro ε h_ε
    let η := min (ε / 2) (min ((α + π / 2) / 2) ((π / 2 - α) / 2))
    have hη : 0 < η := lt_min (half_pos h_ε)
      (lt_min (by linarith) (by linarith))
    have hηε : η < ε := calc
      η ≤ ε / 2 := min_le_left _ _
      _ < ε     := half_lt_self h_ε
    have hη_left : η ≤ (α + π / 2) / 2 := calc
      η ≤ min ((α + π / 2) / 2) ((π / 2 - α) / 2) := min_le_right _ _
      _ ≤ (α + π / 2) / 2 := min_le_left _ _
    have hη_right : η ≤ (π / 2 - α) / 2 := calc
      η ≤ min ((α + π / 2) / 2) ((π / 2 - α) / 2) := min_le_right _ _
      _ ≤ (π / 2 - α) / 2 := min_le_right _ _
    have hlo_mem : α - η ∈ Icc (-(π / 2)) (π / 2) := by
      constructor <;> linarith
    have hhi_mem : α + η ∈ Icc (-(π / 2)) (π / 2) := by
      constructor <;> linarith
    have hsinα : sin α = x₀ := sin_arcsin h_x₀.1.le h_x₀.2.le
    have hlo : sin (α - η) < x₀ := by
      rw [← hsinα]
      exact strictMonoOn_sin hlo_mem (arcsin_mem_Icc x₀) (by linarith)
    have hhi : x₀ < sin (α + η) := by
      rw [← hsinα]
      exact strictMonoOn_sin (arcsin_mem_Icc x₀) hhi_mem (by linarith)
    let δ := min (x₀ - sin (α - η)) (sin (α + η) - x₀)
    have hδ : 0 < δ := lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
    exists δ with hδ
    intro x h_x
    have h_dist_δ : |x - x₀| < δ := infer
      x ∈ Nbhd x₀ δ ⇒ x ∈ Nbho x₀ δ
                      := Nbhd_subset_Nbho h_x
      _             ⇒ |x - x₀| < δ
                      := (Nbho_abs x).mp ?_
    rw [abs_lt] at h_dist_δ
    have h_xlo : sin (α - η) < x := by
      linarith [min_le_left (x₀ - sin (α - η)) (sin (α + η) - x₀)]
    have h_xhi : x < sin (α + η) := by
      linarith [min_le_right (x₀ - sin (α - η)) (sin (α + η) - x₀)]
    have harclo : α - η < arcsin x := by
      rw [← arcsin_sin hlo_mem.1 hlo_mem.2]
      exact arcsin_lt_arcsin (neg_one_le_sin _) h_xlo
        (le_trans (le_of_lt h_xhi) (sin_le_one _))
    have harchi : arcsin x < α + η := by
      rw [← arcsin_sin hhi_mem.1 hhi_mem.2]
      exact arcsin_lt_arcsin
        (le_trans (neg_one_le_sin _) (le_of_lt h_xlo)) h_xhi (sin_le_one _)
    change |arcsin x - arcsin x₀| < ε
    rw [abs_lt]
    constructor <;> linarith

/-- Arc-Sine Function's Right Continuity at `-1` -/
protected lemma RightContinuity.Arcsin_neg1
  : isRightContinuousAt Arcsin (-1)
:= by
  prove_continuity
  · exists 2 with by norm_num
    intro x h_x
    change -1 ≤ x ∧ x ≤ 1
    constructor <;> norm_num at h_x ⊢ <;> linarith
  · intro ε h_ε
    let η := min (ε / 2) (π / 4)
    have hη : 0 < η := lt_min (half_pos h_ε) (by positivity)
    have hηε : η < ε := calc
      η ≤ ε / 2 := min_le_left _ _
      _ < ε     := half_lt_self h_ε
    have hangle : -(π / 2) + η ∈ Icc (-(π / 2)) (π / 2) := by
      constructor
      · linarith
      · have hη_pi : η ≤ π / 4 := min_le_right _ _
        linarith [pi_pos]
    let δ := sin (-(π / 2) + η) + 1
    have hδ : 0 < δ := by
      have hmono : sin (-(π / 2)) < sin (-(π / 2) + η) := strictMonoOn_sin
        ⟨le_rfl, by linarith [pi_pos]⟩ hangle (by linarith)
      rw [sin_neg, sin_pi_div_two] at hmono
      linarith
    exists δ with hδ
    intro x h_x
    have h_xhi : x < sin (-(π / 2) + η) := by
      norm_num at h_x ⊢
      linarith
    have h_xlo : -1 < x := h_x.1
    have harclo : -(π / 2) < arcsin x :=
      neg_pi_div_two_lt_arcsin.mpr h_xlo
    have harchi : arcsin x < -(π / 2) + η := by
      rw [← arcsin_sin hangle.1 hangle.2]
      exact arcsin_lt_arcsin (by linarith) h_xhi (sin_le_one _)
    change |arcsin x - arcsin (-1)| < ε
    rw [arcsin_neg_one, abs_lt]
    constructor <;> linarith

/-- Arc-Sine Function's Left Continuity at `1` -/
protected lemma LeftContinuity.Arcsin_1
  : isLeftContinuousAt Arcsin 1
:= by
  prove_continuity
  · exists 2 with zero_lt_two
    intro x h_x
    change -1 ≤ x ∧ x ≤ 1
    constructor <;> norm_num at h_x ⊢ <;> linarith
  · intro ε h_ε
    let η := min (ε / 2) (π / 4)
    have h_η : η > 0 := by positivity
    have h_η_le_ε : η < ε := calc
      η ≤ ε / 2
          := min_le_left _ _
      _ < ε
          := half_lt_self h_ε
    have hangle : π / 2 - η ∈ Icc (-(π / 2)) (π / 2) := by
      constructor
      · linarith [min_le_right (ε / 2) (π / 4)]
      · linarith
    let δ := 1 - sin (π / 2 - η)
    have h_δ : δ > 0 := by
      dsimp [δ]
      rw [← sin_pi_div_two]
      exact sub_pos.mpr (strictMonoOn_sin hangle
        ⟨by linarith [pi_pos], le_rfl⟩ (by linarith))
    exists δ with h_δ
    intro x h_x
    have h_xhi : x < 1 := h_x.2
    have harclo : π / 2 - η < arcsin x := by
      rw [← arcsin_sin hangle.1 hangle.2]
      apply arcsin_lt_arcsin
      · exact neg_one_le_sin _
      · norm_num at h_x ⊢
        linarith
      · linarith
    have harchi : arcsin x < π / 2 := arcsin_lt_pi_div_two.mpr h_xhi
    change |arcsin x - arcsin 1| < ε
    rw [arcsin_one, abs_lt]
    constructor <;> linarith

/-- Arc-Cosine Function's Continuity for `x > -1 ∧ x < 1` -/
protected lemma Continuity.Arccos
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arccos x
:= by
  intro x₀ h_x₀
  have hsub : isContinuousAt (Constant (π / 2) - Arcsin) x₀ := by
    apply Sub
    · exact Continuity.Constant _ (mem_univ _)
    · exact Continuity.Arcsin _ h_x₀
  rw [← Arccos_eq]
  exact hsub

/-- Arc-Cosine Function's Right Continuity at `-1` -/
protected lemma RightContinuity.Arccos_neg1
  : isRightContinuousAt Arccos (-1)
:= by
  refine ⟨by norm_num [Arccos], ?_⟩
  have h_arcsin_right := RightContinuity.Arcsin_neg1.2
  refine ⟨h_arcsin_right.1, ?_⟩
  intro ε h_ε
  rcases h_arcsin_right.2 ε h_ε with ⟨δ, hδ, hlim⟩
  exists δ with hδ
  intro x h_x
  have h_arcsin_nbho := hlim x h_x
  rw [Nbho_abs] at h_arcsin_nbho ⊢
  change |arccos x - arccos (-1)| < ε
  rw [arccos_eq_pi_div_two_sub_arcsin,
    arccos_eq_pi_div_two_sub_arcsin]
  have heq : π / 2 - arcsin x - (π / 2 - arcsin (-1)) =
      -(arcsin x - arcsin (-1)) := by ring
  rw [heq, abs_neg]
  change |arcsin x - arcsin (-1)| < ε
  exact h_arcsin_nbho

/-- Arc-Cosine Function's Left Continuity at `1` -/
protected lemma LeftContinuity.Arccos_1
  : isLeftContinuousAt Arccos 1
:= by
  refine ⟨by norm_num [Arccos], ?_⟩
  have h_arcsin_left := LeftContinuity.Arcsin_1.2
  refine ⟨h_arcsin_left.1, ?_⟩
  intro ε h_ε
  rcases h_arcsin_left.2 ε h_ε with ⟨δ, hδ, hlim⟩
  exists δ with hδ
  intro x h_x
  have h_arcsin_nbho := hlim x h_x
  rw [Nbho_abs] at h_arcsin_nbho ⊢
  change |arccos x - arccos 1| < ε
  rw [arccos_eq_pi_div_two_sub_arcsin,
    arccos_eq_pi_div_two_sub_arcsin]
  have heq : π / 2 - arcsin x - (π / 2 - arcsin 1) =
      -(arcsin x - arcsin 1) := by ring
  rw [heq, abs_neg]
  change |arcsin x - arcsin 1| < ε
  exact h_arcsin_nbho

/-- Arc-Tangent Function's Continuity -/
protected lemma Continuity.Arctan
  : isContinuous Arctan
:= by
  intro x₀ _
  let α := arctan x₀
  have hα : α ∈ Ioo (-(π / 2)) (π / 2) := by
    simpa [α] using arctan_mem_Ioo x₀
  prove_continuity
  · exists 1 with zero_lt_one
    exact subset_univ _
  · intro ε h_ε
    let η := min (ε / 2)
      (min ((α + π / 2) / 2) ((π / 2 - α) / 2))
    have hη : 0 < η := lt_min (half_pos h_ε)
      (lt_min (by linarith [hα.1]) (by linarith [hα.2]))
    have hη_left : η ≤ (α + π / 2) / 2 := calc
      η ≤ min ((α + π / 2) / 2) ((π / 2 - α) / 2) := min_le_right _ _
      _ ≤ (α + π / 2) / 2 := min_le_left _ _
    have hη_right : η ≤ (π / 2 - α) / 2 := calc
      η ≤ min ((α + π / 2) / 2) ((π / 2 - α) / 2) := min_le_right _ _
      _ ≤ (π / 2 - α) / 2 := min_le_right _ _
    have hlo : -(π / 2) < α - η := by linarith
    have hhi : α + η < π / 2 := by linarith
    have htanlo : tan (α - η) < x₀ := by
      rw [← tan_arctan x₀]
      exact tan_lt_tan_of_lt_of_lt_pi_div_two hlo hα.2 (by linarith)
    have htanhi : x₀ < tan (α + η) := by
      rw [← tan_arctan x₀]
      exact tan_lt_tan_of_lt_of_lt_pi_div_two hα.1 hhi (by linarith)
    let δ := min (x₀ - tan (α - η)) (tan (α + η) - x₀)
    have hδ : 0 < δ := lt_min (sub_pos.mpr htanlo) (sub_pos.mpr htanhi)
    exists δ with hδ
    intro x h_x
    have h_dist_δ : |x - x₀| < δ := infer
      x ∈ Nbhd x₀ δ ⇒ x ∈ Nbho x₀ δ
                      := Nbhd_subset_Nbho h_x
      _             ⇒ |x - x₀| < δ
                      := (Nbho_abs x).mp ?_
    rw [abs_lt] at h_dist_δ
    have h_xlo : tan (α - η) < x := by
      linarith [min_le_left (x₀ - tan (α - η)) (tan (α + η) - x₀)]
    have h_xhi : x < tan (α + η) := by
      linarith [min_le_right (x₀ - tan (α - η)) (tan (α + η) - x₀)]
    have harclo : α - η < arctan x := by
      rw [← arctan_tan hlo (by linarith)]
      exact (arctan_lt_arctan_iff).2 h_xlo
    have harchi : arctan x < α + η := by
      rw [← arctan_tan (by linarith) hhi]
      exact (arctan_lt_arctan_iff).2 h_xhi
    change |arctan x - arctan x₀| < ε
    rw [abs_lt]
    have hηε : η < ε := calc
      η ≤ ε / 2 := min_le_left _ _
      _ < ε     := half_lt_self h_ε
    constructor <;> linarith

/-- Arc-Cotangent Function's Continuity -/
protected lemma Continuity.Arccot
  : isContinuous Arccot
:= by
  intro x₀ _
  have hc : isContinuousAt (Constant (π / 2)) x₀ :=
    Continuity.Constant _ (mem_univ _)
  have hsub : isContinuousAt (Constant (π / 2) - Arctan) x₀ :=
    Sub hc (Continuity.Arctan x₀ (mem_univ _))
  rw [← Arccot_eq]
  exact hsub

/-- Arc-Secant Function's Continuity for `x < -1 ∨ x > 1` -/
protected lemma Continuity.Arcsec
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arcsec x
:= by
  intro x₀ h_x₀
  rcases h_x₀ with h_x₀ | h_x₀
  · change x₀ < -1 at h_x₀
    have h_x₀_ne : x₀ ≠ 0 := by linarith
    have hcomp : isContinuousAt (Arccos ⊙ Identity⁻¹) x₀ :=
      infer
              isContinuousAt Identity x₀
           => isContinuousAt Identity⁻¹ x₀
              := ⟨⟨(Continuity.Identity x₀ (mem_univ _)).1, h_x₀_ne⟩,
            FuncLimit.Inv h_x₀_ne (Continuity.Identity x₀ (mem_univ _)).2⟩
        _  => isContinuousAt (Arccos ⊙ Identity⁻¹) x₀
              := Comp (Continuity.Arccos x₀⁻¹ (inv_mem_Ioo_of_lt_neg_one h_x₀)) ?_
    rw [← Arcsec_eq]
    exact hcomp
  · change 1 < x₀ at h_x₀
    have h_x₀_ne : x₀ ≠ 0 := by linarith
    have hcomp : isContinuousAt (Arccos ⊙ Identity⁻¹) x₀ :=
      infer
              isContinuousAt Identity x₀
           => isContinuousAt Identity⁻¹ x₀
              := ⟨⟨(Continuity.Identity x₀ (mem_univ _)).1, h_x₀_ne⟩,
              FuncLimit.Inv h_x₀_ne (Continuity.Identity x₀ (mem_univ _)).2⟩
        _  => isContinuousAt (Arccos ⊙ Identity⁻¹) x₀
              := Comp (Continuity.Arccos x₀⁻¹ (inv_mem_Ioo_of_one_lt h_x₀)) ?_
    rw [← Arcsec_eq]
    exact hcomp

/-- Arc-Secant Function's Left Continuity at `-1` -/
protected lemma LeftContinuity.Arcsec_neg1
  : isLeftContinuousAt Arcsec (-1)
:= by
  refine ⟨by norm_num [Arcsec], ?_⟩
  have h_arccos_right := RightContinuity.Arccos_neg1.2
  constructor
  · exists 1 with zero_lt_one
    intro x h_x
    left
    exact h_x.2.le
  · intro ε h_ε
    rcases h_arccos_right.2 ε h_ε with ⟨η, hη, hlim⟩
    let δ := min 1 η
    have hδ : 0 < δ := lt_min zero_lt_one hη
    exists δ with hδ
    intro x h_x
    have h_xneg : x < 0 := by linarith [h_x.2]
    have h_xinv_lo : -1 < x⁻¹ := by
      have hinvneg : x⁻¹ < 0 := inv_neg''.mpr h_xneg
      have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      nlinarith [h_x.2]
    have h_xinv_hi : x⁻¹ < -1 + η := by
      have hinvneg : x⁻¹ < 0 := inv_neg''.mpr h_xneg
      have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      have hsmall : -(x + 1) < η := by
        norm_num at h_x
        linarith [min_le_right 1 η]
      nlinarith [h_x.2]
    simpa [Arcsec, arcsec, Arccos] using hlim x⁻¹ ⟨h_xinv_lo, h_xinv_hi⟩

/-- Arc-Secant Function's Right Continuity at `1` -/
protected lemma RightContinuity.Arcsec_1
  : isRightContinuousAt Arcsec 1
:= by
  refine ⟨by norm_num [Arcsec], ?_⟩
  have h_arccos_left := LeftContinuity.Arccos_1.2
  constructor
  · exists 1 with zero_lt_one
    intro x h_x
    right
    exact h_x.1.le
  · intro ε h_ε
    rcases h_arccos_left.2 ε h_ε with ⟨η, hη, hlim⟩
    let δ := min 1 η
    have hδ : δ > 0 := by positivity
    exists δ with hδ
    intro x h_x
    have h_xpos : x > 0 := by linarith [h_x.1]
    have hinvpos : 0 < x⁻¹ := inv_pos.mpr h_xpos
    have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
    have h_xinv_hi : x⁻¹ < 1 := by nlinarith [h_x.1]
    have h_xinv_lo : 1 - η < x⁻¹ := by
      have hsmall : x - 1 < η := by
        norm_num at h_x
        linarith [min_le_right 1 η]
      nlinarith [h_x.1]
    simpa [Arcsec, arcsec, Arccos] using hlim x⁻¹ ⟨h_xinv_lo, h_xinv_hi⟩

/-- Arc-Cosecant Function's Continuity for `x < -1 ∨ x > 1` -/
protected lemma Continuity.Arccsc
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arccsc x
:= by
  intro x₀ h_x₀
  rcases h_x₀ with h_x₀ | h_x₀
  · change x₀ < -1 at h_x₀
    have h_x₀_ne : x₀ ≠ 0 := by linarith
    have hcomp : isContinuousAt (Arcsin ⊙ Identity⁻¹) x₀ :=
      infer
              isContinuousAt Identity x₀
           => isContinuousAt Identity⁻¹ x₀
              := ⟨⟨(Continuity.Identity x₀ (mem_univ _)).1, h_x₀_ne⟩,
            FuncLimit.Inv h_x₀_ne (Continuity.Identity x₀ (mem_univ _)).2⟩
        _  => isContinuousAt (Arcsin ⊙ Identity⁻¹) x₀
              := Comp (Continuity.Arcsin x₀⁻¹ (inv_mem_Ioo_of_lt_neg_one h_x₀)) ?_
    rw [← Arccsc_eq]
    exact hcomp
  · change 1 < x₀ at h_x₀
    have h_x₀_ne : x₀ ≠ 0 := by linarith
    have hcomp : isContinuousAt (Arcsin ⊙ Identity⁻¹) x₀ :=
      infer
              isContinuousAt Identity x₀
           => isContinuousAt Identity⁻¹ x₀
              := ⟨⟨(Continuity.Identity x₀ (mem_univ _)).1, h_x₀_ne⟩,
            FuncLimit.Inv h_x₀_ne (Continuity.Identity x₀ (mem_univ _)).2⟩
        _  => isContinuousAt (Arcsin ⊙ Identity⁻¹) x₀
              := Comp (Continuity.Arcsin x₀⁻¹ (inv_mem_Ioo_of_one_lt h_x₀)) ?_
    rw [← Arccsc_eq]
    exact hcomp

/-- Arc-Cosecant Function's Left Continuity at `-1` -/
protected lemma LeftContinuity.Arccsc_neg1
  : isLeftContinuousAt Arccsc (-1)
:= by
  refine ⟨by norm_num [Arccsc], ?_⟩
  have h_arcsin_right := RightContinuity.Arcsin_neg1.2
  constructor
  · exists 1 with zero_lt_one
    intro x h_x
    change x ≤ -1 ∨ 1 ≤ x
    left
    exact h_x.2.le
  · intro ε h_ε
    rcases h_arcsin_right.2 ε h_ε with ⟨η, hη, hlim⟩
    let δ := min 1 η
    have hδ : 0 < δ := lt_min zero_lt_one hη
    exists δ with hδ
    intro x h_x
    have h_xneg : x < 0 := by linarith [h_x.2]
    have h_xinv_lo : -1 < x⁻¹ := by
      have hinvneg : x⁻¹ < 0 := inv_neg''.mpr h_xneg
      have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      nlinarith [h_x.2]
    have h_xinv_hi : x⁻¹ < -1 + η := by
      have hinvneg : x⁻¹ < 0 := inv_neg''.mpr h_xneg
      have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      have hsmall : -(x + 1) < η := by
        norm_num at h_x
        linarith [min_le_right 1 η]
      nlinarith
    simpa [Arccsc, arccsc, Arcsin] using hlim x⁻¹ ⟨h_xinv_lo, h_xinv_hi⟩

/-- Arc-Cosecant Function's Right Continuity at `1` -/
protected lemma RightContinuity.Arccsc_1
  : isRightContinuousAt Arccsc 1
:= by
  refine ⟨by norm_num [Arccsc], ?_⟩
  have h_arcsin_left := LeftContinuity.Arcsin_1.2
  constructor
  · exists 1 with zero_lt_one
    intro x h_x
    right
    exact h_x.1.le
  · intro ε h_ε
    rcases h_arcsin_left.2 ε h_ε with ⟨η, hη, hlim⟩
    let δ := min 1 η
    have hδ : 0 < δ := lt_min zero_lt_one hη
    exists δ with hδ
    intro x h_x
    have h_xpos : 0 < x := by linarith [h_x.1]
    have hinvpos : 0 < x⁻¹ := inv_pos.mpr h_xpos
    have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
    have h_xinv_hi : x⁻¹ < 1 := by nlinarith [h_x.1]
    have h_xinv_lo : 1 - η < x⁻¹ := by
      have hsmall : x - 1 < η := by
        norm_num at h_x
        linarith [min_le_right 1 η]
      nlinarith [h_x.1]
    simpa [Arccsc, arccsc, Arcsin] using hlim x⁻¹ ⟨h_xinv_lo, h_xinv_hi⟩


page_end
