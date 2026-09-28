/-
    «Calculus_21».Differential.Elementary
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Rules
import «Calculus_21».Limit.Tactics.Equiv
import «Calculus_21».Limit.Tactics.Subst
set_option linter.style.header false

open LimitValue (finite_neg finite_add finite_sub finite_mul finite_div)


/-! # Elementary Functions' Derivatives -/

section
variable {n : ℤ} {C a x₀ : ℝ}

/-- Constant Function's Derivative (Expression) -/
theorem DerivExpr.Constant
  : D (const C) x₀ =. the 0
:= script
  calc
    _  =  lim x₀ fun x ↦ (C - C) / (x - x₀)
          := rfl
    _  =  lim x₀ fun _ ↦ 0
          := by
            lim_congr 1
            simp only [sub_self, zero_div]
    _  =  the 0
          := by lim_cont
  rfl

/-- Constant Function's Derivative -/
theorem Deriv.Constant
  : ∀ x, Deriv (Constant C) x 0
:= by
  intro x
  --infer
  --  D f x₀ =. the D₁ => Deriv (Constant C) x 0
  --                      :=
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Constant

/-- Constant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Constant
  : D₋ (const C) x₀ =. the 0
:= DerivExpr.toLeft <| DerivExpr.Constant

/-- Constant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Constant
  : D₊ (const C) x₀ =. the 0
:= DerivExpr.toRight <| DerivExpr.Constant

/-- Identity Function's Derivative (Expression) -/
theorem DerivExpr.Identity
  : D id x₀ =. the 1
:= script
  calc
    _  =  lim x₀ fun x ↦ (x - x₀) / (x - x₀)
          := rfl
    _  =  lim x₀ fun _ ↦ 1
          := by
            lim_congr 1
            apply div_self
            positivity
    _  =  the 1
          := by lim_cont
  rfl

/-- Identity Function's Derivative -/
theorem Deriv.Identity
  : ∀ x, Deriv Identity x 1
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Identity

/-- Identity Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Identity
  : D₋ id x₀ =. the 1
:= DerivExpr.toLeft <| DerivExpr.Identity

/-- Identity Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Identity
  : D₊ id x₀ =. the 1
:= DerivExpr.toRight <| DerivExpr.Identity

/-- Absolute Value Function's Derivative (Expression) -/
theorem DerivExpr.Abs
    (h_dom : x₀ ≠ 0)
  : D abs x₀ =. the (x₀ / |x₀|)
:= by
  have h := lt_or_gt_of_ne h_dom
  script_cases_by h
  case left =>
    calc
      _  =  lim x₀ fun _ ↦ -1
            := by
              lim_congr -x₀
              rename_i x _ _ hne
              have hx : x < 0 := by linarith
              rw [abs_of_neg hx, abs_of_neg hp]
              field [sub_ne_zero.mpr hne]
      _  =  the (-1)
            := by lim_cont
      _  =  the (x₀ / |x₀|)
            := by
              rw [abs_of_neg hp]
              congr
              field_simp
    rfl
  case right =>
    calc
      _  =  lim x₀ fun _ ↦ 1
            := by
              lim_congr x₀
              rename_i x _ _ hne
              have hx : x > 0 := by linarith
              rw [abs_of_pos hx, abs_of_pos hq, div_self (sub_ne_zero.mpr hne)]
      _  =  the 1
            := by lim_cont
      _  =  the (x₀ / |x₀|)
            := by
              rw [abs_of_pos hq]
              congr
              field_simp
    rfl

/-- Absolute Value Function's Derivative -/
theorem Deriv.Abs
  : ∀ x ≠ 0, Deriv Abs x (x / |x|)
:= by
  intro x h_x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Abs h_x

/-- Absolute Value Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Abs
    (h_dom : x₀ ≠ 0)
  : D₋ abs x₀ =. the (x₀ / |x₀|)
:= DerivExpr.toLeft <| DerivExpr.Abs h_dom

/-- Absolute Value Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Abs
    (h_dom : x₀ ≠ 0)
  : D₊ abs x₀ =. the (x₀ / |x₀|)
:= DerivExpr.toRight <| DerivExpr.Abs h_dom

/-- Square Root Function's Derivative (Expression) -/
theorem DerivExpr.Sqrt
    (h_dom : x₀ > 0)
  : D sqrt x₀ =. the (1 / (2 * √x₀))
:= script
  calc
    _  =  lim x₀ fun x ↦ (√x - √x₀) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ 1 / (√x + √x₀)
          := by
            lim_congr x₀
            rename_i x _ _ _
            have hx : x > 0 := by linarith
            rw [div_eq_div_iff]
            · linarith [Real.sq_sqrt hx.le, Real.sq_sqrt h_dom.le]
            · positivity
            · positivity
    _  =  the (1 / (√x₀ + √x₀))
          := by lim_cont
    _  =  the (1 / (2 * √x₀))
          := by congr 2; ring
  rfl

/-- Square Root Function's Derivative -/
theorem Deriv.Sqrt
  : ∀ x > 0, Deriv Sqrt x (1 / (2 * √x))
:= by
  intro x h_x
  apply Deriv.fromDerivExpr
  · script_exists x / 2 with by positivity
    intro a h_a
    simp only [mem_Ici, mem_Nbhd] at h_a ⊢
    linarith
  · exact DerivExpr.Sqrt h_x

/-- Square Root Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sqrt
    (h_dom : x₀ > 0)
  : D₋ sqrt x₀ =. the (1 / (2 * √x₀))
:= DerivExpr.toLeft <| DerivExpr.Sqrt h_dom

/-- Square Root Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sqrt
    (h_dom : x₀ > 0)
  : D₊ sqrt x₀ =. the (1 / (2 * √x₀))
:= DerivExpr.toRight <| DerivExpr.Sqrt h_dom

/-- Power Function's Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 =. 1` will be used if `n =. 1 ∧ x₀ =. 0`. -/
theorem DerivExpr.Power_ℤ
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D (npow n) x₀ =. the (n * x₀ ^ (n - 1))
:= by
  have hnat : ∀ m : ℕ, D (fun x : ℝ => x ^ m) x₀ =. the (m * x₀ ^ (m - 1)) := by
    intro m
    script_given_proper
    calc
      _  =? the m * D id x₀ * the (x₀ ^ (m - 1))
            := MSPow
      _  =  the (m * x₀ ^ (m - 1))
            := by
              poly_rw [DerivExpr.Identity]
              simp only [finite_mul, mul_one]
  cases n with
  | ofNat m =>
    cases m with
    | zero =>
      have heq : npow (Int.ofNat 0) = const 1 := by funext x; simp [npow, const]
      rw [heq]
      convert (DerivExpr.Constant) using 1
      norm_num
    | succ m =>
      change D (fun x ↦ x ^ (↑(m + 1) : ℤ)) x₀ =. the _
      simp only [zpow_natCast]
      simpa [npow, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        show (m + 1) - 1 = m by omega] using hnat (m + 1)
  | negSucc m =>
    have hp : x₀ ^ (m + 1) ≠ 0 := pow_ne_zero _ (h_dom.resolve_left (by omega))
    script_given_proper
    calc
      _ = D ((fun x ↦ x ^ (m + 1))⁻¹) x₀ := by
        rfl
      _ =? -D (fun x ↦ x ^ (m + 1)) x₀ / the ((x₀ ^ (m + 1)) ^ 2) := Inv
      _ =. the (-(↑(m + 1) * x₀ ^ m) / (x₀ ^ (m + 1)) ^ 2) := by
        poly_rw [hnat (m + 1)]
        simpa only [Nat.add_sub_cancel, finite_neg] using
          (finite_div (a := -(↑(m + 1) * x₀ ^ m)) (pow_ne_zero 2 hp))
      _ = the ((Int.negSucc m) * x₀ ^ (Int.negSucc m - 1)) := by
        congr 1
        rw [show Int.negSucc m - 1 = Int.negSucc (m + 1) by omega, zpow_negSucc]
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp

/-- Power Function's Derivative for `n : ℤ`
    - Junk value `0 ^ 0 =. 1` will be used if `n =. 1 ∧ x =. 0`. -/
theorem Deriv.Power_ℤ
  : ∀ x ∈ { x : ℝ | n > 0 ∨ x ≠ 0 }, Deriv (NPower n) x (n * x ^ (n - 1))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · rcases hx with hn | hx
    · change ∃ δ > 0, Nbhd x δ ⊆ (NPower n).domain
      rw [NPower, if_pos hn]
      exact ⟨1, zero_lt_one, by simp⟩
    · change ∃ δ > 0, Nbhd x δ ⊆ (NPower n).domain
      unfold NPower
      split_ifs with hn
      · exact ⟨1, zero_lt_one, by simp⟩
      · refine ⟨|x| / 2, by positivity, ?_⟩
        intro y hy
        change y ≠ 0
        intro hy0
        simp only [mem_Nbhd] at hy
        rcases hy with ⟨hlo, hhi, _⟩
        rw [hy0] at hlo hhi
        rcases lt_or_gt_of_ne hx with h | h
        · rw [abs_of_neg h] at hlo hhi
          linarith
        · rw [abs_of_pos h] at hlo hhi
          linarith
  · convert DerivExpr.Power_ℤ hx using 1
    change D (if n > 0 then (⟨npow n, Iii⟩ : RFunction)
      else ⟨npow n, {x : ℝ | x ≠ 0}⟩).map x = D (npow n) x
    split_ifs <;> rfl

/-- Power Function's Left Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 =. 1` will be used if `n =. 1 ∧ x₀ =. 0`. -/
theorem LeftDerivExpr.Power_ℤ
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₋ (npow n) x₀ =. the (n * x₀ ^ (n - 1))
:= DerivExpr.toLeft <| DerivExpr.Power_ℤ h_dom

/-- Power Function's Right Derivative for `n : ℤ` (Expression)
    - Junk value `0 ^ 0 =. 1` will be used if `n =. 1 ∧ x₀ =. 0`. -/
theorem RightDerivExpr.Power_ℤ
    (h_dom : n > 0 ∨ x₀ ≠ 0)
  : D₊ (npow n) x₀ =. the (n * x₀ ^ (n - 1))
:= DerivExpr.toRight <| DerivExpr.Power_ℤ h_dom

/-- Natural Exponential Function's Derivative (Expression) -/
theorem DerivExpr.Exp
  : D exp x₀ =. the (exp x₀)
:= script
  calc
    _  =  lim x₀ fun x ↦ (exp x - exp x₀) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ exp x₀ * ((exp (x - x₀) - 1) / (x - x₀))
          := by
            lim_congr 1
            rw [← mul_div_assoc, mul_sub, mul_one, ← Real.exp_add, add_sub_cancel]
    _  =. the (exp x₀) * (lim x₀ fun x ↦ (exp (x - x₀) - 1) / (x - x₀))
          := by lim_smul
    _  =  the (exp x₀) * (lim x₀ fun x ↦ (x - x₀) / (x - x₀))
          := by lim_equiv
    _  =  the (exp x₀) * (lim x₀ fun _ ↦ 1)
          := by lim_congr 1; field
    _  =  the (exp x₀)
          := by lim_cont

/-- Natural Exponential Function's Derivative -/
theorem Deriv.Exp
  : ∀ x, Deriv Exp x (exp x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Exp

/-- Natural Exponential Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Exp
  : D₋ exp x₀ =. the (exp x₀)
:= DerivExpr.toLeft <| DerivExpr.Exp

/-- Natural Exponential Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Exp
  : D₊ exp x₀ =. the (exp x₀)
:= DerivExpr.toRight <| DerivExpr.Exp

/-- Exponential Function's Derivative (Expression) -/
theorem DerivExpr.Expow
    (h_dom : a > 0)
  : D (a ^ ·) x₀ =. the (ln a * a ^ x₀)
:= script
  given_proper
  calc
    _  =  D (exp ∘ ((ln a) • id)) x₀
          := by
            congr 1
            funext x
            exact Real.rpow_def_of_pos h_dom x
    _  =? D exp (((ln a) • id) x₀) * D ((ln a) • id) x₀
          := Comp
    _  =. D exp (((ln a) • id) x₀) * (the (ln a) * D id x₀)
          := by
            gcongr
            exact SMul
    _  =. the (ln a * a ^ x₀)
          := by
            poly_rw [DerivExpr.Exp, DerivExpr.Identity]
            simp only [finite_mul, Pi.smul_apply, smul_eq_mul, id_eq, mul_one]
            rw [Real.rpow_def_of_pos h_dom]
            simp only [ln, mul_comm]
            rfl

/-- Exponential Function's Derivative -/
theorem Deriv.Expow
    (h_a : a > 0)
  : ∀ x, Deriv (Expow a) x (ln a * a ^ x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Expow h_a

/-- Exponential Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Expow
    (h_dom : a > 0)
  : D₋ (a ^ ·) x₀ =. the (ln a * a ^ x₀)
:= DerivExpr.toLeft <| DerivExpr.Expow h_dom

/-- Exponential Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Expow
    (h_dom : a > 0)
  : D₊ (a ^ ·) x₀ =. the (ln a * a ^ x₀)
:= DerivExpr.toRight <| DerivExpr.Expow h_dom

/-- Natural Logarithm Function's Derivative (Expression) -/
theorem DerivExpr.Ln
    (h_dom : x₀ > 0)
  : D ln x₀ =. the x₀⁻¹
:= script
  given_proper
  calc
    _  =  lim x₀ fun x ↦ (ln x - ln x₀) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ ln (1 + (x - x₀) / x₀) / (x - x₀)
          := by
            lim_congr x₀ / 2
            rename_i x _ _ _
            have hx : x > 0 := by linarith
            recover_form
            rw [← Real.log_div hx.ne' h_dom.ne']
            congr
            field
    _  =? Lim (lim x₀ fun x ↦ x - x₀) fun u ↦ ln (1 + u / x₀) / u
          := by lim_subst
    _  =  lim 0 fun u ↦ ln (1 + u / x₀) / u
          := by
            rw [show (lim x₀ fun x ↦ x - x₀) = the 0 by lim_cont]
            simp only [LimitAtExpr.finite]
    _  =  lim 0 fun u ↦ x₀⁻¹ * ln (1 + u / x₀) / (u / x₀)
          := by lim_congr 1; field
    _  =  lim 0 fun u ↦ x₀⁻¹ * (u / x₀) / (u / x₀)
          := by lim_equiv
    _  =  lim 0 fun u ↦ x₀⁻¹
          := by lim_congr 1; field
    _  =  the x₀⁻¹
          := by lim_cont

/-- Natural Logarithm Function's Derivative -/
theorem Deriv.Ln
  : ∀ x > 0, Deriv Ln x x⁻¹
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists x / 2 with by positivity
    intro a h_a
    simp only [mem_Ioi, mem_Nbhd] at h_a ⊢
    linarith
  · exact DerivExpr.Ln hx

/-- Natural Logarithm Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Ln
    (h_dom : x₀ > 0)
  : D₋ ln x₀ =. the x₀⁻¹
:= DerivExpr.toLeft <| DerivExpr.Ln h_dom

/-- Natural Logarithm Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Ln
    (h_dom : x₀ > 0)
  : D₊ ln x₀ =. the x₀⁻¹
:= DerivExpr.toRight <| DerivExpr.Ln h_dom

/-- Power Function's Derivative (Expression) -/
theorem DerivExpr.Power
    (h_dom : x₀ > 0)
  : D (pow a) x₀ =. the (a * x₀ ^ (a - 1))
:= script
  given_proper
  calc
    _  =  D (fun x ↦ exp (a * ln x)) x₀
          := by
            lim_congr x₀
            rename_i x _ _ _
            have hx : x > 0 := by linarith
            change (x ^ a - x₀ ^ a) / (x - x₀)
              = (exp (a * Real.log x) - exp (a * Real.log x₀)) / (x - x₀)
            simp only [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos h_dom, mul_comm a]
    _  =? D exp ((a • ln) x₀) * D (a • ln) x₀
          := Comp
    _  =. D exp ((a • ln) x₀) * (the a * D ln x₀)
          := by
            gcongr
            exact SMul
    _  =  the (exp (a * ln x₀) * (a * x₀⁻¹))
          := by poly_rw [DerivExpr.Exp, DerivExpr.Ln h_dom]
    _  =  the (a * x₀ ^ (a - 1))
          := by
            apply congrArg the
            rw [Real.rpow_sub h_dom, Real.rpow_one, Real.rpow_def_of_pos h_dom]
            simp only [ln, div_eq_mul_inv, mul_comm, mul_assoc]

/-- Power Function's Derivative for `x > 0` -/
protected theorem Deriv.Power
  : ∀ x > 0, Deriv (Power a) x (a * x ^ (a - 1))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · refine ⟨x / 2, by positivity, ?_⟩
    intro y hy
    simp only [mem_Nbhd] at hy
    have hypos : 0 < y := by linarith [hy.1]
    change y ∈ (if a > 0 then (⟨pow a, Ici 0⟩ : RFunction)
      else ⟨pow a, Ioi 0⟩).domain
    split_ifs
    · exact hypos.le
    · exact hypos
  · convert DerivExpr.Power hx using 1
    change D (if a > 0 then (⟨pow a, Ici 0⟩ : RFunction)
      else ⟨pow a, Ioi 0⟩).map x = D (pow a) x
    split_ifs <;> rfl

/-- Power Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Power
    (h_dom : x₀ > 0)
  : D₋ (pow a) x₀ =. the (a * x₀ ^ (a - 1))
:= DerivExpr.toLeft <| DerivExpr.Power h_dom

/-- Power Function's Right Derivative (Expression)
    - Junk value `0 ^ 0 =. 1` will be used if `a =. 1 ∧ x₀ =. 0`. -/
theorem RightDerivExpr.Power
    (h_dom : x₀ > 0 ∨ (a ≥ 1 ∧ x₀ = 0))
  : D₊ (pow a) x₀ =. the (a * x₀ ^ (a - 1))
:= by
  rcases h_dom with hx | ⟨ha, hx⟩
  · exact DerivExpr.toRight <| DerivExpr.Power hx
  subst x₀
  by_cases h : a = 1
  · subst a
    change D₊ (fun x : ℝ ↦ x ^ (1 : ℝ)) 0 =. the (1 * (0 : ℝ) ^ (1 - 1))
    have heq : (fun x : ℝ ↦ x ^ (1 : ℝ)) = id := by
      funext x
      exact Real.rpow_one x
    rw [heq]
    simpa using (RightDerivExpr.Identity (x₀ := 0))
  · have ha' : 1 < a := lt_of_le_of_ne ha (Ne.symm h)
    calc
      _ = lim₊ 0 (fun x : ℝ ↦ x ^ (a - 1)) := by
        unfold RightDerivExpr
        apply RightLimitExpr.Congr
        refine ⟨1, zero_lt_one, ?_⟩
        intro x hx
        have hxpos : 0 < x := hx.1
        change (x ^ a - (0 : ℝ) ^ a) / (x - 0) = x ^ (a - 1)
        rw [Real.zero_rpow (ne_of_gt (by linarith : 0 < a))]
        simp only [sub_zero]
        rw [Real.rpow_sub hxpos, Real.rpow_one]
      _ =. the ((0 : ℝ) ^ (a - 1)) := by
        exact RightLimitExpr.Power (Or.inr ⟨by linarith, rfl⟩)
      _ = the (a * (0 : ℝ) ^ (a - 1)) := by
        rw [Real.zero_rpow (ne_of_gt (sub_pos.mpr ha'))]
        simp

/-- Power Function's Right Derivative at `0` -/
theorem RightDeriv.Power_0
    (h_a : a > 1)
  : RightDeriv (Power a) 0 0
:= by
  apply RightDeriv.fromRightDerivExpr
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    change x ∈ (Power a).domain
    rw [Power, if_pos (by linarith : a > 0)]
    exact le_of_lt hx.1
  · convert RightDerivExpr.Power (Or.inr ⟨by linarith, rfl⟩) using 1
    · change D₊ (if a > 0 then (⟨pow a, Ici 0⟩ : RFunction)
        else ⟨pow a, Ioi 0⟩).map 0 = D₊ (pow a) 0
      rw [if_pos (by linarith : a > 0)]
    · simp only [Real.zero_rpow (ne_of_gt (sub_pos.mpr h_a)), mul_zero]

/-- Logarithm Function's Derivative (Expression) -/
theorem DerivExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D (log a) x₀ =. the (ln a * x₀)⁻¹
:= script
  calc
    _  =  D (fun x ↦ (ln a)⁻¹ * ln x) x₀
          := by
            congr
            funext x
            simp only [ln, log, div_eq_mul_inv, mul_comm]
    _  =. the (ln a)⁻¹ * D ln x₀
          := SMul
    _  =. the (ln a)⁻¹ * the x₀⁻¹
          := by poly_rw [DerivExpr.Ln h_dom.1]
    _  =  the (ln a * x₀)⁻¹
          := by simp only [finite_mul]; ring_nf

/-- Logarithm Function's Derivative -/
theorem Deriv.Log
    (h_a : a > 0 ∧ a ≠ 1)
  : ∀ x > 0, Deriv (Log a) x (ln a * x)⁻¹
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists x / 2 with by positivity
    intro a h_a
    simp only [mem_Ioi, mem_Nbhd] at h_a ⊢
    linarith
  · exact DerivExpr.Log ⟨hx, h_a⟩

/-- Logarithm Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₋ (log a) x₀ =. the (ln a * x₀)⁻¹
:= DerivExpr.toLeft <| DerivExpr.Log h_dom

/-- Logarithm Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Log
    (h_dom : x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
  : D₊ (log a) x₀ =. the (ln a * x₀)⁻¹
:= DerivExpr.toRight <| DerivExpr.Log h_dom

/-- Sine Function's Derivative (Expression) -/
theorem DerivExpr.Sin
  : D sin x₀ =. the (cos x₀)
:= script
  calc
    _  =  lim x₀ fun x ↦ (sin ((x - x₀) / 2) / ((x - x₀) / 2))
            * cos ((x + x₀) / 2)
          := by
            unfold DerivExpr
            lim_congr 1
            rw [Real.sin_sub_sin]
            field
    _  =. lim x₀ (fun x ↦ sin ((x - x₀) / 2) / ((x - x₀) / 2))
            * lim x₀ (fun x ↦ cos ((x + x₀) / 2))
          := by lim_mul
    _  =  lim x₀ (fun x ↦ ((x - x₀) / 2) / ((x - x₀) / 2))
            * lim x₀ (fun x ↦ cos ((x + x₀) / 2))
          := by lim_equiv
    _  =  lim x₀ (fun _ ↦ 1) * lim x₀ (fun x ↦ cos ((x + x₀) / 2))
          := by lim_congr 1; field
    _  =  the (cos x₀)
          := by lim_cont

/-- Sine Function's Derivative -/
theorem Deriv.Sin
  : ∀ x, Deriv Sin x (cos x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Sin

/-- Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sin
  : D₋ sin x₀ =. the (cos x₀)
:= DerivExpr.toLeft <| DerivExpr.Sin

/-- Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sin
  : D₊ sin x₀ =. the (cos x₀)
:= DerivExpr.toRight <| DerivExpr.Sin

/-- Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Cos
  : D cos x₀ =. the (- sin x₀)
:= by
  let a := x₀ + Real.pi / 2
  let q : ℝ → ℝ := fun u => if u = a then cos a else (sin u - sin a) / (u - a)
  have hq : lim a q =. the (q a) := by
    calc
      _ = D sin a := by
        unfold DerivExpr
        lim_congr 1
        simp only [q, if_neg (by assumption)]
      _ =. the (cos a) := DerivExpr.Sin
      _ = the (q a) := by simp only [q, ↓reduceIte]
  calc
    _ = lim x₀ (q ∘ (fun x ↦ x + Real.pi / 2)) := by
      unfold DerivExpr
      lim_congr 1
      rename_i x hlo hhi hne
      have hn : x + Real.pi / 2 ≠ a := by dsimp [a]; exact fun h => hne (add_right_cancel h)
      simp only [Function.comp_apply, q, if_neg hn, a, Real.sin_add_pi_div_two,
        add_sub_add_right_eq_sub]
    _ =. the (q a) := FuncLimitExpr.CompSV (by sorry /-lim_cont-/) hq
    _ = the (- sin x₀) := by simp only [q, ↓reduceIte, a, Real.cos_add_pi_div_two]

/-- Cosine Function's Derivative -/
theorem Deriv.Cos
  : ∀ x, Deriv Cos x (- sin x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Cos

/-- Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cos
  : D₋ cos x₀ =. the (- sin x₀)
:= DerivExpr.toLeft <| DerivExpr.Cos

/-- Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cos
  : D₊ cos x₀ =. the (- sin x₀)
:= DerivExpr.toRight <| DerivExpr.Cos

/-- Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : D tan x₀ =. the (sec x₀ ^ 2)
:= by
  script_given_proper
  calc
    _  =  D (sin / cos) x₀
          := by
            congr
            funext x
            exact Real.tan_eq_sin_div_cos x
    _  =? (D sin x₀ * the (cos x₀) - D cos x₀ * the (sin x₀))
            / the (cos x₀ ^ 2)
          := Div
    _  =  the ((cos x₀ * cos x₀ - (- sin x₀) * sin x₀) / cos x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Sin, DerivExpr.Cos]
            simp only [finite_mul, finite_sub]
            poly_rw [finite_div (pow_ne_zero 2 h_dom)]
    _  =  the (sec x₀ ^ 2)
          := by
            congr
            rw [sec, div_pow, one_pow]
            congr
            linarith [Real.sin_sq_add_cos_sq x₀]

/-- Tangent Function's Derivative -/
theorem Deriv.Tan
  : ∀ x ∈ Tan.domain, Deriv Tan x (sec x ^ 2)
:= by
  intro x hx
  change cos x ≠ 0 at hx
  apply Deriv.fromDerivExpr
  · refine ⟨|cos x| / 2, by positivity, ?_⟩
    intro y hy
    change cos y ≠ 0
    intro hzero
    have hdist : |y - x| < |cos x| / 2 := by
      exact (Nbho_abs _).mp (Nbhd_subset_Nbho hy)
    have hbound := Real.abs_cos_sub_cos_le y x
    rw [hzero, zero_sub, abs_neg] at hbound
    linarith [abs_pos.mpr hx]
  · exact DerivExpr.Tan hx

/-- Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : D₋ tan x₀ =. the (sec x₀ ^ 2)
:= DerivExpr.toLeft <| DerivExpr.Tan h_dom

/-- Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Tan
    (h_dom : cos x₀ ≠ 0)
  : D₊ tan x₀ =. the (sec x₀ ^ 2)
:= DerivExpr.toRight <| DerivExpr.Tan h_dom

/-- Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : D cot x₀ =. the (- csc x₀ ^ 2)
:= script
  given_proper
  calc
    _  =  D (cos / sin) x₀
          := by
            congr
            funext x
            exact Real.cot_eq_cos_div_sin x
    _  =? (D cos x₀ * the (sin x₀) - D sin x₀ * the (cos x₀))
            / the (sin x₀ ^ 2)
          := Div
    _  =  the (((- sin x₀) * sin x₀ - cos x₀ * cos x₀) / sin x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Cos, DerivExpr.Sin]
            simp only [finite_mul, finite_sub]
            poly_rw [finite_div (pow_ne_zero 2 h_dom)]
    _  =  the (- csc x₀ ^ 2)
          := by
            congr
            rw [csc, div_pow, one_pow, ← neg_div]
            congr
            linarith [Real.sin_sq_add_cos_sq x₀]

/-- Cotangent Function's Derivative -/
theorem Deriv.Cot
  : ∀ x ∈ Cot.domain, Deriv Cot x (- csc x ^ 2)
:= by
  intro x hx
  change sin x ≠ 0 at hx
  apply Deriv.fromDerivExpr
  · refine ⟨|sin x| / 2, by positivity, ?_⟩
    intro y hy
    change sin y ≠ 0
    intro hzero
    have hdist : |y - x| < |sin x| / 2 := by
      exact (Nbho_abs _).mp (Nbhd_subset_Nbho hy)
    have hbound := Real.abs_sin_sub_sin_le y x
    rw [hzero, zero_sub, abs_neg] at hbound
    linarith [abs_pos.mpr hx]
  · exact DerivExpr.Cot hx

/-- Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : D₋ cot x₀ =. the (- csc x₀ ^ 2)
:= DerivExpr.toLeft <| DerivExpr.Cot h_dom

/-- Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cot
    (h_dom : sin x₀ ≠ 0)
  : D₊ cot x₀ =. the (- csc x₀ ^ 2)
:= DerivExpr.toRight <| DerivExpr.Cot h_dom

/-- Secant Function's Derivative (Expression) -/
theorem DerivExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : D sec x₀ =. the (tan x₀ * sec x₀)
:= script
  given_proper
  calc
    _  =  D cos⁻¹ x₀
          := by
              congr
              funext x
              func_apply
              simp only [sec, one_div]
    _  =? - D cos x₀ / the (cos x₀ ^ 2)
          := Inv
    _  =  the (- (- sin x₀) / cos x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Cos]
            change the (- (- sin x₀)) / the (cos x₀ ^ 2) = _
            poly_rw [finite_div (pow_ne_zero 2 h_dom)]
    _  =  the (tan x₀ * sec x₀)
          := by
            simp only [Real.tan_eq_sin_div_cos, sec]
            ring_nf

/-- Secant Function's Derivative -/
theorem Deriv.Sec
  : ∀ x ∈ Sec.domain, Deriv Sec x (tan x * sec x)
:= by
  intro x hx
  change cos x ≠ 0 at hx
  apply Deriv.fromDerivExpr
  · refine ⟨|cos x| / 2, by positivity, ?_⟩
    intro y hy
    change cos y ≠ 0
    intro hzero
    have hdist : |y - x| < |cos x| / 2 := by
      exact (Nbho_abs _).mp (Nbhd_subset_Nbho hy)
    have hbound := Real.abs_cos_sub_cos_le y x
    rw [hzero, zero_sub, abs_neg] at hbound
    linarith [abs_pos.mpr hx]
  · exact DerivExpr.Sec hx

/-- Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : D₋ sec x₀ =. the (tan x₀ * sec x₀)
:= DerivExpr.toLeft <| DerivExpr.Sec h_dom

/-- Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sec
    (h_dom : cos x₀ ≠ 0)
  : D₊ sec x₀ =. the (tan x₀ * sec x₀)
:= DerivExpr.toRight <| DerivExpr.Sec h_dom

/-- Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : D csc x₀ =. the (- cot x₀ * csc x₀)
:= script
  given_proper
  calc
    _  =  D sin⁻¹ x₀
          := by
            congr
            funext x
            func_apply
            simp only [csc, one_div]
    _  =? - D sin x₀ / the (sin x₀ ^ 2)
          := Inv
    _  =  the (- cos x₀ / sin x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Sin]
            change the (- cos x₀) / the (sin x₀ ^ 2) = _
            poly_rw [finite_div (pow_ne_zero 2 h_dom)]
    _  =  the (- cot x₀ * csc x₀)
          := by
            simp only [Real.cot_eq_cos_div_sin, csc]
            ring_nf

/-- Cosecant Function's Derivative -/
theorem Deriv.Csc
  : ∀ x ∈ Csc.domain, Deriv Csc x (- cot x * csc x)
:= by
  intro x hx
  change sin x ≠ 0 at hx
  apply Deriv.fromDerivExpr
  · refine ⟨|sin x| / 2, by positivity, ?_⟩
    intro y hy
    change sin y ≠ 0
    intro hzero
    have hdist : |y - x| < |sin x| / 2 := by
      exact (Nbho_abs _).mp (Nbhd_subset_Nbho hy)
    have hbound := Real.abs_sin_sub_sin_le y x
    rw [hzero, zero_sub, abs_neg] at hbound
    linarith [abs_pos.mpr hx]
  · exact DerivExpr.Csc hx

/-- Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : D₋ csc x₀ =. the (- cot x₀ * csc x₀)
:= DerivExpr.toLeft <| DerivExpr.Csc h_dom

/-- Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Csc
    (h_dom : sin x₀ ≠ 0)
  : D₊ csc x₀ =. the (- cot x₀ * csc x₀)
:= DerivExpr.toRight <| DerivExpr.Csc h_dom

/-- Hyp-Sine Function's Derivative (Expression) -/
theorem DerivExpr.Sinh
  : D sinh x₀ =. the (cosh x₀)
:= by
  have hn : D (exp ∘ (-id)) x₀ =. the (-exp (-x₀)) := by
    script_given_proper
    calc
      _ =? D exp (-x₀) * D (-id) x₀ := DerivExpr.Comp
      _ =. D exp (-x₀) * (- D id x₀) := by
        gcongr
        exact DerivExpr.Neg
      _ = the (-exp (-x₀))
          := by
            poly_rw [DerivExpr.Exp, DerivExpr.Identity]
            change the (exp (-x₀) * (-1)) = the (-exp (-x₀))
            congr
            ring_nf
  calc
    _  =  D ((1 / 2) • (exp - exp ∘ (-id))) x₀
          := by
            congr
            funext x
            func_apply
            simp only [Real.sinh_eq, smul_eq_mul, id_eq]
            ring
    _  =. the (1 / 2) * D (exp - exp ∘ (-id)) x₀
          := SMul
    _  =. the (1 / 2) * (D exp x₀ - D (exp ∘ (-id)) x₀)
          := by
            gcongr
            exact Sub
    _  =  the (cosh x₀)
          := by
            poly_rw [DerivExpr.Exp, hn]
            change the ((1 / 2) * (exp x₀ - -exp (-x₀))) = the (cosh x₀)
            rw [Real.cosh_eq]
            ring_nf

/-- Hyp-Sine Function's Derivative -/
theorem Deriv.Sinh
  : ∀ x, Deriv Sinh x (cosh x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Sinh

/-- Hyp-Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sinh
  : D₋ sinh x₀ =. the (cosh x₀)
:= DerivExpr.toLeft <| DerivExpr.Sinh

/-- Hyp-Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sinh
  : D₊ sinh x₀ =. the (cosh x₀)
:= DerivExpr.toRight <| DerivExpr.Sinh

/-- Hyp-Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Cosh
  : D cosh x₀ =. the (sinh x₀)
:= by
  have hn : D (exp ∘ (-id)) x₀ =. the (-exp (-x₀)) := by
    script_given_proper
    calc
      _ =? D exp (-x₀) * D (-id) x₀ := DerivExpr.Comp
      _ =. D exp (-x₀) * (- D id x₀) := by
        gcongr
        exact DerivExpr.Neg
      _ = the (-exp (-x₀)) := by
        poly_rw [DerivExpr.Exp, DerivExpr.Identity]
        change the (exp (-x₀) * (-1)) = the (-exp (-x₀))
        congr 1; ring
  calc
    _ = D ((1 / 2) • (exp + exp ∘ (-id))) x₀ := by
      congr 1; funext x; simp only [Real.cosh_eq, Pi.smul_apply, smul_eq_mul,
        Pi.add_apply, Function.comp_apply, Pi.neg_apply, id_eq]; ring
    _ =. the (1 / 2) * D (exp + exp ∘ (-id)) x₀ := DerivExpr.SMul
    _ =. the (1 / 2) * (D exp x₀ + D (exp ∘ (-id)) x₀) := by
      gcongr
      exact DerivExpr.Add
    _ = the (sinh x₀) := by
      poly_rw [DerivExpr.Exp, hn]
      change the ((1 / 2) * (exp x₀ + -exp (-x₀))) = the (sinh x₀)
      congr 1; rw [Real.sinh_eq]; ring

/-- Hyp-Cosine Function's Derivative -/
theorem Deriv.Cosh
  : ∀ x, Deriv Cosh x (sinh x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Cosh

/-- Hyp-Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Cosh
  : D₋ cosh x₀ =. the (sinh x₀)
:= DerivExpr.toLeft <| DerivExpr.Cosh

/-- Hyp-Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Cosh
  : D₊ cosh x₀ =. the (sinh x₀)
:= DerivExpr.toRight <| DerivExpr.Cosh

/-- Hyp-Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Tanh
  : D tanh x₀ =. the (sech x₀ ^ 2)
:= script
  given_proper
  calc
    _  =  D (sinh / cosh) x₀
          := by
            congr
            funext x
            exact Real.tanh_eq_sinh_div_cosh x
    _  =? (D sinh x₀ * the (cosh x₀) - D cosh x₀ * the (sinh x₀)) / the (cosh x₀ ^ 2)
          := Div
    _  =  the ((cosh x₀ * cosh x₀ - sinh x₀ * sinh x₀) / cosh x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Sinh, DerivExpr.Cosh]
            simp only [finite_mul, finite_sub]
            poly_rw [finite_div (pow_ne_zero 2 (Real.cosh_pos x₀).ne')]
    _  =  the (sech x₀ ^ 2)
          := by
            congr
            rw [sech, div_pow, one_pow]
            congr
            linarith [Real.cosh_sq_sub_sinh_sq x₀]

/-- Hyp-Tangent Function's Derivative -/
theorem Deriv.Tanh
  : ∀ x, Deriv Tanh x (sech x ^ 2)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Tanh

/-- Hyp-Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Tanh
  : D₋ tanh x₀ =. the (sech x₀ ^ 2)
:= DerivExpr.toLeft <| DerivExpr.Tanh

/-- Hyp-Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Tanh
  : D₊ tanh x₀ =. the (sech x₀ ^ 2)
:= DerivExpr.toRight <| DerivExpr.Tanh

/-- Hyp-Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Coth
    (h_dom : x₀ ≠ 0)
  : D coth x₀ =. the (- csch x₀ ^ 2)
:= script
  given_proper
  calc
    _  =  D (cosh / sinh) x₀
          := by
            congr
            funext x
            func_apply
            simp only [coth, Real.tanh_eq_sinh_div_cosh, one_div, inv_div]
    _  =? (D cosh x₀ * the (sinh x₀) - D sinh x₀ * the (cosh x₀))
            / the (sinh x₀ ^ 2)
          := Div
    _  =  the ((sinh x₀ * sinh x₀ - cosh x₀ * cosh x₀) / sinh x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Cosh, DerivExpr.Sinh]
            simp only [finite_mul, finite_sub]
            poly_rw [finite_div (pow_ne_zero 2 (Sinh_ne_zero_iff.mpr h_dom))]
    _  =  the (- csch x₀ ^ 2)
          := by
            congr
            rw [csch, div_pow, one_pow, ← neg_div]
            congr
            linarith [Real.cosh_sq_sub_sinh_sq x₀]

/-- Hyp-Cotangent Function's Derivative -/
theorem Deriv.Coth
  : ∀ x ≠ 0, Deriv Coth x (- csch x ^ 2)
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists |x| / 2 with by positivity
    intro a h_a ha0
    simp only [mem_Nbhd] at h_a
    rcases h_a with ⟨hlo, hhi, _⟩
    rw [ha0] at hlo hhi
    script_cases_by lt_or_gt_of_ne hx
    · rw [abs_of_neg hp] at hlo hhi
      linarith
    · rw [abs_of_pos hq] at hlo hhi
      linarith
  · exact DerivExpr.Coth hx

/-- Hyp-Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Coth
    (h_dom : x₀ ≠ 0)
  : D₋ coth x₀ =. the (- csch x₀ ^ 2)
:= DerivExpr.toLeft <| DerivExpr.Coth h_dom

/-- Hyp-Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Coth
    (h_dom : x₀ ≠ 0)
  : D₊ coth x₀ =. the (- csch x₀ ^ 2)
:= DerivExpr.toRight <| DerivExpr.Coth h_dom

/-- Hyp-Secant Function's Derivative (Expression) -/
theorem DerivExpr.Sech
  : D sech x₀ =. the (- tanh x₀ * sech x₀)
:= script
  given_proper
  calc
    _  =  D cosh⁻¹ x₀
          := by
            congr
            funext x
            func_apply
            simp only [sech, one_div]
    _  =? - D cosh x₀ / the (cosh x₀ ^ 2)
          := Inv
    _  =  the (- sinh x₀ / cosh x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Cosh]
            change the (-sinh x₀) / the (cosh x₀ ^ 2) = _
            poly_rw [finite_div (pow_ne_zero 2 (Real.cosh_pos x₀).ne')]
    _  =  the (- tanh x₀ * sech x₀)
          := by
            simp only [Real.tanh_eq_sinh_div_cosh, sech]
            ring_nf

/-- Hyp-Secant Function's Derivative -/
theorem Deriv.Sech
  : ∀ x, Deriv Sech x (- tanh x * sech x)
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Sech

/-- Hyp-Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Sech
  : D₋ sech x₀ =. the (- tanh x₀ * sech x₀)
:= DerivExpr.toLeft <| DerivExpr.Sech

/-- Hyp-Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Sech
  : D₊ sech x₀ =. the (- tanh x₀ * sech x₀)
:= DerivExpr.toRight <| DerivExpr.Sech

/-- Hyp-Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Csch
    (h_dom : x₀ ≠ 0)
  : D csch x₀ =. the (- coth x₀ * csch x₀)
:= script
  given_proper
  calc
    _  =  D sinh⁻¹ x₀
          := by
            congr
            funext x
            func_apply
            simp only [csch, one_div]
    _  =? - D sinh x₀ / the (sinh x₀ ^ 2)
          := Inv
    _  =  the (- cosh x₀ / sinh x₀ ^ 2)
          := by
            poly_rw [DerivExpr.Sinh]
            change the (-cosh x₀) / the (sinh x₀ ^ 2) = _
            poly_rw [finite_div (pow_ne_zero 2 (Sinh_ne_zero_iff.mpr h_dom))]
    _  =  the (- coth x₀ * csch x₀)
          := by
            simp only [coth, Real.tanh_eq_sinh_div_cosh, csch, one_div, inv_div]
            ring_nf

/-- Hyp-Cosecant Function's Derivative -/
theorem Deriv.Csch
  : ∀ x ≠ 0, Deriv Csch x (- coth x * csch x)
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists |x| / 2 with by positivity
    intro a h_a ha0
    simp only [mem_Nbhd] at h_a
    rcases h_a with ⟨hlo, hhi, _⟩
    rw [ha0] at hlo hhi
    script_cases_by lt_or_gt_of_ne hx
    · rw [abs_of_neg hp] at hlo hhi
      linarith
    · rw [abs_of_pos hq] at hlo hhi
      linarith
  · exact DerivExpr.Csch hx

/-- Hyp-Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Csch
    (h_dom : x₀ ≠ 0)
  : D₋ csch x₀ =. the (- coth x₀ * csch x₀)
:= DerivExpr.toLeft <| DerivExpr.Csch h_dom

/-- Hyp-Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Csch
    (h_dom : x₀ ≠ 0)
  : D₊ csch x₀ =. the (- coth x₀ * csch x₀)
:= DerivExpr.toRight <| DerivExpr.Csch h_dom

/-- Arc-Sine Function's Derivative (Expression) -/
theorem DerivExpr.Arcsin
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arcsin x₀ =. the (1 / √(1 - x₀ ^ 2))
:= by
  let q : ℝ → ℝ := fun u => if u = arcsin x₀ then cos (arcsin x₀)
    else (sin u - sin (arcsin x₀)) / (u - arcsin x₀)
  have hq : lim (arcsin x₀) q =. the (q (arcsin x₀)) := by
    calc
      _ = D sin (arcsin x₀) := by
        apply FuncLimitExpr.Congr
        refine ⟨1, zero_lt_one, ?_⟩
        intro u hu
        simp [q, hu.2.2]
      _ =. the (cos (arcsin x₀)) := DerivExpr.Sin
      _ = the (q (arcsin x₀)) := by simp [q]
  have hc : lim x₀ (q ∘ arcsin) =. the (√(1 - x₀ ^ 2)) := by
    simpa [q, Real.cos_arcsin] using
      FuncLimitExpr.CompSV (FuncLimitExpr.Arcsin h_dom) hq
  have hn : √(1 - x₀ ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    nlinarith [h_dom.1, h_dom.2]
  calc
    _  =  lim x₀ fun x ↦ 1 / (q (arcsin x))
          := by
            apply FuncLimitExpr.Congr
            refine ⟨min (x₀ + 1) (1 - x₀), lt_min (by linarith [h_dom.1])
              (by linarith [h_dom.2]), ?_⟩
            intro x hx
            have hxl : -1 ≤ x := by linarith [hx.1, min_le_left (x₀ + 1) (1 - x₀)]
            have hxu : x ≤ 1 := by linarith [hx.2.1, min_le_right (x₀ + 1) (1 - x₀)]
            have hne : arcsin x ≠ arcsin x₀ := by
              intro he
              have := congrArg sin he
              rw [Real.sin_arcsin hxl hxu,
                Real.sin_arcsin h_dom.1.le h_dom.2.le] at this
              exact hx.2.2 this
            dsimp [q]
            rw_neg hne
            rw [Real.sin_arcsin hxl hxu, Real.sin_arcsin h_dom.1.le h_dom.2.le]
            field_simp
    _  =. (lim x₀ fun _ ↦ 1) / lim x₀ (q ∘ arcsin)
          := FuncLimitExpr.Div
    _  =  the 1 / the (√(1 - x₀ ^ 2))
          := by
            poly_rw [hc]
            lim_cont
    _  =. the (1 / √(1 - x₀ ^ 2))
          := finite_div hn

/-- Arc-Sine Function's Derivative -/
theorem Deriv.Arcsin
  : ∀ x ∈ Ioo (-1) 1, Deriv Arcsin x (1 / √(1 - x ^ 2))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists min (x + 1) (1 - x) with lt_min (by linarith [hx.1])
      (by linarith [hx.2])
    intro a h_a
    simp only [mem_Icc, mem_Nbhd] at h_a ⊢
    script_split_and
    · linarith [h_a.1, min_le_left (x + 1) (1 - x)]
    · linarith [h_a.2.1, min_le_right (x + 1) (1 - x)]
  · exact DerivExpr.Arcsin hx

/-- Arc-Sine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arcsin
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arcsin x₀ =. the (1 / √(1 - x₀ ^ 2))
:= DerivExpr.toLeft <| DerivExpr.Arcsin h_dom

/-- Arc-Sine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arcsin
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arcsin x₀ =. the (1 / √(1 - x₀ ^ 2))
:= DerivExpr.toRight <| DerivExpr.Arcsin h_dom

/-- Arc-Cosine Function's Derivative (Expression) -/
theorem DerivExpr.Arccos
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arccos x₀ =. the (-1 / √(1 - x₀ ^ 2))
:= script
  calc
    _  =  D (const (π / 2) - arcsin) x₀
          := rfl
    _  =. D (const (π / 2)) x₀ - D arcsin x₀
          := Sub
    _  =  the 0 - the (1 / √(1 - x₀ ^ 2))
          := by poly_rw [DerivExpr.Constant, DerivExpr.Arcsin h_dom]
    _  =  the (-1 / √(1 - x₀ ^ 2))
          := by rw [finite_sub]; ring_nf

/-- Arc-Cosine Function's Derivative -/
theorem Deriv.Arccos
  : ∀ x ∈ Ioo (-1) 1, Deriv Arccos x (-1 / √(1 - x ^ 2))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_exists min (x + 1) (1 - x) with lt_min (by linarith [hx.1])
      (by linarith [hx.2])
    intro a h_a
    simp only [mem_Icc, mem_Nbhd] at h_a ⊢
    script_split_and
    · linarith [h_a.1, min_le_left (x + 1) (1 - x)]
    · linarith [h_a.2.1, min_le_right (x + 1) (1 - x)]
  · exact DerivExpr.Arccos hx

/-- Arc-Cosine Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccos
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arccos x₀ =. the (-1 / √(1 - x₀ ^ 2))
:= DerivExpr.toLeft <| DerivExpr.Arccos h_dom

/-- Arc-Cosine Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccos
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arccos x₀ =. the (-1 / √(1 - x₀ ^ 2))
:= DerivExpr.toRight <| DerivExpr.Arccos h_dom

/-- Arc-Tangent Function's Derivative (Expression) -/
theorem DerivExpr.Arctan
  : D arctan x₀ =. the (1 / (1 + x₀ ^ 2))
:= by
  let q : ℝ → ℝ := fun u => if u = arctan x₀ then sec (arctan x₀) ^ 2
    else (tan u - tan (arctan x₀)) / (u - arctan x₀)
  have hq : lim (arctan x₀) q =. the (q (arctan x₀)) := by
    calc
      _ = D tan (arctan x₀) := by
        apply FuncLimitExpr.Congr
        refine ⟨1, zero_lt_one, ?_⟩
        intro u hu
        simp [q, hu.2.2]
      _ =. the (sec (arctan x₀) ^ 2) :=
        DerivExpr.Tan (ne_of_gt (Real.cos_arctan_pos x₀))
      _ = the (q (arctan x₀)) := by simp [q]
  have hv : sec (arctan x₀) ^ 2 = 1 + x₀ ^ 2 := by
    rw [sec, Real.cos_arctan]
    simp only [one_div, inv_inv]
    exact Real.sq_sqrt (by positivity)
  have hc : lim x₀ (q ∘ arctan) =. the (1 + x₀ ^ 2) := by
    simpa only [q, if_pos rfl, hv] using
      FuncLimitExpr.CompSV FuncLimitExpr.Arctan hq
  calc
    _ = lim x₀ fun x ↦ 1 / (q (arctan x)) := by
      apply FuncLimitExpr.Congr
      refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      have hne : arctan x ≠ arctan x₀ := by
        intro he
        exact hx.2.2 (Real.arctan_injective he)
      dsimp [q]
      rw [if_neg hne, Real.tan_arctan, Real.tan_arctan]
      field_simp
    _ =. (lim x₀ fun _ => (1 : ℝ)) / lim x₀ (q ∘ arctan) := FuncLimitExpr.Div
    _ = the 1 / the (1 + x₀ ^ 2) := by
      poly_rw [hc]
      lim_cont
    _ =. the (1 / (1 + x₀ ^ 2)) := finite_div (by positivity)

/-- Arc-Tangent Function's Derivative -/
theorem Deriv.Arctan
  : ∀ x, Deriv Arctan x (1 / (1 + x ^ 2))
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Arctan

/-- Arc-Tangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arctan
  : D₋ arctan x₀ =. the (1 / (1 + x₀ ^ 2))
:= DerivExpr.toLeft <| DerivExpr.Arctan

/-- Arc-Tangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arctan
  : D₊ arctan x₀ =. the (1 / (1 + x₀ ^ 2))
:= DerivExpr.toRight <| DerivExpr.Arctan

/-- Arc-Cotangent Function's Derivative (Expression) -/
theorem DerivExpr.Arccot
  : D arccot x₀ =. the (-1 / (1 + x₀ ^ 2))
:= script
  calc
    _  =  D (const (π / 2) - arctan) x₀
          := rfl
    _  =. D (const (π / 2)) x₀ - D arctan x₀
          := Sub
    _  =  the 0 - the (1 / (1 + x₀ ^ 2))
          := by poly_rw [DerivExpr.Constant, DerivExpr.Arctan]
    _  =  the (-1 / (1 + x₀ ^ 2))
          := by rw [finite_sub]; ring_nf

/-- Arc-Cotangent Function's Derivative -/
theorem Deriv.Arccot
  : ∀ x, Deriv Arccot x (-1 / (1 + x ^ 2))
:= by
  intro x
  apply Deriv.fromDerivExpr
  · script_exists 1 with zero_lt_one
    intro a h_a
    simp only [mem_Nbhd] at h_a
    exact mem_univ _
  · exact DerivExpr.Arccot

/-- Arc-Cotangent Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccot
  : D₋ arccot x₀ =. the (-1 / (1 + x₀ ^ 2))
:= DerivExpr.toLeft <| DerivExpr.Arccot

/-- Arc-Cotangent Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccot
  : D₊ arccot x₀ =. the (-1 / (1 + x₀ ^ 2))
:= DerivExpr.toRight <| DerivExpr.Arccot

/-- Arc-Secant Function's Derivative (Expression) -/
theorem DerivExpr.Arcsec
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arcsec x₀ =. the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= by
  have hx : x₀ ≠ 0 := by rcases h_dom with h | h <;> linarith
  have hx2 : 0 < x₀ ^ 2 - 1 := by
    rcases h_dom with h | h <;> nlinarith
  have hi : -1 < x₀⁻¹ ∧ x₀⁻¹ < 1 := by
    rcases h_dom with h | h
    · constructor
      · simpa using (inv_lt_inv_of_neg (by norm_num : (-1 : ℝ) < 0)
          (by linarith : x₀ < 0)).mpr h
      · exact lt_trans (inv_lt_zero'.mpr (by linarith)) zero_lt_one
    · constructor
      · exact lt_trans (by norm_num) (inv_pos.mpr (by linarith))
      · exact (inv_lt_one₀ (by linarith)).mpr h
  have hs : √(1 - (x₀⁻¹) ^ 2) = √(x₀ ^ 2 - 1) / |x₀| := by
    rw [← Real.sqrt_sq_eq_abs x₀, ← Real.sqrt_div (le_of_lt hx2)]
    congr
    field_simp
  have hd : D id⁻¹ x₀ =. the (-1 / x₀ ^ 2) := by
    script_given_proper
    calc
      _ =? - D id x₀ / the (x₀ ^ 2) := Inv
      _ =. the (-1 / x₀ ^ 2) := by
        poly_rw [DerivExpr.Identity]
        exact finite_div (pow_ne_zero 2 hx)
  script_given_proper
  calc
    _  =? D arccos (x₀⁻¹) * D id⁻¹ x₀
          := Comp
    _  =  the (-1 / √(1 - (x₀⁻¹) ^ 2)) * the (-1 / x₀ ^ 2)
          := by poly_rw [DerivExpr.Arccos hi, hd]
    _  =  the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
          := by
            rw [finite_mul, hs]
            congr 1
            field_simp
            linarith [sq_abs x₀]

/-- Arc-Secant Function's Derivative -/
theorem Deriv.Arcsec
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arcsec x (1 / (|x| * √(x ^ 2 - 1)))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_cases_by hx
    · simp only [mem_Iio] at hp
      script_exists (-x - 1) / 2 with by linarith
      intro a h_a
      left
      simp only [mem_Iic, mem_Nbhd] at h_a ⊢
      linarith
    · simp only [mem_Ioi] at hq
      script_exists (x - 1) / 2 with by linarith
      intro a h_a
      right
      simp only [mem_Ici, mem_Nbhd] at h_a ⊢
      linarith
  · exact DerivExpr.Arcsec hx

/-- Arc-Secant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arcsec
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arcsec x₀ =. the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= DerivExpr.toLeft <| DerivExpr.Arcsec h_dom

/-- Arc-Secant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arcsec
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arcsec x₀ =. the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= DerivExpr.toRight <| DerivExpr.Arcsec h_dom

/-- Arc-Cosecant Function's Derivative (Expression) -/
theorem DerivExpr.Arccsc
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arccsc x₀ =. the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= script
  calc
    _  =  D (const (π / 2) - arcsec) x₀
          := by
            congr
            funext x
            change arcsin x⁻¹ = π / 2 - (π / 2 - arcsin x⁻¹)
            ring
    _  =. D (const (π / 2)) x₀ - D arcsec x₀
          := Sub
    _  =  the 0 - the (1 / (|x₀| * √(x₀ ^ 2 - 1)))
          := by poly_rw [DerivExpr.Constant, DerivExpr.Arcsec h_dom]
    _  =  the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
          := by rw [finite_sub]; ring_nf

/-- Arc-Cosecant Function's Derivative -/
theorem Deriv.Arccsc
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, Deriv Arccsc x (-1 / (|x| * √(x ^ 2 - 1)))
:= by
  intro x hx
  apply Deriv.fromDerivExpr
  · script_cases_by hx
    · simp only [mem_Iio] at hp
      script_exists (-x - 1) / 2 with by linarith
      intro a h_a
      left
      simp only [mem_Iic, mem_Nbhd] at h_a ⊢
      linarith
    · simp only [mem_Ioi] at hq
      script_exists (x - 1) / 2 with by linarith
      intro a h_a
      right
      simp only [mem_Ici, mem_Nbhd] at h_a ⊢
      linarith
  · exact DerivExpr.Arccsc hx

/-- Arc-Cosecant Function's Left Derivative (Expression) -/
theorem LeftDerivExpr.Arccsc
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arccsc x₀ =. the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= DerivExpr.toLeft <| DerivExpr.Arccsc h_dom

/-- Arc-Cosecant Function's Right Derivative (Expression) -/
theorem RightDerivExpr.Arccsc
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arccsc x₀ =. the (-1 / (|x₀| * √(x₀ ^ 2 - 1)))
:= DerivExpr.toRight <| DerivExpr.Arccsc h_dom

end


page_end
