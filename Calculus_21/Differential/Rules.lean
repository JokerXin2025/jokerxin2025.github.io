/-
    «Calculus_21».Differential.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Defs
import «Calculus_21».Limit.Elementary
set_option linter.style.header false


/-! # Derivative Calculation Rules -/

section
variable {n : ℕ} {F G : Function} {k x₀ D₁ D₂ : ℝ}

/-- Scalar Multiplication of Derivative -/
theorem Deriv.SMul
    (h_F : Deriv F x₀ D₁)
  : Deriv (k • F) x₀ (k * D₁)
:= sorry

/-- Scalar Multiplication of Left Derivative -/
theorem LeftDeriv.SMul
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (k • F) x₀ (k * D₁)
:= sorry

/-- Scalar Multiplication of Right Derivative -/
theorem RightDeriv.SMul
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (k • F) x₀ (k * D₁)
:= sorry

/-- Scalar Multiplication of N-th Order Derivative -/
theorem NthDeriv.SMul
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (k • F) x₀ (k * D₁)
:= sorry

/-- Additive Inverse of Derivative -/
theorem Deriv.Neg
    (h_F : Deriv F x₀ D₁)
  : Deriv (-F) x₀ (-D₁)
:= sorry

/-- Additive Inverse of Left Derivative -/
theorem LeftDeriv.Neg
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (-F) x₀ (-D₁)
:= sorry

/-- Additive Inverse of Right Derivative -/
theorem RightDeriv.Neg
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (-F) x₀ (-D₁)
:= sorry

/-- Additive Inverse of N-th Order Derivative -/
theorem NthDeriv.Neg
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (-F) x₀ (-D₁)
:= sorry

/-- Multiplicative Inverse of Derivative -/
theorem Deriv.Inv
    (h_F : Deriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : Deriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Multiplicative Inverse of Left Derivative -/
theorem LeftDeriv.Inv
    (h_F : LeftDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : LeftDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Multiplicative Inverse of Right Derivative -/
theorem RightDeriv.Inv
    (h_F : RightDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : RightDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= sorry

/-- Addition of Derivative -/
theorem Deriv.Add
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Addition of Left Derivative -/
theorem LeftDeriv.Add
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Addition of Right Derivative -/
theorem RightDeriv.Add
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Addition of N-th Order Derivative -/
theorem NthDeriv.Add
    (h_F : NthDeriv n F x₀ D₁) (h_G : NthDeriv n G x₀ D₂)
  : NthDeriv n (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Subtraction of Derivative -/
theorem Deriv.Sub
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Subtraction of Left Derivative -/
theorem LeftDeriv.Sub
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Subtraction of Right Derivative -/
theorem RightDeriv.Sub
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Subtraction of N-th Order Derivative -/
theorem NthDeriv.Sub
    (h_F : NthDeriv n F x₀ D₁) (h_G : NthDeriv n G x₀ D₂)
  : NthDeriv n (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Multiplication of Derivative -/
theorem Deriv.Mul
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
  : Deriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Multiplication of Left Derivative -/
theorem LeftDeriv.Mul
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
  : LeftDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Multiplication of Right Derivative -/
theorem RightDeriv.Mul
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
  : RightDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= sorry

/-- Division of Derivative -/
theorem Deriv.Div
    (h_F : Deriv F x₀ D₁) (h_G : Deriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : Deriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Division of Left Derivative -/
theorem LeftDeriv.Div
    (h_F : LeftDeriv F x₀ D₁) (h_G : LeftDeriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : LeftDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Division of Right Derivative -/
theorem RightDeriv.Div
    (h_F : RightDeriv F x₀ D₁) (h_G : RightDeriv G x₀ D₂)
    (h_G_ne0 : G.map x₀ ≠ 0)
  : RightDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= sorry

/-- Composition of Derivative -/
theorem Deriv.Chain {F' G' : ℝ}
    (h_G : Deriv G x₀ G') (h_F : Deriv F (G.map x₀) F')
    (h_FGx₀ : G.map x₀ ∈ F.domain)
  : Deriv (F ⊙ G) x₀ (F' * G')
:= by
  let slope : Function :=
    ⟨fun u => if u = G.map x₀ then F' else
        (F.map u - F.map (G.map x₀)) / (u - G.map x₀),
      F.domain ∪ {G.map x₀}⟩
  have h_slope : FuncLimit slope (G.map x₀) F' := by
    apply h_F.Congr
    rcases h_F.1 with ⟨δ, hδ, hdom⟩
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro u hu
      exact Or.inl (hdom hu).1.1.1
    · intro u hu
      change (F.map u - F.map (G.map x₀)) / (u - G.map x₀) = _
      simp [slope, hu.2.2]
  have h_slope_cont : isContinuousAt slope (G.map x₀) := by
    refine ⟨Or.inr rfl, ?_⟩
    simpa [slope] using h_slope
  have h_G_cont : FuncLimit G x₀ (G.map x₀) := by
    let displacement := Identity - Constant x₀
    have h_displacement : FuncLimit displacement x₀ 0 := by
      convert FuncLimit.Sub
        (Continuity.Identity x₀ (mem_univ _)).2
        (Continuity.Constant x₀ (mem_univ _) :
          isContinuousAt (Constant x₀) x₀).2 using 1
      change 0 = x₀ - x₀
      ring
    have h_product := FuncLimit.Mul h_G h_displacement
    have h_difference : FuncLimit (G - Constant (G.map x₀)) x₀ 0 := by
      apply (show FuncLimit
        (((G - Constant (G.map x₀)) / (Identity - Constant x₀)) * displacement)
          x₀ 0 by simpa using h_product).Congr
      rcases h_G.1 with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, ?_, ?_⟩
      · intro x hx
        exact ⟨(hdom hx).1.1.1, trivial⟩
      · intro x hx
        change ((G.map x - G.map x₀) / (x - x₀)) * (x - x₀) =
          G.map x - G.map x₀
        field_simp [sub_ne_zero.mpr hx.2.2]
    have h_sum := FuncLimit.Add h_difference
      (Continuity.Constant (C := G.map x₀) x₀ (mem_univ _)).2
    apply (show FuncLimit
      ((G - Constant (G.map x₀)) + Constant (G.map x₀)) x₀ (G.map x₀) by
        convert h_sum using 1
        change G.map x₀ = 0 + G.map x₀
        ring).Congr
    rcases h_G.1 with ⟨δ, hδ, hdom⟩
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro x hx
      exact (hdom hx).1.1.1
    · intro x hx
      change (G.map x - G.map x₀) + G.map x₀ = G.map x
      ring
  have h_slope_comp : FuncLimit (slope ⊙ G) x₀ F' :=
    by simpa [slope] using FuncLimit.CompSV h_G_cont h_slope_cont
  have h_product := FuncLimit.Mul h_slope_comp h_G
  apply h_product.Congr
  rcases h_G.1 with ⟨δG, hδG, hGdom⟩
  rcases h_F.1 with ⟨δF, hδF, hFdom⟩
  rcases h_G_cont.2 δF hδF with ⟨δC, hδC, hGclose⟩
  refine ⟨min δG δC, lt_min hδG hδC, ?_, ?_⟩
  · intro x hx
    have hxG : x ∈ Nbhd x₀ δG := by
      exact ⟨by linarith [hx.1, min_le_left δG δC],
        by linarith [hx.2.1, min_le_left δG δC], hx.2.2⟩
    have hxC : x ∈ Nbhd x₀ δC := by
      exact ⟨by linarith [hx.1, min_le_right δG δC],
        by linarith [hx.2.1, min_le_right δG δC], hx.2.2⟩
    have hxGdom := hGdom hxG
    have hGx_near := hGclose x hxC
    have hGxF : G.map x ∈ F.domain := by
      by_cases h_eq : G.map x = G.map x₀
      · simpa [h_eq] using h_FGx₀
      · exact (hFdom ⟨hGx_near.1, hGx_near.2, h_eq⟩).1.1.1
    refine ⟨⟨⟨⟨hxGdom.1.1.1, hGxF⟩, trivial⟩,
      ⟨trivial, trivial⟩⟩, ?_⟩
    change x - x₀ ≠ 0
    exact sub_ne_zero.mpr hx.2.2
  · intro x hx
    change slope.map (G.map x) * ((G.map x - G.map x₀) / (x - x₀)) =
      ((F.map (G.map x) - F.map (G.map x₀)) / (x - x₀))
    by_cases h_eq : G.map x = G.map x₀
    · simp [slope, h_eq]
    · simp only [slope, h_eq, ↓reduceIte]
      field_simp [sub_ne_zero.mpr hx.2.2, sub_ne_zero.mpr h_eq]

/-- Composition of Left Derivative -/
theorem LeftDeriv.Chain {F' G' : ℝ}
    (h_G : LeftDeriv G x₀ G') (h_F : LeftDeriv F (G.map x₀) F')
  : LeftDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- Composition of Right Derivative -/
theorem RightDeriv.Chain {F' G' : ℝ}
    (h_G : RightDeriv G x₀ G') (h_F : RightDeriv F (G.map x₀) F')
  : RightDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

end


page_end
