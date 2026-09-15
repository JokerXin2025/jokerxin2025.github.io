/-
    «Calculus_21».Differential.MeanValue
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.ClosedInterval
import «Calculus_21».Differential.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Mean Value Theorems -/

private lemma hasDerivAt_of_Deriv {F : Function} {x₀ D : ℝ}
    (h_deriv : Deriv F x₀ D)
  : HasDerivAt F.map D x₀
:= by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhds]
  intro ε h_ε
  rcases h_deriv.2 ε h_ε with ⟨δ, hδ, hmap⟩
  have hevent : Metric.ball x₀ δ ∈ nhdsWithin x₀ ({x₀}ᶜ : Set ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Metric.ball x₀ δ, Metric.ball_mem_nhds x₀ hδ, Set.inter_subset_left⟩
  filter_upwards [hevent, self_mem_nhdsWithin] with x h_xdist h_xne
  have h_xNbhd : x ∈ Nbhd x₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq] at h_xdist
    rw [mem_Nbhd]
    constructor
    · linarith [neg_lt_of_abs_lt h_xdist]
    · exact ⟨by linarith [lt_of_abs_lt h_xdist], h_xne⟩
  have h_εmap := hmap x h_xNbhd
  rw [Nbho_abs] at h_εmap
  change |(F.map x - F.map x₀) / (x - x₀) - D| < ε at h_εmap
  simpa [slope_def_field, Real.dist_eq, abs_sub_comm] using h_εmap

/-- Fermat's Lemma -/
theorem Fermat_Lemma {F : Function} {x₀ δ : ℝ}
    (hδ : 0 < δ)
    (_h_dom : Nbho x₀ δ ⊆ F.domain)
    (h_deriv : isDerivableAt F x₀)
    (h_extre : (∀ x ∈ Nbho x₀ δ, F.map x ≤ F.map x₀)
               ∨ (∀ x ∈ Nbho x₀ δ, F.map x ≥ F.map x₀))
  : Deriv F x₀ 0
:= by
  rcases h_deriv with ⟨D, hD⟩
  have hmath : HasDerivAt F.map D x₀ := hasDerivAt_of_Deriv hD
  have hlocal : IsLocalExtr F.map x₀ := by
    rcases h_extre with hmax | hmin
    · apply Or.inr
      filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x h_x
      apply hmax x
      rw [Metric.mem_ball, Real.dist_eq] at h_x
      rw [Nbho_abs]
      simpa [abs_sub_comm] using h_x
    · apply Or.inl
      filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x h_x
      apply hmin x
      rw [Metric.mem_ball, Real.dist_eq] at h_x
      rw [Nbho_abs]
      simpa [abs_sub_comm] using h_x
  have hD0 : D = 0 := hlocal.hasDerivAt_eq_zero hmath
  simpa [hD0] using hD

section
variable {F G : Function} {a b : ℝ}

/-- Rolle's Mean Value Theorem -/
theorem Rolle_MeanValue
    (h_a_lt_b : a < b)
    (_h_dom : Icc a b ⊆ F.domain)
    (h_eq : F.map a = F.map b)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ 0
:= by
  have hmath_cont := h_cont.continuousOn
  have hmath_deriv : ∀ x ∈ Ioo a b, HasDerivAt F.map ((Diff F).map x) x := by
    intro x h_x
    unfold Diff
    simp only [dif_pos (h_deriv x h_x)]
    exact hasDerivAt_of_Deriv (Classical.choose_spec (h_deriv x h_x))
  rcases exists_hasDerivAt_eq_zero h_a_lt_b hmath_cont h_eq hmath_deriv with
    ⟨ξ, h_ξ, hzero⟩
  exists ξ with h_ξ
  have hchosen : Deriv F ξ ((Diff F).map ξ) := by
    unfold Diff
    simp only [dif_pos (h_deriv ξ h_ξ)]
    exact Classical.choose_spec (h_deriv ξ h_ξ)
  simpa [hzero] using hchosen

/-- Lagrange's Mean Value Theorem -/
theorem Lagrange_MeanValue
    (h_a_lt_b : a < b)
    (_h_dom : Icc a b ⊆ F.domain)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ ((F.map b - F.map a) / (b - a))
:= by
  have hmath_cont := h_cont.continuousOn
  have hmath_deriv : ∀ x ∈ Ioo a b, HasDerivAt F.map ((Diff F).map x) x := by
    intro x h_x
    unfold Diff
    simp only [dif_pos (h_deriv x h_x)]
    exact hasDerivAt_of_Deriv (Classical.choose_spec (h_deriv x h_x))
  rcases exists_hasDerivAt_eq_slope F.map (Diff F).map h_a_lt_b hmath_cont hmath_deriv with
    ⟨ξ, h_ξ, hslope⟩
  exists ξ with h_ξ
  have hchosen : Deriv F ξ ((Diff F).map ξ) := by
    unfold Diff
    simp only [dif_pos (h_deriv ξ h_ξ)]
    exact Classical.choose_spec (h_deriv ξ h_ξ)
  simpa [hslope] using hchosen

/-- Cauchy's Mean Value Theorem -/
theorem Cauchy_MeanValue
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_G'_ne_0 : ∀ x ∈ (Diff G).domain, (Diff G).map x ≠ 0)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (F.map b - F.map a) / (G.map b - G.map a) = (Diff F).map ξ / (Diff G).map ξ
:= sorry

/-- Cauchy's Mean Value Theorem (Product Form) -/
theorem Cauchy_MeanValue'
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (Diff F).map ξ * (G.map b - G.map a) = (Diff G).map ξ * (F.map b - F.map a)
:= sorry

end


page_end
