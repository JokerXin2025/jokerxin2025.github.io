/-
    «Calculus_21».Continuity.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
import «Calculus_21».Limit.Rules
set_option linter.style.header false


/-! # Core Properties of Function's Continuity -/

/-- Function Limit Composition (Special Version)
    - This version requires outer function `F` to be continuous at `u₀` -/
theorem FuncLimit.CompSV {x₀ u₀ : ℝ} {F G : Function}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F_cont : isContinuousAt F u₀)
  : FuncLimit (F ⊙ G) x₀ (F.map u₀)
:= by
  have h_u₀_in_F := h_F_cont.1
  have h_F_lim := h_F_cont.2
  rcases h_F_lim.1 with ⟨δF, hδF_pos, hδF_dom⟩
  rcases h_u₀.1 with ⟨δG, hδG_pos, hδG_dom⟩
  rcases h_u₀.2 δF hδF_pos with ⟨δ2, hδ2_pos, hδ2⟩
  constructor
  · use min δG δ2, lt_min hδG_pos hδ2_pos
    intro x h_x
    have h_x_G_nbhd : x ∈ Nbhd x₀ δG := by
      have : min δG δ2 ≤ δG := min_le_left _ _
      exact ⟨by linarith [h_x.1], by linarith [h_x.2.1], h_x.2.2⟩
    have h_x_2_nbhd : x ∈ Nbhd x₀ δ2 := by
      have : min δG δ2 ≤ δ2 := min_le_right _ _
      exact ⟨by linarith [h_x.1], by linarith [h_x.2.1], h_x.2.2⟩
    have h_xG : x ∈ G.domain := hδG_dom h_x_G_nbhd
    have h_x_eps := hδ2 x h_x_2_nbhd
    have h_xF : G.map x ∈ F.domain := by
      by_cases h_eq : G.map x = u₀
      · rw [h_eq]
        exact h_u₀_in_F
      · exact hδF_dom ⟨h_x_eps.1, h_x_eps.2, h_eq⟩
    exact ⟨h_xG, h_xF⟩
  · intro ε h_ε
    rcases h_F_lim.2 ε h_ε with ⟨δ1, hδ1_pos, hδ1⟩
    rcases h_u₀.2 δ1 hδ1_pos with ⟨δ3, hδ3_pos, hδ3⟩
    use δ3, hδ3_pos
    intro x h_x
    have hGx_nbho := hδ3 x h_x
    by_cases h_eq : G.map x = u₀
    · change F.map (G.map x) ∈ Nbho (F.map u₀) ε
      rw [h_eq]
      exact ⟨by linarith [h_ε], by linarith [h_ε]⟩
    · have hGx_nbhd : G.map x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
      exact hδ1 (G.map x) hGx_nbhd

theorem Continuity.Congr {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀)
    (h_congr : ∃ δ > 0, Nbho x₀ δ ⊆ G.domain ∧
      ∀ x ∈ Nbho x₀ δ, F.map x = G.map x)
  : isContinuousAt G x₀
:= by
  rcases h_congr with ⟨δ, hδ, hG_dom, heq⟩
  have h_x₀ : x₀ ∈ Nbho x₀ δ := ⟨by linarith, by linarith⟩
  refine ⟨hG_dom h_x₀, ?_⟩
  rw [← heq x₀ h_x₀]
  apply FuncLimit.Congr h_F.2
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro _ h_x
    exact hG_dom (Nbhd_subset_Nbho h_x)
  · intro _ h_x
    exact heq _ (Nbhd_subset_Nbho h_x)

/-- Additive Inverse of Continuity -/
theorem Continuity.Neg {F : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀)
  : isContinuousAt (-F) x₀
:= ⟨h_F.1, FuncLimit.Neg h_F.2⟩

/-- Scalar Multiplication of Continuity -/
theorem Continuity.SMul {F : Function} {x₀ k : ℝ}
    (h_F : isContinuousAt F x₀)
  : isContinuousAt (k • F) x₀
:= ⟨h_F.1, FuncLimit.SMul h_F.2⟩

/-- Addition of Continuity -/
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Add h_F.2 h_G.2⟩

/-- Subtraction of Continuity -/
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Sub h_F.2 h_G.2⟩

/-- Multiplication of Continuity -/
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Mul h_F.2 h_G.2⟩

/-- Division of Continuity -/
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= ⟨⟨⟨h_F.1, h_G.1⟩, h_Gx₀_ne_0⟩, FuncLimit.Div h_F.2 h_G.2 h_Gx₀_ne_0⟩

/-- Composition of Continuity -/
theorem Continuity.Comp {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F (G.map x₀))
    (h_G : isContinuousAt G x₀)
  : isContinuousAt (F ⊙ G) x₀
:= ⟨⟨h_G.1, h_F.1⟩, FuncLimit.CompSV h_G.2 h_F⟩


page_end
