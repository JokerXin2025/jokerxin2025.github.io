/-
    Calculus_21.Continuity.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
import «Calculus_21».Limit.Rules
set_option linter.style.header false


/-! # Properties of Function's Continuity -/

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
    intro x hx
    have hx_G_nbhd : x ∈ Nbhd x₀ δG := by
      have : min δG δ2 ≤ δG := min_le_left _ _
      exact ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2⟩
    have hx_2_nbhd : x ∈ Nbhd x₀ δ2 := by
      have : min δG δ2 ≤ δ2 := min_le_right _ _
      exact ⟨by linarith [hx.1], by linarith [hx.2.1], hx.2.2⟩
    have hxG : x ∈ G.domain := hδG_dom hx_G_nbhd
    have hx_eps := hδ2 x hx_2_nbhd
    have hxF : G.map x ∈ F.domain := by
      by_cases h_eq : G.map x = u₀
      · rw [h_eq]
        exact h_u₀_in_F
      · exact hδF_dom ⟨hx_eps.1, hx_eps.2, h_eq⟩
    exact ⟨hxG, hxF⟩
  · intro ε hε
    rcases h_F_lim.2 ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    rcases h_u₀.2 δ1 hδ1_pos with ⟨δ3, hδ3_pos, hδ3⟩
    use δ3, hδ3_pos
    intro x hx
    have hGx_nbho := hδ3 x hx
    by_cases h_eq : G.map x = u₀
    · change F.map (G.map x) ∈ Nbho (F.map u₀) ε
      rw [h_eq]
      exact ⟨by linarith [hε], by linarith [hε]⟩
    · have hGx_nbhd : G.map x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
      exact hδ1 (G.map x) hGx_nbhd

/-- Function Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be continuous at `u₀` -/
theorem FuncLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= by
  have hg := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_u₀
  have hf := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_f_cont
  have h_f_cont_prop : isContinuousAt ⟨f, Iii⟩ u₀ := ⟨Set.mem_univ _, hf⟩
  have h_comp := FuncLimit.CompSV hg h_f_cont_prop
  exact FuncLimit_to_FuncLimitExpr h_comp

/-- Left Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be left continuous at `u₀` -/
theorem LeftLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₋ g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim₋ (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= by
  have hg := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_u₀
  have hf := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_f_cont
  have h_comp : LeftLimit ⟨f ∘ g, Iii⟩ x₀ (f u₀) := by
    constructor
    · exact ⟨1, zero_lt_one, Set.subset_univ _⟩
    · intro ε hε
      rcases hf.2 ε hε with ⟨δ1, hδ1_pos, hδ1⟩
      rcases hg.2 δ1 hδ1_pos with ⟨δ2, hδ2_pos, hδ2⟩
      use δ2, hδ2_pos
      intro x hx
      have hGx_nbho := hδ2 x hx
      by_cases h_eq : g x = u₀
      · change f (g x) ∈ Nbho (f u₀) ε
        rw [h_eq]
        exact ⟨by linarith [hε], by linarith [hε]⟩
      · have hGx_nbhd : g x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
        exact hδ1 (g x) hGx_nbhd
  exact LeftLimit_to_LeftLimitExpr h_comp

/-- Right Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be right continuous at `u₀` -/
theorem RightLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₊ g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim₊ (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= by
  have hg := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_u₀
  have hf := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_f_cont
  have h_comp : RightLimit ⟨f ∘ g, Iii⟩ x₀ (f u₀) := by
    constructor
    · exact ⟨1, zero_lt_one, Set.subset_univ _⟩
    · intro ε hε
      rcases hf.2 ε hε with ⟨δ1, hδ1_pos, hδ1⟩
      rcases hg.2 δ1 hδ1_pos with ⟨δ2, hδ2_pos, hδ2⟩
      use δ2, hδ2_pos
      intro x hx
      have hGx_nbho := hδ2 x hx
      by_cases h_eq : g x = u₀
      · change f (g x) ∈ Nbho (f u₀) ε
        rw [h_eq]
        exact ⟨by linarith [hε], by linarith [hε]⟩
      · have hGx_nbhd : g x ∈ Nbhd u₀ δ1 := ⟨hGx_nbho.1, hGx_nbho.2, h_eq⟩
        exact hδ1 (g x) hGx_nbhd
  exact RightLimit_to_RightLimitExpr h_comp

/-- Continuity of Function Addition -/
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Add h_F.2 h_G.2⟩

/-- Continuity of Function Subtraction -/
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Sub h_F.2 h_G.2⟩

/-- Continuity of Function Multiplication -/
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Mul h_F.2 h_G.2⟩

/-- Continuity of Function Division -/
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= ⟨⟨⟨h_F.1, h_G.1⟩, h_Gx₀_ne_0⟩, FuncLimit.Div h_F.2 h_G.2 h_Gx₀_ne_0⟩

/-- Continuity of Function Composition -/
theorem Continuity.Comp {F G : Function} {x₀ u₀ : ℝ}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F : isContinuousAt F u₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F ⊙ G) x₀
:= by
  have hu_eq : u₀ = G.map x₀ := FuncLimit_Unique h_u₀ h_G.2
  simp_all only
  constructor
  · exact ⟨h_G.1, h_F.1⟩
  · exact FuncLimit.CompSV h_u₀ h_F
