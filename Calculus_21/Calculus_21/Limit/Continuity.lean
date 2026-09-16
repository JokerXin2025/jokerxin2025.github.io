/-
    «Calculus_21».Limit.Continuity
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs.Func
import «Calculus_21».Limit.Rules
set_option linter.style.header false


/-! # Definitions of RFunction's Continuity -/

namespace RFunction

/-- Continuous at Some Point -/
def isContinuousAt (F : RFunction) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ FuncLimit F x₀ (F.map x₀)

/-- Continuous Everywhere -/
def isContinuous (F : RFunction) : Prop :=
  ∀ x ∈ F.domain, isContinuousAt F x

/-- Continuous on the Interval -/
def isContinuousIn (F : RFunction) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, isContinuousAt F x

/-- Left Continuous at Some Point -/
def isLeftContinuousAt (F : RFunction) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ LeftLimit F x₀ (F.map x₀)

/-- Right Continuous at Some Point -/
def isRightContinuousAt (F : RFunction) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ RightLimit F x₀ (F.map x₀)

/-- Continuous on the Closed Interval
    Similar to `isContinuousIn`, but continuity at the endpoints represents right
    continuity and left continuity respectively.
    - Before using it, please **make sure that `l < r`** -/
def isContinuousInIcc (F : RFunction) (l r : ℝ) : Prop :=
  isContinuousIn F (Ioo l r)
  ∧ F.isRightContinuousAt l
  ∧ F.isLeftContinuousAt r

end RFunction
open RFunction


/-! # Core Properties of RFunction's Continuity -/

/-- RFunction Limit Composition (Special Version)
    - This version requires outer function `F` to be continuous at `u₀` -/
theorem FuncLimit.CompSV {x₀ u₀ : ℝ} {F G : RFunction}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F_cont : F.isContinuousAt u₀)
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

theorem Continuity.Congr {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀)
    (h_congr : ∃ δ > 0, Nbho x₀ δ ⊆ G.domain ∧
      ∀ x ∈ Nbho x₀ δ, F.map x = G.map x)
  : G.isContinuousAt x₀
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
theorem Continuity.Neg {F : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀)
  : (-F).isContinuousAt x₀
:= ⟨h_F.1, FuncLimit.Neg h_F.2⟩

/-- Scalar Multiplication of Continuity -/
theorem Continuity.SMul {F : RFunction} {x₀ k : ℝ}
    (h_F : F.isContinuousAt x₀)
  : (k • F).isContinuousAt x₀
:= ⟨h_F.1, FuncLimit.SMul h_F.2⟩

/-- Addition of Continuity -/
theorem Continuity.Add {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀) (h_G : G.isContinuousAt x₀)
  : (F + G).isContinuousAt x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Add h_F.2 h_G.2⟩

/-- Subtraction of Continuity -/
theorem Continuity.Sub {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀) (h_G : G.isContinuousAt x₀)
  : (F - G).isContinuousAt x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Sub h_F.2 h_G.2⟩

/-- Multiplication of Continuity -/
theorem Continuity.Mul {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀) (h_G : G.isContinuousAt x₀)
  : (F * G).isContinuousAt x₀
:= ⟨⟨h_F.1, h_G.1⟩, FuncLimit.Mul h_F.2 h_G.2⟩

/-- Division of Continuity -/
theorem Continuity.Div {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt x₀) (h_G : G.isContinuousAt x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : (F / G).isContinuousAt x₀
:= ⟨⟨⟨h_F.1, h_G.1⟩, h_Gx₀_ne_0⟩, FuncLimit.Div h_F.2 h_G.2 h_Gx₀_ne_0⟩

/-- Composition of Continuity -/
theorem Continuity.Comp {F G : RFunction} {x₀ : ℝ}
    (h_F : F.isContinuousAt (G.map x₀))
    (h_G : G.isContinuousAt x₀)
  : (F ⊙ G).isContinuousAt x₀
:= ⟨⟨h_G.1, h_F.1⟩, FuncLimit.CompSV h_G.2 h_F⟩


/-! # Lemmas on RFunction's Continuity -/

variable {F : RFunction} {l r C : ℝ}

/-- Continuous at Some Point ⇒ Left Continuous at Some Point -/
lemma isContinuousAt_implies_LeftAt {F : RFunction} {x₀ : ℝ}
    (h_cont : F.isContinuousAt x₀)
  : F.isLeftContinuousAt x₀
:= ⟨h_cont.1, FuncLimit.toLeft h_cont.2⟩

/-- Continuous at Some Point ⇒ Right Continuous at Some Point -/
lemma isContinuousAt_implies_RightAt {F : RFunction} {x₀ : ℝ}
    (h_cont : F.isContinuousAt x₀)
  : F.isRightContinuousAt x₀
:= ⟨h_cont.1, FuncLimit.toRight h_cont.2⟩


/-- Minimum Values Theorem -/
theorem Min_Existence
    (h_l_lt_r : l < r)
    (h_cont : F.isContinuousInIcc l r)
  : ∃ m ∈ Icc l r, isMinimumPointOn F (Icc l r) m
:= sorry

/-- Maximum Values Theorem -/
theorem Max_Existence
    (h_l_lt_r : l < r)
    (h_cont : F.isContinuousInIcc l r)
  : ∃ m ∈ Icc l r, isMaximumPointOn F (Icc l r) m
:= sorry

/-- Intermediate Value Theorem -/
theorem Interm_Existence
    (h_l_lt_r : l < r)
    (_h_l_in_dom : l ∈ F.domain)
    (_h_r_in_dom : r ∈ F.domain)
    (h_interm : F.map l < C ∧ C < F.map r
                ∨ F.map r < C ∧ C < F.map l)
    (h_cont : F.isContinuousInIcc l r)
  : ∃ c ∈ Ioo l r, F.map c = C
:= sorry


page_end
