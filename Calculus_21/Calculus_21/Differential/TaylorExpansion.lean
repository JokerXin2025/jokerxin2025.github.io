/-
    «Calculus_21».Differential.TaylorExpansion
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Infinitesimal.Higher
import «Calculus_21».Limit.L'Hospital
set_option linter.style.header false


/-- Taylor's Polynomial -/
noncomputable def TaylorPolynomial (F : RFunction) (x₀ : ℝ) (N : ℕ) : RFunction :=
  ⟨fun x ↦ ∑ k ∈ range (N + 1),
    (((NthDiff k F).map x₀ / (k)!) * (x - x₀) ^ k), Iii⟩


/-! # Taylor's Formula -/

/-- Taylor's Expansion with Peano's Remainder Term -/
theorem TaylorExpansion_Peano {N : ℕ} {F : RFunction} {x₀ : ℝ}
    (h_N : N > 0)
    (h_deriv : isNthDerivableAt N F x₀)
  : ∃ R : RFunction,
      F = TaylorPolynomial F x₀ N + R
      ∧ isHigherInfinitesimal R ⟨fun x ↦ (x - x₀) ^ N, Iii⟩ x₀
:= sorry

/-- Taylor's Expansion with Lagrange's Remainder Term (for `x < x₀`) -/
theorem TaylorExpansion_Lagrange_left {N : ℕ} {F : RFunction} {x₀ x : ℝ}
    (h_x_lt_x₀ : x < x₀)
    (h_deriv₁ : Icc x x₀ ⊆ (NthDiff N F).domain ∧ (NthDiff N F).isContinuous)
    (h_deriv₂ : Ioo x x₀ ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x x₀,
      F.map x = (TaylorPolynomial F x₀ N).map x +
      (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1))
:= sorry

/-- Taylor's Expansion with Lagrange's Remainder Term (for `x > x₀`) -/
theorem TaylorExpansion_Lagrange_right {N : ℕ} {F : RFunction} {x₀ x : ℝ}
    (h_x_gt_x₀ : x > x₀)
    (h_deriv₁ : Icc x₀ x ⊆ (NthDiff N F).domain ∧ (NthDiff N F).isContinuous)
    (h_deriv₂ : Ioo x₀ x ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x₀ x,
      F.map x = (TaylorPolynomial F x₀ N).map x +
      (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1))
:= sorry

page_end
