/-
    «Calculus_21».Limit.Infinitesimal.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs
set_option linter.style.header false


/-! # Definitions of Infinitesimal -/

/-- Infinitesimal -/
abbrev isInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  FuncLimit F x₀ 0

/-- Left Infinitesimal -/
abbrev isLeftInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  LeftLimit F x₀ 0

/-- Right Infinitesimal -/
abbrev isRightInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  RightLimit F x₀ 0


/-! # Properties of Infinitesimal -/

/-- Bounded Function × Infinitesimal -/
theorem Infinitesimal.MulBounded {F₁ F₂ : Function} {x₀ : ℝ}
    (h_bound : FuncBounded F₁)
    (h_ifs : isInfinitesimal F₂ x₀)
    (h_F₁_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ F₁.domain)
  : isInfinitesimal (F₁ * F₂) x₀
:= sorry

/-- Locally Bounded Function × Infinitesimal -/
theorem Infinitesimal.MulLocalBounded {F₁ F₂ : Function} {x₀ δ : ℝ}
    (h_bound : FuncLocalBounded F₁ x₀)
    (h_ifs : isInfinitesimal F₂ x₀)
    (h_F₁_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ F₁.domain)
  : isInfinitesimal (F₁ * F₂) x₀
:= sorry

/-- Infinitesimal + Infinitesimal -/
theorem Infinitesimal.Add {F G : Function} {x₀ : ℝ}
    (h_F : isInfinitesimal F x₀)
    (h_G : isInfinitesimal G x₀)
  : isInfinitesimal (F + G) x₀
:= sorry

/-- Infinitesimal × Infinitesimal -/
theorem Infinitesimal.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isInfinitesimal F x₀)
    (h_G : isInfinitesimal G x₀)
  : isInfinitesimal (F * G) x₀
:= sorry

page_end
