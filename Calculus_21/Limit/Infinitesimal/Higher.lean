/-
    «Calculus_21».Limit.Infinitesimal.Higher
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Infinitesimal.Defs
set_option linter.style.header false


/-! # Definitions of Higher Order Infinitesimal -/

/-- Higher Order Infinitesimal -/
def isHigherInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ FuncLimit (F / G) x₀ 0

/-- Higher Order Left Infinitesimal -/
def isHigherLeftInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ LeftLimit (F / G) x₀ 0

/-- Higher Order Right Infinitesimal -/
def isHigherRightInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ RightLimit (F / G) x₀ 0

page_end
