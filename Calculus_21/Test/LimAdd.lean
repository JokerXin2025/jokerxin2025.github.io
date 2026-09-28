import «Calculus_21».Limit.Tactics.Rules

/-! # Tests for local `lim_add` calculation -/

section
variable {f g h i : ℝ → ℝ} {x₀ : ℝ}

-- The original whole-expression behavior remains available.
example : lim x₀ (f + g) =. lim x₀ f + lim x₀ g := by
  lim_add

example : lim₋ x₀ (f + g) =. lim₋ x₀ f + lim₋ x₀ g := by
  lim_add

example : lim₊ x₀ (f + g) =. lim₊ x₀ f + lim₊ x₀ g := by
  lim_add

-- The rule can be applied below an addition on either side.
example : lim x₀ (f + g) + lim x₀ h =.
    (lim x₀ f + lim x₀ g) + lim x₀ h := by
  lim_add

example : lim x₀ h + lim x₀ (f + g) =.
    lim x₀ h + (lim x₀ f + lim x₀ g) := by
  lim_add

-- `gcongr` recursively descends through arbitrarily nested additions.
example : lim x₀ h + (lim x₀ (f + g) + lim x₀ i) =.
    lim x₀ h + ((lim x₀ f + lim x₀ g) + lim x₀ i) := by
  lim_add

-- Registered unary and subtraction congruence rules can surround the change.
example : -(lim x₀ (f + g) + lim x₀ h) =.
    -((lim x₀ f + lim x₀ g) + lim x₀ h) := by
  lim_add

example : (lim x₀ h - lim x₀ (f + g))⁻¹ =.
    (lim x₀ h - (lim x₀ f + lim x₀ g))⁻¹ := by
  lim_add

-- Multiple differing leaves can be transformed in one terminal step.
example : lim x₀ (f + g) + lim x₀ (h + i) =.
    (lim x₀ f + lim x₀ g) + (lim x₀ h + lim x₀ i) := by
  lim_add

-- RFunction, left, and right limits may occur together in one expression.
example : lim x₀ (f + g) + (lim₋ x₀ (h + i) + lim₊ x₀ (f + h)) =.
    (lim x₀ f + lim x₀ g) +
      ((lim₋ x₀ h + lim₋ x₀ i) + (lim₊ x₀ f + lim₊ x₀ h)) := by
  lim_add

-- The intended use is as a terminal tactic in a `calc` step.
example : lim x₀ (f + g) + lim x₀ h =. unknown := by
  calc
    _ =. (lim x₀ f + lim x₀ g) + lim x₀ h := by lim_add
    _ =. unknown := LimitValue.unknown_always _

end

section
variable {a b c d : ℕ → ℝ}

-- RSequence limits are supported by the generalized branch as well.
example : limₙ (a + b) + limₙ (c + d) =.
    (limₙ a + limₙ b) + (limₙ c + limₙ d) := by
  lim_add

-- This also checks that the congruence attributes are available independently.
example (h₁ : limₙ a =. limₙ b) (h₂ : limₙ c =. limₙ d) :
    -(limₙ a - limₙ c) =. -(limₙ b - limₙ d) := by
  gcongr

end
