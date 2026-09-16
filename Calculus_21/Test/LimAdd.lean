import «Calculus_21».Limit.Tactics.Calc

/-! # Tests for local `lim_add` calculation -/

section
variable {f g h i : ℝ → ℝ} {x₀ : ℝ}

-- The original whole-expression behavior remains available.
example : lim (f + g) x₀ =. lim f x₀ + lim g x₀ := by
  lim_add

example : lim₋ (f + g) x₀ =. lim₋ f x₀ + lim₋ g x₀ := by
  lim_add

example : lim₊ (f + g) x₀ =. lim₊ f x₀ + lim₊ g x₀ := by
  lim_add

-- The rule can be applied below an addition on either side.
example : lim (f + g) x₀ + lim h x₀ =.
    (lim f x₀ + lim g x₀) + lim h x₀ := by
  lim_add

example : lim h x₀ + lim (f + g) x₀ =.
    lim h x₀ + (lim f x₀ + lim g x₀) := by
  lim_add

-- `gcongr` recursively descends through arbitrarily nested additions.
example : lim h x₀ + (lim (f + g) x₀ + lim i x₀) =.
    lim h x₀ + ((lim f x₀ + lim g x₀) + lim i x₀) := by
  lim_add

-- Registered unary and subtraction congruence rules can surround the change.
example : -(lim (f + g) x₀ + lim h x₀) =.
    -((lim f x₀ + lim g x₀) + lim h x₀) := by
  lim_add

example : (lim h x₀ - lim (f + g) x₀)⁻¹ =.
    (lim h x₀ - (lim f x₀ + lim g x₀))⁻¹ := by
  lim_add

-- Multiple differing leaves can be transformed in one terminal step.
example : lim (f + g) x₀ + lim (h + i) x₀ =.
    (lim f x₀ + lim g x₀) + (lim h x₀ + lim i x₀) := by
  lim_add

-- RFunction, left, and right limits may occur together in one expression.
example : lim (f + g) x₀ + (lim₋ (h + i) x₀ + lim₊ (f + h) x₀) =.
    (lim f x₀ + lim g x₀) +
      ((lim₋ h x₀ + lim₋ i x₀) + (lim₊ f x₀ + lim₊ h x₀)) := by
  lim_add

-- The intended use is as a terminal tactic in a `calc` step.
example : lim (f + g) x₀ + lim h x₀ =. unknown := by
  calc
    _ =. (lim f x₀ + lim g x₀) + lim h x₀ := by lim_add
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
