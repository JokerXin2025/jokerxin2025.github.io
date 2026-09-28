import «Calculus_21».Prelude

example (f g : ℝ → ℝ) (x : ℝ) :
    (f⁻¹ + g * f) x = (f x)⁻¹ + g x * f x := by
  fun_dsimp

example (f : ℝ → ℝ) (x x₀ : ℝ) (hx : f x ≠ 0) (hx₀ : f x₀ ≠ 0) :
    (f⁻¹ x - f⁻¹ x₀) / (x - x₀)
      = -((f x - f x₀) / (x - x₀)) / (f x * f x₀) := by
  fun_dsimp
  guard_target =ₛ
    ((f x)⁻¹ - (f x₀)⁻¹) / (x - x₀)
      = -((f x - f x₀) / (x - x₀)) / (f x * f x₀)
  field_simp
  ring

example (P : ℝ → Prop) (f : ℝ → ℝ) (x : ℝ) (h : P (f⁻¹ x)) : P ((f x)⁻¹) := by
  fun_dsimp at h ⊢
  exact h
