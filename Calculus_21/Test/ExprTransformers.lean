import «Calculus_21».Limit.Expr.GCongr
import «Calculus_21».Limit.Expr.ProperReflect

/-! # Tests for automatic proper-value reflection -/

section
variable {A B C target : LimitValue} {b : ℝ}

example (h : ProperClass.isProper (A + B)) : ProperClass.isProper A := by
  script_proper_reflect

example (h : ProperClass.isProper (A + B)) : ProperClass.isProper B := by
  script_proper_reflect (source := h)

example (h : ProperClass.isProper (A * B)) : ProperClass.isProper A := by
  script_proper_reflect (source := h)

example (h : ProperClass.isProper (A * B)) : ProperClass.isProper B := by
  script_proper_reflect

example (h : ProperClass.isProper (-A)) : ProperClass.isProper A := by
  script_proper_reflect

example (h : ProperClass.isProper (A - B)) : ProperClass.isProper A := by
  script_proper_reflect

example (h : ProperClass.isProper (A - B)) : ProperClass.isProper B := by
  script_proper_reflect

example (h : ProperClass.isProper (A / the b)) : ProperClass.isProper A := by
  script_proper_reflect

example (h : ProperClass.isProper ((A * B + C) / the b)) :
    ProperClass.isProper B := by
  script_proper_reflect

example {cond : Prop} [AutoProperReflect A (ProperClass.isProper target) cond]
    (hcond : cond)
    (h : ProperClass.isProper ((A * B) / the b)) :
    ProperClass.isProper target := by
  script_proper_reflect (discharger := hcond)

example (h : ProperClass.isProper (A + B)) : ∃ a : ℝ, A = the a := by
  script_proper_reflect

example (h : ProperClass.isProper (A / the b)) : b ≠ 0 := by
  script_proper_reflect (source := h)

example (h : ProperClass.isProper (A / the (b ^ 2))) : b ≠ 0 := by
  script_proper_reflect (source := h)

example (h : ProperClass.isProper (A / the (b ^ 2))) : b ^ 2 ≠ 0 := by
  script_proper_reflect (source := h)

example (_h_other : ProperClass.isProper B)
    (h : ProperClass.isProper (A / the (b ^ 2))) : b ^ 2 ≠ 0 := by
  script_proper_reflect

example {cond : Prop} [AutoProperReflect A (ProperClass.isProper target) cond]
    (hcond : cond) (h : ProperClass.isProper A) : ProperClass.isProper target := by
  script_proper_reflect (source := h, discharger := hcond)

example {cond : Prop} [AutoProperReflect A (ProperClass.isProper target) cond]
    (hcond : cond) (h : ProperClass.isProper A) : ProperClass.isProper target := by
  script_proper_reflect (discharger := hcond, source := h)

example (h : ProperClass.isProper (A + B)) : ProperClass.isProper A := by
  have hA : ProperClass.isProper A := by
    script_proper_reflect (source := h)
  exact hA

end
