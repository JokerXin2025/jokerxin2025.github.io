import «Calculus_21».Limit.Expr.GCongr

/-! # Tests for abstract transformers and proper backward reasoning -/

open ProperClass

section
variable {A A' B B' target : LimitValue} {b : ℝ}
variable {x y z : LimitValue.Outcome}

example (hA : A =. A') (hB : B =. B') : A * B =. A' * B' := by
  gcongr

example (h : isProper (A * B)) : isProper A := by
  proper_reflect A from h as hA
  exact hA

example (h : isProper (A / the b)) : isProper A ∧ b ≠ 0 :=
  ProperClass.isProper_div_finite h

example [AutoProperReflect A target] (h : isProper ((A * B) / the b)) :
    isProper target := by
  proper_reflect target from h as htarget
  exact htarget

example (hx : x ∈ LimitValue.gamma A) (hy : y ∈ LimitValue.gamma B)
    (hxyz : LimitValue.Outcome.Mul x y z) : z ∈ LimitValue.gamma (A * B) := by
  change x ∈ Expr.Concretization.Gamma A at hx
  change y ∈ Expr.Concretization.Gamma B at hy
  change z ∈ Expr.Concretization.Gamma (A * B)
  exact Expr.Transformer.binary_sound
    (op := fun X Y : LimitValue => X * Y)
    (concrete := LimitValue.Outcome.Mul) hx hy hxyz

example (h : isProper (A / the b)) : isProper A ∧ b ≠ 0 := by
  proper_backward h with (fun X : LimitValue => X / the b) as hpre
  exact hpre

example (h : isProper A⁻¹) : LimitValue.InvProperPre A :=
  LimitValue.isProper_inv h

example (h : isProper (A ^ B)) : LimitValue.PowProperPre A B :=
  LimitValue.isProper_pow h

example (hA : A =. A') (hB : B =. B') : A ^ B =. A' ^ B' := by
  gcongr

end
