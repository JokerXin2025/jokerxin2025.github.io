/-
    «Calculus_21».Limit.Expr.ProperReflect
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false


namespace LimitValue.isProper
variable {A B : LimitValue} {b : ℝ} {n : ℕ} {P : Prop} {cond₁ : Prop}

private lemma add_left
  : (A + B).isProper → A.isProper
:= by cases A <;> cases B <;> simp only [isProper, imp_self, implies_true]

private lemma add_right
  : (A + B).isProper → B.isProper
:= by cases A <;> cases B <;> simp only [isProper, imp_self, implies_true]

private lemma mul_left
  : (A * B).isProper → A.isProper
:= by
  cases A <;> cases B
  <;> simp only [isProper, HMul.hMul, Mul.mul, imp_self, implies_true]
  <;> grind

private lemma mul_right
  : (A * B).isProper → B.isProper
:= by
  cases A <;> cases B
  <;> simp only [isProper, HMul.hMul, Mul.mul, imp_self, implies_true]
  <;> grind

private lemma neg
  : (-A).isProper → A.isProper
:= by cases A <;> simp only [isProper, imp_self]

private lemma inv_finite
  : (the b)⁻¹.isProper → b ≠ 0
:= by
  intro h hb
  subst b
  change (the 0)⁻¹.isProper at h
  simp [Inv.inv, isProper] at h

private instance
    [h : AutoProperReflect A P cond₁]
  : AutoProperReflect (A + B) P cond₁
:= ⟨(h.reflect · ·.add_left)⟩

private instance
    [h : AutoProperReflect B P cond₁]
  : AutoProperReflect (A + B) P cond₁
:= ⟨(h.reflect · ·.add_right)⟩

private instance
    [h : AutoProperReflect A P cond₁]
  : AutoProperReflect (A * B) P cond₁
:= ⟨(h.reflect · ·.mul_left)⟩

private instance
    [h : AutoProperReflect B P cond₁]
  : AutoProperReflect (A * B) P cond₁
:= ⟨(h.reflect · ·.mul_right)⟩

private instance
    [h : AutoProperReflect A P cond₁]
  : AutoProperReflect (-A) P cond₁
:= ⟨(h.reflect · ·.neg)⟩

private instance
    [h : AutoProperReflect A P cond₁]
  : AutoProperReflect (A - B) P cond₁
:= ⟨(h.reflect · ·.add_left)⟩

private instance
    [h : AutoProperReflect B P cond₁]
  : AutoProperReflect (A - B) P cond₁
:= ⟨(h.reflect · ·.add_right.neg)⟩

private instance
    [h : AutoProperReflect A P cond₁]
  : AutoProperReflect (A / the b) P cond₁
:= ⟨(h.reflect · ·.mul_left)⟩

private instance
    [h : AutoProperReflect (the b)⁻¹ P cond₁]
  : AutoProperReflect (A / the b) P cond₁
:= ⟨(h.reflect · ·.mul_right)⟩

private instance
  : AutoProperReflect A (∃ a : ℝ, A =. the a) True
:= ⟨directly isProper.getEqual⟩

private instance
  : AutoProperReflect A (∃ a : ℝ, A = the a) True
:= ⟨directly isProper.getEqual!⟩

private instance
  : AutoProperReflect (the b)⁻¹ (b ≠ 0) True
:= ⟨directly inv_finite⟩

private instance
  : AutoProperReflect (the (b ^ n))⁻¹ (b ≠ 0) (n ≠ 0)
:= ⟨fun hn h hb ↦ inv_finite h (by simp [hb, hn])⟩

end LimitValue.isProper
