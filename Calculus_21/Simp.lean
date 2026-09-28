/-
    «Calculus_21».Expr.Simp
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
set_option linter.style.header false

/-
/-! # Real Number Expression Typeclass -/

section
variable (ε : Type)
local macro "Expr" : term => `(Except ε ℝ)

/-- Real Number Expression Typeclass -/
class RealExpr extends
    Add (Expr), Sub (Expr), Mul (Expr), Div (Expr),
    Pow (Expr) (Expr), Neg (Expr), Inv (Expr) where
  add_ok {a b : ℝ} : (the a : Expr) + the b = the (a + b)
  sub_ok {a b : ℝ} : (the a : Expr) - the b = the (a - b)
  mul_ok {a b : ℝ} : (the a : Expr) * the b = the (a * b)
  div_ok {a b : ℝ} : b ≠ 0 → (the a : Expr) / the b = the (a / b)
  pow_ok {a b : ℝ} :
    a > 0 ∨ (a = 0 ∧ b > 0) ∨ (a < 0 ∧ ∃ n : ℤ, b = n)
    → (the a : Expr) ^ (the b : Expr) = the (a ^ b)
  neg_ok {a : ℝ} : -(the a : Expr) = the (-a)
  inv_ok {a : ℝ} : a ≠ 0 → (the a : Expr)⁻¹ = the a⁻¹

end


/-! # Automatic expression evaluation of `RealExpr` -/

variable {ε : Type} [RealExpr ε] {c c₁ c₂ : Prop} {a b : ℝ}
local macro "Expr" : term => `(Except ε ℝ)

private class AutoExpr (expr : Expr)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → expr = the val

instance eval_the : AutoExpr (the a : Expr) a True where
  eq := directly rfl

instance eval_add {A B : Expr}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂] :
    AutoExpr (A + B) (a + b) (c₁ ∧ c₂) where
  eq := by rintro ⟨ha, hb⟩; rw [h₁.eq ha, h₂.eq hb, RealExpr.add_ok]

instance eval_sub {A B : Expr}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂] :
    AutoExpr (A - B) (a - b) (c₁ ∧ c₂) where
  eq := by rintro ⟨ha, hb⟩; rw [h₁.eq ha, h₂.eq hb, RealExpr.sub_ok]

instance eval_mul {A B : Expr}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂] :
    AutoExpr (A * B) (a * b) (c₁ ∧ c₂) where
  eq := by rintro ⟨ha, hb⟩; rw [h₁.eq ha, h₂.eq hb, RealExpr.mul_ok]

instance eval_neg {A : Expr}
    [h : AutoExpr A a c] : AutoExpr (-A) (-a) c where
  eq := by intro ha; rw [h.eq ha, RealExpr.neg_ok]

instance eval_div {A B : Expr}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂] :
    AutoExpr (A / B) (a / b) (c₁ ∧ c₂ ∧ b ≠ 0) where
  eq := by rintro ⟨ha, hb, hn⟩; rw [h₁.eq ha, h₂.eq hb, RealExpr.div_ok hn]

instance eval_inv {A : Expr}
    [h : AutoExpr A a c] : AutoExpr A⁻¹ a⁻¹ (c ∧ a ≠ 0) where
  eq := by rintro ⟨ha, hn⟩; rw [h.eq ha, RealExpr.inv_ok hn]

instance eval_pow {A B : Expr}
    [h₁ : AutoExpr A a c₁] [h₂ : AutoExpr B b c₂] :
    AutoExpr (A ^ B) (a ^ b)
      (c₁ ∧ c₂ ∧ (a > 0 ∨ (a = 0 ∧ b > 0) ∨ (a < 0 ∧ ∃ n : ℤ, b = n))) where
  eq := by
    rintro ⟨ha, hb, hp⟩
    rw [h₁.eq ha, h₂.eq hb, RealExpr.pow_ok hp]

omit [RealExpr ε] in
private lemma autoExpr (A : Expr) [AutoExpr A a c] (h_cond : c)
  : A = the a
:= AutoExpr.eq h_cond


/-- # Expression Simplification
    __Usage__ `expr_simp`
-/
macro "expr_simp" : tactic => `(tactic| (
  intros
  repeat
    rewrite [autoExpr]
    any_goals auto_side_condition
))
-/
