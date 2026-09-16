/-
  Minimal reproduction for section variables and instance declarations.

  Compile with:
    lake env lean ExprSimpRepro.lean
-/

import Mathlib

set_option relaxedAutoImplicit false

section

variable (ε : Type)
abbrev Expr := Except ε ℝ

class RealExpr extends Add (Expr ε) where
  add_ok {a b : ℝ} :
    (Except.ok a : Expr ε) + Except.ok b = Except.ok (a + b)

end

section

variable {ε : Type} [RealExpr ε]
variable {a b : ℝ} {A B : Expr ε}

private class AutoExpr (expr : Expr ε)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → expr = Except.ok val

instance eval_ok : AutoExpr (Except.ok a : Expr ε) a True where
  eq := fun _ => rfl

/- This version works: A and B are explicit parameters of the instance. -/
instance eval_add_explicit {A B : Expr ε}
    [h₁ : AutoExpr A a True] [h₂ : AutoExpr B b True] :
    AutoExpr (A + B) (a + b) True where
  eq := by
    intro _
    rw [h₁.eq trivial, h₂.eq trivial, RealExpr.add_ok]

/-
  This version uses the section variables A and B instead.

  With `relaxedAutoImplicit false`, Lean does not turn section variables
  into declaration parameters merely because their names occur in a typeclass
  binder.  In particular, the instance header below does not elaborate as
  the explicit version above.
-/
instance eval_add_section
    [h₁ : AutoExpr A a True] [h₂ : AutoExpr B b True] :
    AutoExpr (A + B) (a + b) True where
  eq := by
    intro _
    rw [h₁.eq trivial, h₂.eq trivial, RealExpr.add_ok]

end
