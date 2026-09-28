import «Calculus_21».PolyCalc
import «Calculus_21».Limit.Expr.Init

/-! # Tests for rewriting with polymorphic equalities -/

example {A : LimitValue} {a : ℝ} (h : A =. the a) : A = the a := by
  exact Expr.PolyCalc.PolyEq.eq_of_proper h (by trivial)

example {A : LimitValue} {a : ℝ} (h : A =. the a) :
    some A = some (the a) := by
  poly_rw [h]

example {A : LimitValue} {a : ℝ} (h : A =. the a)
    (p : LimitValue → Prop) (hp : p (the a)) : p A := by
  poly_rw [← h] at hp
  exact hp

example {A B : LimitValue} {a b : ℝ}
    (hA : A =. the a) (hB : B =. the b) :
    (A, B) = (the a, the b) := by
  poly_rw [hA, hB]
