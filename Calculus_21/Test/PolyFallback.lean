import «Calculus_21».Limit.Expr.Init

/-! # Tests for precision fallback relations -/

open LimitValue

example (a : ℝ) : the a =. unknown := by
  exact Expr.PolyCalc.le_unknown _

example : pos_infty =. infty := by
  exact Expr.PolyCalc.le_of_fallbackCore LimitFallbackCore.pos_infty_infty

example : pos_infty =. diverg := by
  exact Expr.PolyCalc.le_trans
    (Expr.PolyCalc.le_of_fallbackCore LimitFallbackCore.pos_infty_infty)
    (Expr.PolyCalc.le_of_fallbackCore LimitFallbackCore.infty_divergence)

example : pos_infty =. unknown := by
  exact Expr.PolyCalc.le_unknown _

example : neg_infty =. unknown := by
  exact Expr.PolyCalc.le_unknown _

example : infty =. unknown := by
  exact Expr.PolyCalc.le_unknown _

example : unknown =. unknown := by
  rfl

example : True := by
  fail_if_success exact (by trivial : unknown =. diverg)
  trivial
