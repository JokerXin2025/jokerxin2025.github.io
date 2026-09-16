import «Calculus_21».Limit.Expr.Init

/-! # Tests for automatic `PolyEqual` fallback-path search -/

open LimitValue

example (a : ℝ) : the a =. unknown := by
  poly_fallback

example : pos_infty =. infty := by
  poly_fallback

example : pos_infty =. diverg := by
  poly_fallback

example : pos_infty =. unknown := by
  poly_fallback

example : neg_infty =. unknown := by
  poly_fallback

example : infty =. unknown := by
  poly_fallback

example : unknown =. unknown := by
  poly_fallback

example : True := by
  fail_if_success exact (by poly_fallback : unknown =. diverg)
  trivial

inductive TestValue where
| atom : ℕ → TestValue
| middle
| top

inductive TestFallbackCore : TestValue → TestValue → Prop where
| atom_middle (n : ℕ) : TestFallbackCore (.atom n) .middle
| middle_top : TestFallbackCore .middle .top

instance : PolyExpr TestValue where
  fallbackCore := TestFallbackCore

example (n : ℕ) : TestValue.atom n =. TestValue.top := by
  poly_fallback
