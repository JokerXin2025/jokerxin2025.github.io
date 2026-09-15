/-
    «Calculus_21».Expr.PolyFallback
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.PolyEqual
set_option linter.style.header false


/-- Prove `PolyEqual` goals by bounded search over the constructors of `fallbackCore`. -/
macro "poly_fallback" : tactic => `(tactic|
  solve_by_elim
    (maxDepth := 12) (symm := false) (exfalso := false)
    only [PolyEqual_refl, PolyEqual_trans, PolyEqual.single]
)
