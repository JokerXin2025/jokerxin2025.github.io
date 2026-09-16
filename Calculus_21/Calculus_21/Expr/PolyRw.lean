/-
    «Calculus_21».Expr.PolyRw
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.EqualIfProper
set_option linter.style.header false


open Lean Parser Tactic

/--
`poly_rw` has the same syntax as `rw`, but converts each supplied `Equal` proof
to an ordinary equality using `ProperClass.eq_of_proper` first.

For now, the required `isProper` proof is discharged with `by trivial`.
-/
macro "poly_rw " cfg:optConfig rules:rwRuleSeq loc:(location)? : tactic => do
  let `(rwRuleSeq| [$rules,*]) := rules
    | Macro.throwUnsupported
  let rules ← rules.getElems.mapM fun rule =>
    match rule with
    | `(rwRule| ← $term:term) =>
        `(rwRule| ← (ProperClass.eq_of_proper $term (by trivial)))
    | `(rwRule| $term:term) =>
        `(rwRule| (ProperClass.eq_of_proper $term (by trivial)))
    | _ => Macro.throwUnsupported
  `(tactic| (
    rw $[$(getConfigItems cfg)]* [$rules,*] $(loc)?
    try rfl
  ))

section

private inductive PolyRwTest where
  | first
  | second

private def PolyRwEqual (a b : PolyRwTest) : Prop := a = b

private instance : ProperClass PolyRwTest PolyRwEqual where
  isProper _ := True
  equal_refl := Eq.refl
  eq_of_proper h _ := h

private example (h : PolyRwEqual PolyRwTest.first PolyRwTest.second) :
    some PolyRwTest.first = some PolyRwTest.second := by
  poly_rw [h]

private example (h : PolyRwEqual PolyRwTest.first PolyRwTest.second)
    (p : PolyRwTest → Prop) (hp : p PolyRwTest.second) : p PolyRwTest.first := by
  poly_rw [← h] at hp
  exact hp

end
