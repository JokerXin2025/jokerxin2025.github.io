/-
    «Calculus_21».PolyCalc.PolyRw
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc.Defs
set_option linter.style.header false


namespace PolyCalc.PolyEq
variable {ExprValue : Type u} {A B : ExprValue}
variable [PolyCalc ExprValue] [ProperClass ExprValue]

/-- A polymorphic equality ending at a proper value is an ordinary equality. -/
theorem eq_of_proper (h : A =. B) (hB : ProperClass.isProper B) : A = B :=
  ProperClass.rigid A B h hB

end PolyCalc.PolyEq


open Lean Parser Tactic

/--
`poly_rw` has the same syntax as `rw`, but first turns every supplied
polymorphic equality into an ordinary equality. The right-hand side of each
rule must be provably proper by `trivial`.
-/
macro "poly_rw" cfg:optConfig rules:rwRuleSeq loc:(location)? : tactic => do
  let `(rwRuleSeq| [$rules,*]) := rules
    | Macro.throwUnsupported
  let rules ← rules.getElems.mapM fun rule =>
    match rule with
    | `(rwRule| ← $term:term) =>
        `(rwRule| ← (PolyCalc.PolyEq.eq_of_proper $term (by trivial)))
    | `(rwRule| $term:term) =>
        `(rwRule| (PolyCalc.PolyEq.eq_of_proper $term (by trivial)))
    | _ => Macro.throwUnsupported
  `(tactic| (
    rw $[$(getConfigItems cfg)]* [$rules,*] $(loc)?
    try rfl
  ))

script_macro (recorder := exclusive)
"poly_rw" cfg:optConfig rules:rwRuleSeq loc:(location)? => do
  let `(rwRuleSeq| [$rules,*]) := rules
    | Macro.throwUnsupported
  let rules ← rules.getElems.mapM fun rule =>
    match rule with
    | `(rwRule| ← $term:term) =>
        `(rwRule| ← (PolyCalc.PolyEq.eq_of_proper $term (by trivial)))
    | `(rwRule| $term:term) =>
        `(rwRule| (PolyCalc.PolyEq.eq_of_proper $term (by trivial)))
    | _ => Macro.throwUnsupported
  `(tactic| (
    rw $[$(getConfigItems cfg)]* [$rules,*] $(loc)?
    try rfl
  ))
