/-
    «Calculus_21».Expr.PolyEqual
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Polymorphic Equality `=.` -/

/-- Polymorphic equality typeclass -/
class PolyExpr (ExprValue : Type) where
  fallbackCore : ExprValue → ExprValue → Prop

section
variable {ExprValue : Type} {A B C : ExprValue} [PolyExpr ExprValue]

/-- Polymorphic equality relation -/
def PolyEqual : ExprValue → ExprValue → Prop := Relation.ReflTransGen <|
  fun A B => Nonempty (PolyExpr.fallbackCore A B)

infix:50 " =. " => PolyEqual

@[refl]
theorem PolyEqual_refl
  : A =. A
:= Relation.ReflTransGen.refl

@[trans]
theorem PolyEqual_trans
  : A =. B → B =. C → A =. C
:= Relation.ReflTransGen.trans

namespace PolyEqual

/-- Promote one core fallback step to polymorphic equality. -/
theorem single (h : PolyExpr.fallbackCore A B) : A =. B :=
  Relation.ReflTransGen.single ⟨h⟩

/-- Lift preservation of core fallback steps to all polymorphic equalities. -/
theorem map {ExprValue' : Type} [PolyExpr ExprValue'] (f : ExprValue → ExprValue')
    (hstep : ∀ {A B}, PolyExpr.fallbackCore A B → f A =. f B)
    (h : A =. B) : f A =. f B := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
      rcases h with ⟨h⟩
      exact PolyEqual_trans ih (hstep h)

end PolyEqual

instance : Trans PolyEqual PolyEqual (@PolyEqual ExprValue _) where
  trans := PolyEqual_trans

instance : Trans PolyEqual Eq (@PolyEqual ExprValue _) where
  trans {A B C} hAB hBC := by grind

instance : Trans Eq PolyEqual (@PolyEqual ExprValue _) where
  trans {A B C} hAB hBC := by grind

end
