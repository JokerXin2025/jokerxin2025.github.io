/-
    «Calculus_21».PolyCalc.Defs
    leeased under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false

open Relation
variable {ExprValue : Type u} {A B C : ExprValue}


/-! # Abstract Domains -/

class PolyCalc (ExprValue : Type u) where
  fallbackCore : ExprValue → ExprValue → Prop
  unknown : ExprValue

inductive PolyCalc.FallbackStep [PolyCalc ExprValue] : ExprValue → ExprValue → Prop where
| core {A B : ExprValue} : fallbackCore A B → FallbackStep A B
| unknown (A : ExprValue) : FallbackStep A unknown


/-! # Polymorphic Equality `=.` -/

def PolyCalc.PolyEq [PolyCalc ExprValue] : ExprValue → ExprValue → Prop :=
  ReflTransGen (FallbackStep (ExprValue := ExprValue))

infix:50 " =. " => PolyCalc.PolyEq

namespace PolyCalc
variable [PolyCalc ExprValue]

@[refl]
private theorem refl : A =. A := ReflTransGen.refl

@[trans]
private theorem trans : A =. B → B =. C → A =. C := ReflTransGen.trans

/-! The following instances are used to connect `=` and `=.` together in `calc` -/

instance : Trans PolyEq PolyEq (@PolyEq ExprValue _) := ⟨trans⟩

instance : Trans Eq PolyEq (@PolyEq ExprValue _) := ⟨by grind⟩

instance : Trans PolyEq Eq (@PolyEq ExprValue _) := ⟨by grind⟩

theorem pe_unknown (A : ExprValue) : A =. unknown :=
  ReflTransGen.single (FallbackStep.unknown A)

theorem pe_of_fallbackCore (h : fallbackCore A B) : A =. B :=
  ReflTransGen.single (FallbackStep.core h)

theorem pe_of_eq : A = B → A =. B := by intro h; subst h; rfl

end PolyCalc

/-- Proper values are rigid under information loss. -/
class ProperClass (ExprValue : Type u) [PolyCalc ExprValue] where
  isProper : ExprValue → Prop
  rigid : ∀ a b : ExprValue, a =. b → isProper b → a = b

section
variable [PolyCalc ExprValue] [ProperClass ExprValue]

def EqualIfProper (A B : ExprValue) : Prop :=
  ProperClass.isProper B → A =. B

infix:50 " =? " => EqualIfProper

/-- Reintroduce an already known properness condition around a polymorphic equality. -/
theorem EqualIfProper.reintroduce
    (hB : ProperClass.isProper B)
    (h : A =? B)
  : A =. B
:= h hB

open Lean Elab Tactic Meta in
/-- Turn a goal `A =. B` into `A =? B` when `B` is trivially proper. -/
script_elab
"given_proper"
=> withMainContext do
  let goal ← getMainGoal
  let proof ← elabTermForApply (← `(EqualIfProper.reintroduce (by trivial)))
  replaceMainGoal (← goal.apply proof)

open Lean Elab Tactic Meta in
/-- Introduce the properness premise of `A =? B` and make it available in the context. -/
script_elab (intro := [h])
"intro_proper'" h:ident
=> withMainContext do
  let (hProper, goal) ← (← getMainGoal).intro h.getId.eraseMacroScopes
  goal.withContext do
    let hProperStx ← Term.exprToSyntax (mkFVar hProper)
    let proof ← elabTermForApply (← `(EqualIfProper.reintroduce $hProperStx))
    replaceMainGoal (← goal.apply proof)

@[refl]
private theorem EqualIfProper_refl
  : A =? A
:= by
  intro _
  exact PolyCalc.refl

@[trans]
private theorem EqualIfProper_trans
  : A =? B → B =? C → A =? C
:= by
  intro h₁ h₂ h_C
  have hBC : B = C := ProperClass.rigid _ _ (h₂ h_C) h_C
  subst C
  exact h₁ h_C

/-! The following instances are used to connect `=`, `=?` and `=.` together in `calc` -/

instance : Trans EqualIfProper Eq (@EqualIfProper ExprValue _ _) where
  trans {A B C} h₁ h₂ := by grind

instance : Trans Eq EqualIfProper (@EqualIfProper ExprValue _ _) where
  trans {A B C} h₁ h₂ := by grind

instance : Trans EqualIfProper EqualIfProper (@EqualIfProper ExprValue _ _) where
  trans := EqualIfProper_trans

instance : Trans PolyCalc.PolyEq EqualIfProper (@EqualIfProper ExprValue _ _) where
  trans {A B C} hAB hBC := by
    intro hC
    have hBC' : B = C := ProperClass.rigid _ _ (hBC hC) hC
    subst C
    exact hAB

instance : Trans EqualIfProper PolyCalc.PolyEq (@EqualIfProper ExprValue _ _) where
  trans {A B C} hAB hBC := by
    intro hC
    have hBC' : B = C := ProperClass.rigid _ _ hBC hC
    subst C
    exact hAB hC

end
