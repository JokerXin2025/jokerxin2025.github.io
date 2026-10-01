/-
    «Calculus_21».PolyCalc.AutoReflect
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc.Defs
set_option linter.style.header false

variable {ExprValue : Type u} {A : ExprValue} {P : Prop}
variable [PolyCalc ExprValue] [ProperClass ExprValue]


/-! # Automatic Proper-Value Reasoning -/

class AutoProperReflect (A : ExprValue) (P : Prop) (cond : outParam Prop) : Prop where
  reflect : cond → ProperClass.isProper A → P

instance properReflect_refl :
  AutoProperReflect A (ProperClass.isProper A) True where
    reflect := fun _ ↦ id

lemma autoProperReflect {cond : Prop}
    (h_source : ProperClass.isProper A := by assumption)
    [h : AutoProperReflect A P cond]
    (h_cond : cond := by trivial)
  : P
:= h.reflect h_cond h_source

open Lean Elab Tactic Meta in
private def closeProperReflectGoal (hCond? : Option Syntax) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let sourceType ← instantiateMVars localDecl.type
        if sourceType.getAppFn.constName? == some ``ProperClass.isProper then
          let savedState ← saveState
          try
            let source := mkFVar localDecl.fvarId
            let sourceStx ← Term.exprToSyntax source
            let candidateStx ← match hCond? with
              | none =>
                  `(autoProperReflect
                      (h_source := $sourceStx)
                      (h_cond := by trivial))
              | some hCond =>
                  let hCond : Term := ⟨hCond⟩
                  `(autoProperReflect
                      (h_source := $sourceStx)
                      (h_cond := $hCond))
            let candidate ← elabTermEnsuringType candidateStx target
            Term.synthesizeSyntheticMVarsNoPostponing
            let candidate ← instantiateMVars candidate
            if candidate.hasExprMVar then
              throwError "unresolved proper reflection instance"
            goal.assign candidate
            replaceMainGoal []
            return
          catch _ =>
            restoreState savedState
    throwError "script_proper_reflect could not find a suitable proper source"

script_elab
"proper_reflect"
=>
  closeProperReflectGoal none

script_elab
"proper_reflect" "(" "discharger" ":=" disch:term ")"
=>
  closeProperReflectGoal disch

script_macro
"proper_reflect" "(" "source" ":=" src:term ")"
=> `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := by trivial)
)

script_macro
"proper_reflect" "(" "discharger" ":=" disch:term "," "source" ":=" src:term ")"
=> `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := $disch)
)

script_macro
"proper_reflect" "(" "source" ":=" src:term "," "discharger" ":=" disch:term ")"
=> `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := $disch)
)

elab
"proper_reflect"
: tactic =>
  closeProperReflectGoal none

elab
"proper_reflect" "(" "discharger" ":=" disch:term ")"
: tactic =>
  closeProperReflectGoal disch

macro
"proper_reflect" "(" "source" ":=" src:term ")"
: tactic => `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := by trivial)
)

macro
"proper_reflect" "(" "discharger" ":=" disch:term "," "source" ":=" src:term ")"
: tactic => `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := $disch)
)

macro
"proper_reflect" "(" "source" ":=" src:term "," "discharger" ":=" disch:term ")"
: tactic => `(tactic|
  exact autoProperReflect
    (h_source := $src)
    (h_cond := $disch)
)
