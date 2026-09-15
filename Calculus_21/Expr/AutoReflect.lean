/-
    «Calculus_21».Expr.AutoReflect
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.EqualIfProper
set_option linter.style.header false

open ProperClass
variable {ExprValue : Type} {A B : ExprValue}
variable {Equal : ExprValue → ExprValue → Prop}
variable [ProperClass ExprValue Equal]


/-! # Automatic Proper-Value Reasoning -/

/-- A path that reflects properness from a root expression to a subexpression. -/
class AutoProperReflect (A B : ExprValue) : Prop where
  reflect : isProper A → isProper B

instance properReflect_refl :
  AutoProperReflect A A where
    reflect := id

lemma autoProperReflect [AutoProperReflect A B]
  : isProper A → isProper B
:= AutoProperReflect.reflect

macro "proper_reflect" target:term "as" h:ident : tactic => `(tactic|
  have $h : isProper $target := autoProperReflect (by assumption)
)

macro "proper_reflect" target:term "from" root:term "as" h:ident : tactic => `(tactic|
  have $h : isProper $target := autoProperReflect $root
)
