/-
    «Calculus_21».PolyCalc
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc.Defs
import «Calculus_21».PolyCalc.AutoReflect
import «Calculus_21».PolyCalc.PolyRw
set_option linter.style.header false


syntax "use_expr" : tactic

script_macro (strategy := true)
"use_expr" => `(tactic| use_expr)
