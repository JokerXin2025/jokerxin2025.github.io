/-
    «Calculus_21».Limit.Tactics.Congr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.BasicRules
set_option linter.style.header false


/-! # Tactics -/

/-- ## Limit Expression Congruence Substitution By Tactic

    __Usage__ `lim_congr ⟨r : ℝ⟩`

-/
macro "lim_congr" radius:term : tactic => `(tactic| (
  try gcongr
  try apply PolyCalc.pe_of_eq
  first
  | apply FuncLimitExpr.Congr
  | apply LeftLimitExpr.Congr
  | apply RightLimitExpr.Congr
  refine ⟨$radius, ?_, ?_⟩
  · first
    | trivial; done
    | norm_num; done
    | positivity; done
    | linarith; done
    | nlinarith; done
    | fail ""
  simp only [mem_Nbhd, mem_Ioo, and_imp]
  intros
))

macro "lim_congr'" radius:term : tactic => `(tactic| (
  try gcongr
  try apply PolyCalc.pe_of_eq
  first
  | apply FuncLimitExpr.Congr
  | apply LeftLimitExpr.Congr
  | apply RightLimitExpr.Congr
  refine ⟨$radius, ?_, ?_⟩
  · first
    | trivial; done
    | norm_num; done
    | positivity; done
    | linarith; done
    | nlinarith; done
    | fail ""
  intros
))

page_end
