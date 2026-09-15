/-
    «Calculus_21».Limit.Tactics.Congr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false


/-! # Tactics -/

/-- ## Limit Expression Congruence Substitution

    __Usage__ `lim_congr ⟨h : ...⟩ within ⟨r : ℝ⟩`

    - `lim_congr` uses the given conclusion (`h`'s type) to rewrite the limit
      expression, a real number `r` provided to locally apply the congruence
-/
macro "lim_congr" h:term "within" radius:term : tactic => `(tactic| {
  first
  | apply FuncLimitExpr.Congr
  | apply LeftLimitExpr.Congr
  | apply RightLimitExpr.Congr
  refine ⟨$radius, ?_⟩
  constructor
  · first
    | norm_num
    | positivity
    | linarith
    | nlinarith
    done
  · intro x h_x
    simp only [mem_Nbhd, mem_Ioo] at h_x
    exact $h x (by linarith)
})

/-- ## Limit Expression Congruence Substitution By Tactic

    __Usage__ `lim_congr by ⟨T : tactic⟩ within ⟨r : ℝ⟩`

    - `lim_congr by` uses specific tactic `T` to rewrite the limit expression.
-/
macro "lim_congr_by" tacticA:tactic "within" radius:term : tactic => `(tactic| {
  first
  | apply FuncLimitExpr.Congr
  | apply LeftLimitExpr.Congr
  | apply RightLimitExpr.Congr
  refine ⟨$radius, ?_⟩
  constructor
  · first
    | norm_num
    | positivity
    | linarith
    | nlinarith
    done
  · simp only [mem_Nbhd, mem_Ioo, and_imp]
    intros
    $tacticA
    done
})

page_end
