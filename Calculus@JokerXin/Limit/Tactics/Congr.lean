import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Rules

open Lean Elab Tactic


/-! ## Tactics -/

/-- ### Limit Expression Congruence Substitution
    __Usage__ `_lim_congr ⟨h : ...⟩ within ⟨r : ℝ⟩`
    - `_lim_congr` uses the given conclusion (`h`'s type) to rewrite the _limit
      expression, a real number `r` provided to locally apply the congruence
-/
macro "_lim_congr" h:term "within" radius:term : tactic => `(tactic| {
  first
  | apply FuncLimitExpr.Congr $radius
  | apply LeftLimitExpr.Congr $radius
  | apply RightLimitExpr.Congr $radius
  intro x h_x
  simp only [Set.mem_Ioo] at h_x
  exact ($h) x (by linarith)
})


/-- ### Limit Expression Congruence Substitution Based on `field`
    __Usage__ `_lim_congr_by_field`
    - `_lim_congr_by_field` uses tactic `field` and the following methods to
      rewrite the _limit:
      - __Forced Reduction__: Reduce the fractional _limit expression without
        providing the proof that the reduced factor is non-zero.
-/
macro "_lim_congr_by_field" : tactic => `(tactic| {
  first
  | apply FuncLimitExpr.Congr 1
  | apply LeftLimitExpr.Congr 1
  | apply RightLimitExpr.Congr 1
  intro x _
  apply Eq.trans
  · first
    | exact FuncLimitExpr.Reduce
    | exact FuncLimitExpr.Reduce'
    | exact LeftLimitExpr.Reduce
    | exact LeftLimitExpr.Reduce'
    | exact RightLimitExpr.Reduce
    | exact RightLimitExpr.Reduce'
    | exact Eq.refl _
  · field
})
