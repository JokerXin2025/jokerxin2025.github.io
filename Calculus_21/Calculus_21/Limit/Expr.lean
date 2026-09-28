/-
    «Calculus_21».Limit.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
import «Calculus_21».Limit.Expr.GCongr
import «Calculus_21».Limit.Expr.ProperReflect
import «Calculus_21».Limit.Expr.BasicRules
import «Calculus_21».Limit.Expr.Elementary
import «Calculus_21».Limit.Expr.Subst
set_option linter.style.header false


macro_rules
| `(tactic| use_expr) => `(tactic|
  first
  | refine SeqLimit.fromSeqLimitExpr ?side ?calculation
  | refine FuncLimit.fromFuncLimitExpr ?side ?calculation
  | refine LeftLimit.fromLeftLimitExpr ?side ?calculation
  | refine RightLimit.fromRightLimitExpr ?side ?calculation
  | refine PosInftyLimit.fromPosInftyLimitExpr ?side ?calculation
  | refine NegInftyLimit.fromNegInftyLimitExpr ?side ?calculation
  | refine InftyLimit.fromInftyLimitExpr ?side ?calculation
)
