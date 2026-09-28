import «Calculus_21».Limit.Expr.Init

/-! # Tests for limit-expression initialization -/

open LimitValue

example : LimitValue.PowProperPre (LimitValue.finite 2) LimitValue.posInfty := by
  simp [LimitValue.PowProperPre]

example : LimitValue.PowProperPre (LimitValue.finite (1 / 2)) LimitValue.negInfty := by
  norm_num [LimitValue.PowProperPre]

example : LimitValue.PowProperPre LimitValue.posInfty (LimitValue.finite 2) := by
  simp [LimitValue.PowProperPre]

example : LimitValue.PowProperPre LimitValue.posInfty LimitValue.posInfty := by
  simp [LimitValue.PowProperPre]

example (h : Expr.ProperClass.isProper ((the 2) ^ pos_infty)) :
    LimitValue.PowProperPre (the 2) pos_infty :=
  LimitValue.isProper_pow h
