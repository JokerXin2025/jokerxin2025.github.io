/-
    «Calculus_21».Limit.Tactics.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.BasicRules
import «Calculus_21».Limit.Expr.GCongr
set_option linter.style.header false


macro "lim_neg" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Neg
  | exact FuncLimitExpr.Neg
  | exact LeftLimitExpr.Neg
  | exact RightLimitExpr.Neg
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Neg
    | exact FuncLimitExpr.Neg
    | exact LeftLimitExpr.Neg
    | exact RightLimitExpr.Neg
)

macro "lim_inv" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Inv
  | exact FuncLimitExpr.Inv
  | exact LeftLimitExpr.Inv
  | exact RightLimitExpr.Inv
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Inv
    | exact FuncLimitExpr.Inv
    | exact LeftLimitExpr.Inv
    | exact RightLimitExpr.Inv
)

macro "lim_smul" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.SMul
  | exact SeqLimitExpr.SMul'
  | exact FuncLimitExpr.SMul
  | exact FuncLimitExpr.SMul'
  | exact LeftLimitExpr.SMul
  | exact LeftLimitExpr.SMul'
  | exact RightLimitExpr.SMul
  | exact RightLimitExpr.SMul'
  /-| exact PosInftyLimitExpr.SMul
  | exact PosInftyLimitExpr.SMul'
  | exact NegInftyLimitExpr.SMul
  | exact NegInftyLimitExpr.SMul'
  | exact InftyLimitExpr.SMul
  | exact InftyLimitExpr.SMul'-/
  | gcongr
    all_goals first
    | exact SeqLimitExpr.SMul
    | exact SeqLimitExpr.SMul'
    | exact FuncLimitExpr.SMul
    | exact FuncLimitExpr.SMul'
    | exact LeftLimitExpr.SMul
    | exact LeftLimitExpr.SMul'
    | exact RightLimitExpr.SMul
    | exact RightLimitExpr.SMul'
    | exact PosInftyLimitExpr.SMul
    | exact PosInftyLimitExpr.SMul'
    | exact NegInftyLimitExpr.SMul
    | exact NegInftyLimitExpr.SMul'
    | exact InftyLimitExpr.SMul
    | exact InftyLimitExpr.SMul'
)

macro "lim_add" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Add
  | exact FuncLimitExpr.Add
  | exact LeftLimitExpr.Add
  | exact RightLimitExpr.Add
  | exact PosInftyLimitExpr.Add
  | exact NegInftyLimitExpr.Add
  | exact InftyLimitExpr.Add
  | try gcongr
    all_goals first
    | exact SeqLimitExpr.Add
    | exact FuncLimitExpr.Add
    | exact LeftLimitExpr.Add
    | exact RightLimitExpr.Add
    | exact PosInftyLimitExpr.Add
    | exact NegInftyLimitExpr.Add
    | exact InftyLimitExpr.Add
  | fail "`lim_add` failed"
)

macro "lim_sub" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Sub
  | exact FuncLimitExpr.Sub
  | exact LeftLimitExpr.Sub
  | exact RightLimitExpr.Sub
  | exact PosInftyLimitExpr.Sub
  | exact NegInftyLimitExpr.Sub
  | exact InftyLimitExpr.Sub
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Sub
    | exact FuncLimitExpr.Sub
    | exact LeftLimitExpr.Sub
    | exact RightLimitExpr.Sub
    | exact PosInftyLimitExpr.Sub
    | exact NegInftyLimitExpr.Sub
    | exact InftyLimitExpr.Sub
)

macro "lim_mul" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Mul
  | exact FuncLimitExpr.Mul
  | exact LeftLimitExpr.Mul
  | exact RightLimitExpr.Mul
  | exact PosInftyLimitExpr.Mul
  | exact NegInftyLimitExpr.Mul
  | exact InftyLimitExpr.Mul
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Mul
    | exact FuncLimitExpr.Mul
    | exact LeftLimitExpr.Mul
    | exact RightLimitExpr.Mul
    | exact PosInftyLimitExpr.Mul
    | exact NegInftyLimitExpr.Mul
    | exact InftyLimitExpr.Mul
)

macro "lim_div" : tactic => `(tactic|
  first
  | exact SeqLimitExpr.Div
  | exact FuncLimitExpr.Div
  | exact LeftLimitExpr.Div
  | exact RightLimitExpr.Div
  | exact PosInftyLimitExpr.Div
  | exact NegInftyLimitExpr.Div
  | exact InftyLimitExpr.Div
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Div
    | exact FuncLimitExpr.Div
    | exact LeftLimitExpr.Div
    | exact RightLimitExpr.Div
    | exact PosInftyLimitExpr.Div
    | exact NegInftyLimitExpr.Div
    | exact InftyLimitExpr.Div
)


page_end

theorem PosInftyLimitExpr.Sub {f g : ℝ → ℝ}
  : lim pos_infty (f - g) =. lim pos_infty f - lim pos_infty g
:= sorry

/-
open LimitValue
local macro "use_expr" : tactic => `(tactic| apply finite_iff.mp)
local macro "expr_calc" : tactic => `(tactic| rw [finite_div_zero (by norm_num)])



example
  : (lim₊ 1 fun x ↦ 1 / ln x ^ 2) =. infty
:= calc
  _  =. (lim₊ 1 fun _ ↦ 1) / lim₊ 1 fun x ↦ ln x ^ 2
        := by lim_div
  _  =  the 1 / the 0
        := by lim_cont
  _  =. infty
        := by expr_calc

example
  : (lim₊ 0 fun x ↦ ln x - ln x) =. unknown
:= calc
  _  =. (lim₊ 0 fun x ↦ ln x) - lim₊ 0 fun x ↦ ln x
        := by lim_sub
  _  =  neg_infty - neg_infty
        := by rw [RightLimitExpr.Ln_zero]
  _  =  unknown
        := by rfl

example
  : (lim₊ 0 fun x ↦ ln x - ln x) = the 0
:= by
  use_expr
  calc
  _  =  lim₊ 0 fun _ ↦ 0
        := by lim_congr 1; ring
  _  =. the 0
        := by lim_cont
-/
