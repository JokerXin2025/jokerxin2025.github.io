/-
    «Calculus_21».Limit.Tactics.Calc
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Cont
set_option linter.style.header false


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
  | gcongr
    all_goals first
    | exact SeqLimitExpr.Add
    | exact FuncLimitExpr.Add
    | exact LeftLimitExpr.Add
    | exact RightLimitExpr.Add
    | exact PosInftyLimitExpr.Add
    | exact NegInftyLimitExpr.Add
    | exact InftyLimitExpr.Add
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

open LimitValue
macro "use_expr" : tactic => `(tactic| apply finite_iff.mp)
macro "expr_calc" : tactic => `(tactic| rw [finite_div_zero (by norm_num)])



example
  : lim₊ (fun x ↦ 1 / ln x ^ 2) 1 =. infty
:= calc
  _  =. lim₊ (fun _ ↦ 1) 1 / lim₊ (fun x ↦ ln x ^ 2) 1
        := by lim_div
  _  =  the 1 / the 0
        := by lim_cont
  _  =. infty
        := by expr_calc

example
  : lim₊ (fun x ↦ ln x - ln x) 0 =. unknown
:= calc
  _  =. lim₊ (fun x ↦ ln x) 0 - lim₊ (fun x ↦ ln x) 0
        := by lim_sub
  _  =  neg_infty - neg_infty
        := by rw [RightLimitExpr.Ln_zero]
  _  =  unknown
        := by rfl

example
  : lim₊ (fun x ↦ ln x - ln x) 0 = the 0
:= by
  use_expr
  calc
  _  =  lim₊ (fun _ ↦ 0) 0
        := by lim_congr_by ring within 1
  _  =. the 0
        := by lim_cont
