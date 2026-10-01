/-
    «Calculus_21».Differential.Tactics.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Rules
set_option linter.style.header false


macro "deriv_neg" : tactic => `(tactic|
  first
  | exact DerivExpr.Neg
  | exact LeftDerivExpr.Neg
  | exact RightDerivExpr.Neg
  | gcongr
    all_goals first
    | exact DerivExpr.Neg
    | exact LeftDerivExpr.Neg
    | exact RightDerivExpr.Neg
)

macro "deriv_inv" : tactic => `(tactic|
  first
  | exact DerivExpr.Inv
  | exact LeftDerivExpr.Inv
  | exact RightDerivExpr.Inv
  | gcongr
    all_goals first
    | exact DerivExpr.Inv
    | exact LeftDerivExpr.Inv
    | exact RightDerivExpr.INv
)

macro "deriv_mspow" : tactic => `(tactic|
  first
  | exact DerivExpr.MSPow
  | exact LeftDerivExpr.MSPow
  | exact RightDerivExpr.MSPow
  | gcongr
    all_goals first
    | exact DerivExpr.MSPow
    | exact LeftDerivExpr.MSPow
    | exact RightDerivExpr.MSPow
)

macro "deriv_smul" : tactic => `(tactic|
  first
  | exact DerivExpr.SMul
  | exact DerivExpr.SMul'
  | exact LeftDerivExpr.SMul
  | exact LeftDerivExpr.SMul'
  | exact RightDerivExpr.SMul
  | exact RightDerivExpr.SMul'
  | gcongr
    all_goals first
    | exact DerivExpr.SMul
    | exact DerivExpr.SMul'
    | exact LeftDerivExpr.SMul
    | exact LeftDerivExpr.SMul'
    | exact RightDerivExpr.SMul
    | exact RightDerivExpr.SMul'
)

macro "deriv_add" : tactic => `(tactic|
  first
  | exact DerivExpr.Add
  | exact LeftDerivExpr.Add
  | exact RightDerivExpr.Add
  | try gcongr
    all_goals first
    | exact DerivExpr.Add
    | exact LeftDerivExpr.Add
    | exact RightDerivExpr.Add
  | fail "`lim_add` failed"
)

macro "deriv_sub" : tactic => `(tactic|
  first
  | exact DerivExpr.Sub
  | exact LeftDerivExpr.Sub
  | exact RightDerivExpr.Sub
  | gcongr
    all_goals first
    | exact DerivExpr.Sub
    | exact LeftDerivExpr.Sub
    | exact RightDerivExpr.Sub
)

macro "deriv_mul" : tactic => `(tactic|
  first
  | exact DerivExpr.Mul
  | exact LeftDerivExpr.Mul
  | exact RightDerivExpr.Mul
  | gcongr
    all_goals first
    | exact DerivExpr.Mul
    | exact LeftDerivExpr.Mul
    | exact RightDerivExpr.Mul
)

macro "deriv_div" : tactic => `(tactic|
  first
  | exact DerivExpr.Div
  | exact LeftDerivExpr.Div
  | exact RightDerivExpr.Div
  | gcongr
    all_goals first
    | exact DerivExpr.Div
    | exact LeftDerivExpr.Div
    | exact RightDerivExpr.Div
)

macro "deriv_comp" : tactic => `(tactic|
  first
  | exact DerivExpr.Comp
  | exact LeftDerivExpr.Comp
  | exact RightDerivExpr.Comp
  | gcongr
    all_goals first
    | exact DerivExpr.Comp
    | exact LeftDerivExpr.Comp
    | exact RightDerivExpr.Comp
)


page_end
