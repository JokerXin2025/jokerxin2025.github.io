/-
    «Calculus_21».Prelude
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import ProofScript
import Aesop.Frontend.Command
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option linter.style.header false


/-! # Notations -/

export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici
            mem_Ioo mem_Icc mem_Ioc mem_Ico mem_Iio mem_Iic mem_Ioi mem_Ici
            mem_univ subset_univ mem_setOf_eq nonempty_Icc)
export Finset (range)
export Real (sqrt exp sin cos tan cot sinh cosh tanh arcsin arccos arctan)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n  -- this is only scoped in Mathlib
macro "directly" item:term : term => `(fun _ ↦ $item)


/-! # Supplementary Definitions -/

noncomputable def e : ℝ := Real.exp 1
noncomputable def π : ℝ := Real.pi

def const (C : ℝ) : ℝ → ℝ := Function.const ℝ C
noncomputable def pow (a : ℝ) : ℝ → ℝ := (Real.rpow · a)
noncomputable def npow : ℤ → ℝ → ℝ := ZPow.zpow
noncomputable def ln : ℝ → ℝ := Real.log
noncomputable def log (a : ℝ) : ℝ → ℝ := (Real.log · / Real.log a)
noncomputable def sec : ℝ → ℝ := (1 / cos ·)
noncomputable def csc : ℝ → ℝ := (1 / sin ·)
noncomputable def coth : ℝ → ℝ := (1 / tanh ·)
noncomputable def sech : ℝ → ℝ := (1 / cosh ·)
noncomputable def csch : ℝ → ℝ := (1 / sinh ·)
noncomputable def arccot : ℝ → ℝ := (π / 2 - arctan ·)
noncomputable def arcsec : ℝ → ℝ := (arccos ·⁻¹)
noncomputable def arccsc : ℝ → ℝ := (arcsin ·⁻¹)

section
variable {a b x : ℝ}

lemma mem_Ioi_max_left
  : x ∈ Ioi (max a b) → x ∈ Ioi a
:= (lt_of_le_of_lt (le_max_left a b) ·)

lemma mem_Ioi_max_right
  : x ∈ Ioi (max a b) → x ∈ Ioi b
:= (lt_of_le_of_lt (le_max_right a b) ·)

lemma mem_Iio_neg_max_left
  : x ∈ Iio (-max a b) → x ∈ Iio (-a)
:= (lt_of_lt_of_le · <| neg_le_neg <| le_max_left a b)

lemma mem_Iio_neg_max_right
  : x ∈ Iio (-max a b) → x ∈ Iio (-b)
:= (lt_of_lt_of_le · <| neg_le_neg <| le_max_right a b)

private lemma recover_e : e = exp 1 := rfl
private lemma recover_π : π = Real.pi := rfl
private lemma recover_const : const = Function.const ℝ := rfl
private lemma recover_pow {a : ℝ} : pow a = (Real.rpow · a) := rfl
private lemma recover_npow : npow = ZPow.zpow := rfl
private lemma recover_ln : ln = Real.log := rfl
private lemma recover_log {a : ℝ} : log a = (Real.log · / Real.log a) := rfl
private lemma recover_sec : sec = (1 / cos ·) := rfl
private lemma recover_csc : csc = (1 / sin ·) := rfl
private lemma recover_coth : coth = (1 / tanh ·) := rfl
private lemma recover_sech : sech = (1 / cosh ·) := rfl
private lemma recover_csch : csch = (1 / sinh ·) := rfl
private lemma recover_arccot : arccot = (π / 2 - arctan ·) := rfl
private lemma recover_arcsec : arcsec = (arccos ·⁻¹) := rfl
private lemma recover_arccsc : arccsc = (arcsin ·⁻¹) := rfl

macro "auto_side_condition" : tactic => `(tactic| (
  repeat any_goals apply And.intro
  all_goals try simp_all only [
    recover_e,
    recover_π,
    recover_const,
    recover_pow,
    recover_npow,
    recover_ln,
    recover_log,
    recover_sec,
    recover_csc,
    recover_coth,
    recover_sech,
    recover_csch,
    recover_arccot,
    recover_arcsec,
    recover_arccsc,
  ]
  all_goals try first
  | trivial; done
  | tauto; done
  | positivity; done
  | norm_num; done
  | linarith; done
  | nlinarith; done
))


/-! # Declarations for Aesop -/

declare_aesop_rule_sets [AutoEquation]


/-! # Project Information for ProofScript -/

project_info {
  title := "Calculus_21",
  authors := ["JokerXin"]
}

page_end

/-
open Lean.Elab.Tactic

@[aesop unsafe 50% tactic (rule_sets := [AutoEquation])]
def apply_congArg : TacticM Unit := do
  evalTactic (← `(tactic| apply congrArg the))

@[aesop unsafe 20% tactic (rule_sets := [AutoEquation])]
def exe_field : TacticM Unit := do
  evalTactic (← `(tactic| field))

/-- ## Automatic Equation Prover
    __Usage__ `auto_eq`
-/
macro "auto_eq" : tactic => `(tactic|
  aesop (rule_sets := [AutoEquation]) (
    config := { warnOnNonterminal := false }
  )
)
-/
