/-
    «Calculus_21».Prelude
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import ProofScript
import ProofScript.Mathlib
import Aesop.Frontend.Command
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.DefEqTransformations
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


/-! # Tactics -/

script_macro (recorder := exclusive)
"func_apply" loc?:(ppSpace Lean.Parser.Tactic.location)?
=> `(tactic|
  dsimp only [
    Function.comp_apply,
    Function.const_apply,
    Pi.zero_apply,
    Pi.one_apply,
    Pi.smul_apply,
    Pi.smul_apply',
    Pi.add_apply,
    Pi.neg_apply,
    Pi.sub_apply,
    Pi.mul_apply,
    Pi.inv_apply,
    Pi.div_apply,
    Pi.pow_apply,
    Pi.star_apply
  ] $[$loc?]?
)

macro "func_apply" loc?:(ppSpace Lean.Parser.Tactic.location)?
: tactic => `(tactic|
  dsimp only [
    Function.comp_apply,
    Function.const_apply,
    Pi.zero_apply,
    Pi.one_apply,
    Pi.smul_apply,
    Pi.smul_apply',
    Pi.add_apply,
    Pi.neg_apply,
    Pi.sub_apply,
    Pi.mul_apply,
    Pi.inv_apply,
    Pi.div_apply,
    Pi.pow_apply,
    Pi.star_apply
  ] $[$loc?]?
)


/-! # Supplementary Definitions -/

noncomputable section
def e : ℝ := Real.exp 1
def π : ℝ := Real.pi

def const (C : ℝ) : ℝ → ℝ := Function.const ℝ C
def pow (a : ℝ) : ℝ → ℝ := (Real.rpow · a)
def npow : ℤ → ℝ → ℝ := ZPow.zpow
def ln : ℝ → ℝ := Real.log
def log (a : ℝ) : ℝ → ℝ := (Real.log · / Real.log a)
def sec : ℝ → ℝ := (1 / cos ·)
def csc : ℝ → ℝ := (1 / sin ·)
def coth : ℝ → ℝ := (1 / tanh ·)
def sech : ℝ → ℝ := (1 / cosh ·)
def csch : ℝ → ℝ := (1 / sinh ·)
def arccot : ℝ → ℝ := (π / 2 - arctan ·)
def arcsec : ℝ → ℝ := (arccos ·⁻¹)
def arccsc : ℝ → ℝ := (arcsin ·⁻¹)

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
private lemma recover_pow : pow a = (Real.rpow · a) := rfl
private lemma recover_npow : npow = ZPow.zpow := rfl
private lemma recover_ln : ln = Real.log := rfl
private lemma recover_log : log a = (Real.log · / Real.log a) := rfl
private lemma recover_sec : sec = (1 / cos ·) := rfl
private lemma recover_csc : csc = (1 / sin ·) := rfl
private lemma recover_coth : coth = (1 / tanh ·) := rfl
private lemma recover_sech : sech = (1 / cosh ·) := rfl
private lemma recover_csch : csch = (1 / sinh ·) := rfl
private lemma recover_arccot : arccot = (π / 2 - arctan ·) := rfl
private lemma recover_arcsec : arcsec = (arccos ·⁻¹) := rfl
private lemma recover_arccsc : arccsc = (arcsin ·⁻¹) := rfl

end

macro "recover_form" : tactic => `(tactic|
  dsimp only [
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
)
macro "auto_side_condition" : tactic => `(tactic| (
  repeat any_goals apply And.intro
  all_goals try recover_form
  all_goals try first
  | trivial; done
  | tauto; done
  | positivity; done
  | norm_num; done
  | linarith; done
  | nlinarith; done
  | ring; done
  | field; done
))


/-! # Declarations for Aesop -/

declare_aesop_rule_sets [AutoContinuity]
declare_aesop_rule_sets [AutoDerivability]


/-! # Project Information for ProofScript -/

project_info {
  title := "Calculus_21",
  authors := ["JokerXin"]
}


page_end


script_macro
"exists" data:term "with" cond:term
=> `(tactic|
  refine ⟨$data, $cond, ?_⟩
)

macro "rw_pos" h:term : tactic => `(tactic| rw [if_pos $h])
script_macro "rw_pos" h:term => `(tactic| rw_pos $h)

macro "rw_neg" h:term : tactic => `(tactic| rw [if_neg $h])
script_macro "rw_neg" h:term => `(tactic| rw_neg $h)
