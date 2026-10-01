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

macro "auto_side_condition" : tactic => `(tactic|
  focus
    repeat any_goals apply And.intro
    all_goals try recover_form
    all_goals try first
    | trivial; done
    | tauto; done
    | positivity; done
    | norm_num; done
    | linarith; done
    | nlinarith; done
)

macro "auto_solver" : tactic => `(tactic|
  focus
    repeat any_goals apply And.intro
    all_goals try beta_reduce
    all_goals try dsimp only [id_eq]
    all_goals try recover_form
    all_goals try simp (discharger := positivity) only [
      add_zero, zero_add, mul_one, one_mul, mul_zero, zero_mul,
      sub_self, sub_zero, zero_sub, neg_neg,
      add_neg_cancel, neg_add_cancel, add_sub_cancel_left, add_sub_cancel_right,
      sub_add_cancel, sub_sub_cancel,
      div_one, zero_div, div_zero, div_self,
      inv_zero, inv_one, inv_inv, mul_inv_cancel₀, inv_mul_cancel₀,
      inv_mul_cancel_left₀, mul_inv_cancel_right₀,
      pow_zero, pow_one, zero_pow, one_pow,
      zpow_zero, zpow_one, zpow_natCast,
      abs_zero, abs_one, abs_neg, abs_abs, abs_of_nonneg, abs_of_nonpos,
      sq_abs, abs_pow, abs_inv, abs_mul, abs_div,
      abs_nonneg, sq_nonneg,
      min_self, max_self, min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      Real.sin_zero, Real.cos_zero, Real.tan_zero,
      Real.sin_neg, Real.cos_neg, Real.tan_neg,
      Real.sin_pi, Real.cos_pi, Real.sin_two_pi, Real.cos_two_pi,
      Real.sin_pi_div_two, Real.cos_pi_div_two, Real.tan_pi_div_two,
      Real.sin_pi_div_three, Real.cos_pi_div_three,
      Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four,
      Real.sin_pi_div_six, Real.cos_pi_div_six,
      Real.sin_add_pi, Real.sin_sub_pi, Real.sin_pi_sub,
      Real.cos_add_pi, Real.cos_sub_pi, Real.cos_pi_sub,
      Real.sin_add_two_pi, Real.sin_sub_two_pi,
      Real.cos_add_two_pi, Real.cos_sub_two_pi,
      Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two, Real.sin_pi_div_two_sub,
      Real.cos_add_pi_div_two, Real.cos_sub_pi_div_two, Real.cos_pi_div_two_sub,
      Real.sin_nat_mul_pi, Real.sin_int_mul_pi,
      Real.cos_nat_mul_pi, Real.cos_int_mul_pi,
      Real.sin_add_nat_mul_two_pi, Real.sin_add_int_mul_two_pi,
      Real.sin_sub_nat_mul_two_pi, Real.sin_sub_int_mul_two_pi,
      Real.cos_add_nat_mul_two_pi, Real.cos_add_int_mul_two_pi,
      Real.cos_sub_nat_mul_two_pi, Real.cos_sub_int_mul_two_pi,
      Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq,
      Real.exp_zero, Real.exp_pos, Real.exp_ne_zero,
      Real.log_zero, Real.log_one, Real.log_exp, Real.exp_log,
      Real.exp_log_eq_abs, Real.log_abs, Real.log_neg_eq_log,
      Real.logb_zero, Real.logb_one, Real.logb_abs, Real.logb_abs_base,
      Real.logb_neg_eq_logb, Real.logb_rpow, Real.rpow_logb,
      Real.sqrt_zero, Real.sqrt_one, Real.sqrt_eq_zero_of_nonpos,
      Real.sqrt_sq_eq_abs, Real.sqrt_mul_self_eq_abs,
      Real.sq_sqrt, Real.mul_self_sqrt, Real.sqrt_nonneg,
      Real.sqrt_div_self,
      Real.rpow_zero, Real.rpow_one, Real.one_rpow, Real.zero_rpow,
      Real.rpow_natCast, Real.rpow_intCast, Real.rpow_two, Real.rpow_neg_one,
      Real.rpow_rpow_inv, Real.rpow_inv_rpow,
      Real.pow_rpow_inv_natCast, Real.rpow_inv_natCast_pow,
      Real.arcsin_zero, Real.arcsin_one, Real.arcsin_neg_one, Real.arcsin_neg,
      Real.arccos_zero, Real.arccos_one, Real.arccos_neg_one,
      Real.arctan_zero, Real.arctan_one, Real.arctan_neg,
      Real.sin_arcsin, Real.arcsin_sin, Real.cos_arccos, Real.arccos_cos,
      Real.tan_arctan, Real.arctan_tan,
      Real.sinh_zero, Real.cosh_zero, Real.tanh_zero,
      Real.sinh_neg, Real.cosh_neg, Real.tanh_neg, Real.cosh_abs,
      Real.cosh_sq_sub_sinh_sq,
      Real.arsinh_zero, Real.arsinh_neg, Real.sinh_arsinh, Real.arsinh_sinh,
      Real.arcosh_zero, Real.cosh_arcosh, Real.arcosh_cosh,
      Real.artanh_zero, Real.tanh_artanh, Real.artanh_tanh,
      abs_of_nonneg, abs_of_nonpos, div_self, mul_inv_cancel₀, inv_mul_cancel₀,
      Real.exp_log, Real.sq_sqrt, Real.mul_self_sqrt]
    all_goals try field_simp (discharger :=
      first
      | field_simp_discharge
      | norm_cast; omega
      | auto_side_condition
    )
    all_goals try solve
    | trivial
    | tauto
    | tauto_set
    | positivity
    | norm_num
    | ring
    | linarith
    | nlinarith
)


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
