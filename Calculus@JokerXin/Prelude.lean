-- import Lean2TeX.Register
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Aesop.Frontend.Command


/- # Notations -/

export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici mem_univ subset_univ)
export Finset (range)
export Real (sqrt exp sin cos tan cot sinh cosh tanh arcsin arccos arctan)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n  -- this is only scoped in Mathlib
macro "the" : term => `(some)
macro "directly" id:ident : term => `(fun _ ↦ $id)


/- # Supplementary Definitions -/

noncomputable def e : ℝ := Real.exp 1
noncomputable def π : ℝ := Real.pi

def const (C : ℝ) : ℝ → ℝ := Function.const ℝ C
noncomputable abbrev npow (n : ℤ) : ℝ → ℝ := DivInvMonoid.zpow n
noncomputable def pow (a : ℝ) : ℝ → ℝ := (Real.rpow · a)
noncomputable def ln : ℝ → ℝ := Real.log
noncomputable def log : ℝ → ℝ → ℝ := (fun a x ↦ Real.log x / Real.log a)
noncomputable def sec : ℝ → ℝ := (1 / cos ·)
noncomputable def csc : ℝ → ℝ := (1 / sin ·)
noncomputable def coth : ℝ → ℝ := (1 / tanh ·)
noncomputable def sech : ℝ → ℝ := (1 / cosh ·)
noncomputable def csch : ℝ → ℝ := (1 / sinh ·)
noncomputable def arccot : ℝ → ℝ := (π / 2 - arctan ·)
noncomputable def arcsec : ℝ → ℝ := (fun x ↦ arccos (1 / x))
noncomputable def arccsc : ℝ → ℝ := (fun x ↦ arcsin (1 / x))


/- # Declarations for Aesop -/

declare_aesop_rule_sets [
  ExprInitialize,
  ExprConvert,
  ExprSimplify,
  AutoEquation,
  LimitSimplify,
  LimitEquivalent
]
