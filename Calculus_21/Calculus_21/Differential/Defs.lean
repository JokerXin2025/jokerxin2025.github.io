/-
    «Calculus_21».Differential.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs.Func
set_option linter.style.header false


/-! # Definitions of Derivative -/

/-- Derivative -/
def Deriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  FuncLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

abbrev isDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Deriv F x₀ L

abbrev isDerivable (F : RFunction) : Prop :=
  ∀ x ∈ F.domain, isDerivableAt F x

open Classical in
/-- Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def Diff (F : RFunction) : RFunction where
  map := fun x =>
    if h : isDerivableAt F x then
      choose h
    else 0
  domain := { x | isDerivableAt F x }

/-- N-th Order Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def NthDiff (n : ℕ) (F : RFunction) : RFunction :=
  match n with
  | 0     => F
  | n + 1 => Diff (NthDiff n F)

/-- N-th Order Derivative -/
def NthDeriv (n : ℕ) (F : RFunction) (x₀ D : ℝ) : Prop :=
  match n with
  | 0     => F.map x₀ = D ∧ x₀ ∈ F.domain
  | n + 1 => Deriv (NthDiff n F) x₀ D

abbrev isNthDerivableAt (n : ℕ) (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, NthDeriv n F x₀ L

abbrev isNthDerivable (n : ℕ) (F : RFunction) : Prop :=
  ∀ x ∈ F.domain, ∃ L : ℝ, NthDeriv n F x L

/-- Left Derivative -/
def LeftDeriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  LeftLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

abbrev isLeftDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftDeriv F x₀ L

/-- Right Derivative -/
def RightDeriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  RightLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

abbrev isRightDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightDeriv F x₀ L


/-! # Lemmas on N-th Order Differential -/

lemma NthDiff_zero {F : RFunction}
  : NthDiff 0 F = F
:= script rfl

lemma NthDiff_succ {n : ℕ} {F : RFunction}
  : NthDiff (n + 1) F = Diff (NthDiff n F)
:= script rfl

lemma NthDeriv_zero {F : RFunction} {x₀ D : ℝ}
  : NthDeriv 0 F x₀ D ↔ F.map x₀ = D ∧ x₀ ∈ F.domain
:= script trivial

lemma NthDeriv_succ {n : ℕ} {F : RFunction} {x₀ D : ℝ}
  : NthDeriv (n + 1) F x₀ D ↔ Deriv (NthDiff n F) x₀ D
:= script trivial

@theorem NthDeriv_Unique {n : ℕ} {F : RFunction} {x₀ D₁ D₂ : ℝ}
    (h₁ : NthDeriv n F x₀ D₁) (h₂ : NthDeriv n F x₀ D₂) : D₁ = D₂ := by
  cases n with
  | zero => rw [← h₁.1, ← h₂.1]
  | succ n => exact FuncLimit_Unique h₁ h₂

theorem_info NthDeriv_Unique {
  name := "Uniqueness of N-th Order Derivative",
  tag := "uniqueness"
}

page_end
