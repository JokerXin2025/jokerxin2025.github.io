/-
    Calculus_21.Function.Concepts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Function.Defs
set_option linter.style.header false


/-! # Neighborhood -/

/-- Neighborhood -/
abbrev Nbho (x₀ δ : ℝ) : Set ℝ := { x : ℝ | x₀ - δ < x ∧ x < x₀ + δ }

/-- Deleted Neighborhood -/
abbrev Nbhd (x₀ δ : ℝ) : Set ℝ := { x : ℝ | (x₀ - δ) < x ∧ x < (x₀ + δ) ∧ x ≠ x₀ }

/-- Deleted Neighborhood ⊆ Neighborhood -/
lemma Nbhd_subset_Nbho {x₀ δ : ℝ}
  : Nbhd x₀ δ ⊆ Nbho x₀ δ
:= by simp_all only [Set.setOf_subset_setOf, ne_eq, and_self, implies_true]


/-! # Minimum Point & Maximum Point -/

/-- Minimum Point -/
def isMinimumPoint (F : Function) (m : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x > F.map m

/-- Maximum Point -/
def isMaximumPoint (F : Function) (M : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x < F.map M


/-! # Boundedness of Function -/

/-- Bounded Function -/
def FuncBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, |F.map x| < M

/-- Upper-Bounded Function -/
def FuncUpperBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x < M

/-- Lower-Bounded Function -/
def FuncLowerBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x > -M

/-- Locally Bounded Function -/
def FuncLocalBounded (F : Function) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ M > 0, ∀ x ∈ F.domain ∩ Nbho x₀ δ, |F.map x| < M

/-- Locally Bounded Function (at Negative Infinity) -/
def FuncLocalBounded_NegInfty (F : Function) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Iic (-M₁), |F.map x| < M₂

/-- Locally Bounded Function (at Positive Infinity) -/
def FuncLocalBounded_PosInfty (F : Function) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Ici M₁, |F.map x| < M₂
