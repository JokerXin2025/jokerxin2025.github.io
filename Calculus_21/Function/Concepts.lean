/-
    «Calculus_21».Function.Concepts
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
:= by simp_all only [Set.setOf_subset_setOf, and_self, implies_true]

/-- Neighborhood's Equivalent Statement by Absolute Value -/
lemma Nbho_abs {x₀ δ : ℝ}
  : ∀ x, x ∈ Nbho x₀ δ ↔ |x - x₀| < δ
:= by
  intros
  dsimp only [Nbho, mem_setOf_eq]
  rewrite [abs_lt]
  constructor <;> intros <;> constructor <;> linarith

lemma mem_Nbho {x₀ δ x : ℝ}
  : x ∈ Nbho x₀ δ ↔ x₀ - δ < x ∧ x < x₀ + δ
:= by simp only [mem_setOf_eq]

lemma mem_Nbhd {x₀ δ x : ℝ}
  : x ∈ Nbhd x₀ δ ↔ x₀ - δ < x ∧ x < x₀ + δ ∧ x ≠ x₀
:= by simp only [mem_setOf_eq]


/-! # Minimum Point & Maximum Point -/

/-- Minimum Point -/
def isMinimumPoint (F : RFunction) (m : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map m ≤ F.map x

/-- Maximum Point -/
def isMaximumPoint (F : RFunction) (M : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x ≤ F.map M

/-- Minimum Point on a Set -/
def isMinimumPointOn (F : RFunction) (s : Set ℝ) (m : ℝ) : Prop :=
  ∀ x ∈ s, F.map m ≤ F.map x

/-- Maximum Point on a Set -/
def isMaximumPointOn (F : RFunction) (s : Set ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ s, F.map x ≤ F.map M


/-! # Boundedness of RFunction -/

/-- Bounded RFunction -/
def FuncBounded (F : RFunction) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, |F.map x| < M

/-- Upper-Bounded RFunction -/
def FuncUpperBounded (F : RFunction) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x < M

/-- Lower-Bounded RFunction -/
def FuncLowerBounded (F : RFunction) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x > -M

/-- Locally Bounded RFunction -/
def FuncLocalBounded (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ M > 0, ∀ x ∈ F.domain ∩ Nbho x₀ δ, |F.map x| < M

/-- Locally Bounded RFunction (at Negative Infinity) -/
def FuncLocalBounded_NegInfty (F : RFunction) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Iic (-M₁), |F.map x| < M₂

/-- Locally Bounded RFunction (at Positive Infinity) -/
def FuncLocalBounded_PosInfty (F : RFunction) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Ici M₁, |F.map x| < M₂

page_end
