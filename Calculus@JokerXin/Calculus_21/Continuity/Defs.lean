/-
    Calculus_21.Continuity.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs
set_option linter.style.header false


/-! # Definitions of Function Continuity -/

/-- Continuous at Some Point -/
def isContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ FuncLimit F x₀ (F.map x₀)

/-- Continuous Everywhere -/
abbrev isContinuous (F : Function) : Prop :=
  ∀ x ∈ F.domain, isContinuousAt F x

/-- Continuous on the Interval -/
abbrev isContinuousIn (F : Function) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, isContinuousAt F x

/-- Left Continuous at Some Point -/
def isLeftContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ LeftLimit F x₀ (F.map x₀)

/-- Right Continuous at Some Point -/
def isRightContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ RightLimit F x₀ (F.map x₀)

/-- Continuous on the Closed Interval
    Similar to `isContinuousIn`, but continuity at the endpoints represents right
    continuity and left continuity respectively.
    - Before using it, please make sure that `l < r` -/
abbrev isContinuousInIcc (F : Function) (l r : ℝ) : Prop :=
  isContinuousIn F (Ioo l r)
  ∧ isRightContinuousAt F l
  ∧ isLeftContinuousAt F r


/-! # Lemmas on Function Continuity -/

/-- Continuous Everywhere ⇒ Continuous at Some Point -/
lemma isContinuous_implies_At {F : Function} {x₀ : ℝ}
    (h_cont : isContinuous F) (h_dom : x₀ ∈ F.domain)
  : isContinuousAt F x₀
:= h_cont x₀ h_dom

/-- Continuous on the Interval ⇒ Continuous at Some Point -/
lemma isContinuousIn_implies_At {F : Function} {x₀ : ℝ} {I : Set ℝ}
    (h_cont : isContinuousIn F I) (h_dom : x₀ ∈ I)
  : isContinuousAt F x₀
:= h_cont x₀ h_dom

/-- Continuous at Some Point ⇒ Left Continuous at Some Point -/
lemma isContinuousAt_implies_LeftAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isLeftContinuousAt F x₀
:= ⟨h_cont.1, FuncLimit_toLeft h_cont.2⟩

/-- Continuous at Some Point ⇒ Right Continuous at Some Point -/
lemma isContinuousAt_implies_RightAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isRightContinuousAt F x₀
:= ⟨h_cont.1, FuncLimit_toRight h_cont.2⟩
