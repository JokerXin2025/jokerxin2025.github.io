/-
    «Calculus_21».Differential.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs.Func
set_option linter.style.header false

script_macro "apply" h:term => `(tactic|
  apply $h
)


/-! # Definitions of Derivative -/

/-- Derivative -/
def Deriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  FuncLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

/-- Enlarging the domain to `Iii` preserves the derivative of the same map. -/
lemma Deriv.total {F : RFunction} {a d : ℝ} (h : Deriv F a d)
    : Deriv (_root_.total F.map) a d := by
  constructor
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    exact ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, sub_ne_zero.mpr ht.2.2⟩
  · exact h.2

namespace RFunction

def isDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Deriv F x₀ L

/-- Two-sided derivability at every point of a set, not a derivative within the set. -/
@[aesop norm unfold (rule_sets := [AutoDerivability])]
def isDerivableIn (F : RFunction) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, F.isDerivableAt x

@[aesop norm unfold (rule_sets := [AutoDerivability])]
def isDerivable (F : RFunction) : Prop :=
  ∀ x ∈ F.domain, isDerivableAt F x

end RFunction

open Classical in
/-- Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def Diff (F : RFunction) : RFunction where
  map := fun x =>
    if h : F.isDerivableAt x then
      choose h
    else 0
  domain := { x | F.isDerivableAt x }

/-- N-th Order Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def NthDiff (n : ℕ) (F : RFunction) : RFunction :=
  match n with
  | 0     => F
  | n + 1 => Diff (NthDiff n F)

/-- N-th Order Derivative, requiring all lower orders to exist at the point. -/
def NthDeriv (n : ℕ) (F : RFunction) (x₀ D : ℝ) : Prop :=
  match n with
  | 0     => F.map x₀ = D ∧ x₀ ∈ F.domain
  | n + 1 => (∃ d, NthDeriv n F x₀ d) ∧ Deriv (NthDiff n F) x₀ D

def isNthDerivableAt (n : ℕ) (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ D : ℝ, NthDeriv n F x₀ D

def isNthDerivable (n : ℕ) (F : RFunction) : Prop :=
  ∀ x ∈ F.domain, ∃ D : ℝ, NthDeriv n F x D

/-- Left Derivative -/
def LeftDeriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  LeftLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

def isLeftDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ D : ℝ, LeftDeriv F x₀ D

/-- Right Derivative -/
def RightDeriv (F : RFunction) (x₀ D : ℝ) : Prop :=
  RightLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ D

def isRightDerivableAt (F : RFunction) (x₀ : ℝ) : Prop :=
  ∃ D : ℝ, RightDeriv F x₀ D


/-! # Lemmas -/

section
variable {F : RFunction} {x₀ D : ℝ}

theorem Deriv.toLeft
  : Deriv F x₀ D → LeftDeriv F x₀ D
:= by sorry

theorem Deriv.toRight
  : Deriv F x₀ D → RightDeriv F x₀ D
:= by sorry

end

/-! # Lemmas on N-th Order Differential -/

section
variable {F : RFunction}

lemma NthDiff_zero
  : NthDiff 0 F = F
:= rfl

lemma NthDiff_succ {n : ℕ}
  : NthDiff (n + 1) F = Diff (NthDiff n F)
:= rfl

lemma NthDeriv_zero {x₀ D : ℝ}
  : NthDeriv 0 F x₀ D ↔ F.map x₀ = D ∧ x₀ ∈ F.domain
:= script trivial

lemma NthDeriv_succ {n : ℕ} {x₀ D : ℝ}
  : NthDeriv (n + 1) F x₀ D ↔
      isNthDerivableAt n F x₀ ∧ Deriv (NthDiff n F) x₀ D
:= script trivial

lemma NthDeriv.lower {n : ℕ} {x₀ D : ℝ}
    (h : NthDeriv (n + 1) F x₀ D) : isNthDerivableAt n F x₀ :=
  h.1

lemma NthDeriv.deriv {n : ℕ} {x₀ D : ℝ}
    (h : NthDeriv (n + 1) F x₀ D) : Deriv (NthDiff n F) x₀ D :=
  h.2

lemma nthDiff_diff (n : ℕ) : NthDiff n (Diff F) = NthDiff (n + 1) F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Diff (NthDiff n (Diff F)) = Diff (NthDiff (n + 1) F)
    rw [ih]

lemma isNthDerivableAt.lower {n : ℕ} {x₀ : ℝ}
    (h : isNthDerivableAt (n + 1) F x₀) : isNthDerivableAt n F x₀ := by
  obtain ⟨d, hd⟩ := h
  exact hd.lower

/-- Existence of a higher derivative implies existence of every lower order. -/
lemma isNthDerivableAt.mono {m n : ℕ} {x₀ : ℝ}
    (h : isNthDerivableAt n F x₀) (hmn : m ≤ n) : isNthDerivableAt m F x₀ := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact h
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst m
      exact h
    · exact ih h.lower (by omega)

lemma NthDeriv.lower_order {m n : ℕ} {x₀ D : ℝ}
    (h : NthDeriv n F x₀ D) (hmn : m ≤ n) : isNthDerivableAt m F x₀ :=
  isNthDerivableAt.mono ⟨D, h⟩ hmn

/-- Cumulative existence implies membership in the unchanged operator's domain.
The converse is not asserted: `NthDiff` does not enforce lower-order existence. -/
lemma isNthDerivableAt.mem_domain {n : ℕ} {x₀ : ℝ}
    (h : isNthDerivableAt n F x₀) : x₀ ∈ (NthDiff n F).domain := by
  obtain ⟨d, hd⟩ := h
  cases n with
  | zero => exact hd.2
  | succ n => exact ⟨d, hd.deriv⟩

lemma NthDeriv.mem_domain {m n : ℕ} {x₀ D : ℝ}
    (h : NthDeriv n F x₀ D) (hmn : m ≤ n) : x₀ ∈ (NthDiff m F).domain :=
  (h.lower_order hmn).mem_domain

lemma isNthDerivable.mono {m n : ℕ}
    (h : isNthDerivable n F) (hmn : m ≤ n)
  : isNthDerivable m F := by
  intro x hx
  exact (isNthDerivableAt.mono (h x hx) hmn)

@theorem NthDeriv_Unique {n : ℕ} {x₀ D₁ D₂ : ℝ}
    (h₁ : NthDeriv n F x₀ D₁) (h₂ : NthDeriv n F x₀ D₂)
  : D₁ = D₂
:= script
  cases_on n
  | zero => rw [← h₁.1, ← h₂.1]
  | succ n => apply h₁.deriv.unique h₂.deriv

theorem_info NthDeriv_Unique {
  name := "Uniqueness of N-th Order Derivative",
  tag := "uniqueness"
}

end


page_end
