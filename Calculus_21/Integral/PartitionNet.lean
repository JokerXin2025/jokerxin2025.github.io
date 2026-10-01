/-
    «Calculus_21».Integral.PartitionNet
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Function.Defs
set_option linter.style.header false


/-! # Directed Sets and Real Nets for Riemann Integration -/

namespace Integral.PartitionNet

/-- A nonempty directed set, with its relation given explicitly. -/
structure DirectedSet where
  Index : Type
  nonempty : Nonempty Index
  rel : Index → Index → Prop
  refl : ∀ i, rel i i
  trans : ∀ {i j k}, rel i j → rel j k → rel i k
  upper : ∀ i j, ∃ k, rel i k ∧ rel j k

/-- A real-valued net. Its indices need not be real numbers. -/
structure RealNet (D : DirectedSet) where
  map : D.Index → ℝ

/-- Convergence uses all indices beyond one threshold. -/
def NetLimit {D : DirectedSet} (A : RealNet D) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ i₀, ∀ i, D.rel i₀ i → |A.map i - L| < ε

def NetConverges {D : DirectedSet} (A : RealNet D) : Prop :=
  ∃ L, NetLimit A L

/-- The real Cauchy condition, without filters or uniform spaces. -/
def NetCauchy {D : DirectedSet} (A : RealNet D) : Prop :=
  ∀ ε > 0, ∃ i₀, ∀ i j,
    D.rel i₀ i → D.rel i₀ j → |A.map i - A.map j| < ε


/-! # Elementary Limit Laws -/

section
variable {D : DirectedSet} {A B : RealNet D} {L L₁ L₂ : ℝ}

theorem NetLimit.unique
    (h₁ : NetLimit A L₁) (h₂ : NetLimit A L₂)
  : L₁ = L₂
:= by
  by_contra h_ne
  have h_pos : 0 < |L₁ - L₂| := abs_pos.mpr (sub_ne_zero.mpr h_ne)
  obtain ⟨i, hi⟩ := h₁ (|L₁ - L₂| / 3) (by positivity)
  obtain ⟨j, hj⟩ := h₂ (|L₁ - L₂| / 3) (by positivity)
  obtain ⟨k, hik, hjk⟩ := D.upper i j
  have h₁k := (abs_lt.mp (hi k hik))
  have h₂k := (abs_lt.mp (hj k hjk))
  rcases le_total L₁ L₂ with h_le | h_le
  · rw [abs_of_nonpos (sub_nonpos.mpr h_le)] at *
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h_le)] at *
    linarith

theorem NetLimit.Const (c : ℝ)
  : NetLimit (D := D) ⟨fun _ => c⟩ c
:= by
  intro ε h_ε
  obtain ⟨i⟩ := D.nonempty
  exact ⟨i, fun _ _ => by simpa using h_ε⟩

theorem NetLimit.Congr
    (h_lim : NetLimit A L)
    (h_eq : ∃ i₀, ∀ i, D.rel i₀ i → A.map i = B.map i)
  : NetLimit B L
:= by
  intro ε h_ε
  obtain ⟨i, hi⟩ := h_lim ε h_ε
  obtain ⟨j, hj⟩ := h_eq
  obtain ⟨k, hik, hjk⟩ := D.upper i j
  refine ⟨k, fun l hkl => ?_⟩
  rw [← hj l (D.trans hjk hkl)]
  exact hi l (D.trans hik hkl)

theorem NetLimit.Add
    (h_A : NetLimit A L₁) (h_B : NetLimit B L₂)
  : NetLimit ⟨fun i => A.map i + B.map i⟩ (L₁ + L₂)
:= by
  intro ε h_ε
  obtain ⟨i, hi⟩ := h_A (ε / 2) (by positivity)
  obtain ⟨j, hj⟩ := h_B (ε / 2) (by positivity)
  obtain ⟨k, hik, hjk⟩ := D.upper i j
  refine ⟨k, fun l hkl => ?_⟩
  have hA := abs_lt.mp (hi l (D.trans hik hkl))
  have hB := abs_lt.mp (hj l (D.trans hjk hkl))
  change |A.map l + B.map l - (L₁ + L₂)| < ε
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem NetLimit.SMul (c : ℝ)
    (h_lim : NetLimit A L)
  : NetLimit ⟨fun i => c * A.map i⟩ (c * L)
:= by
  by_cases h_c : c = 0
  · subst c
    simpa using (NetLimit.Const (D := D) 0)
  intro ε h_ε
  obtain ⟨i, hi⟩ := h_lim (ε / |c|) (div_pos h_ε (abs_pos.mpr h_c))
  refine ⟨i, fun j hij => ?_⟩
  change |c * A.map j - c * L| < ε
  rw [← mul_sub, abs_mul]
  have h := (lt_div_iff₀ (abs_pos.mpr h_c)).mp (hi j hij)
  simpa [mul_comm] using h

theorem NetLimit.Neg (h_lim : NetLimit A L)
  : NetLimit ⟨fun i => -A.map i⟩ (-L)
:= by
  simpa using h_lim.SMul (-1)

theorem NetLimit.Sub
    (h_A : NetLimit A L₁) (h_B : NetLimit B L₂)
  : NetLimit ⟨fun i => A.map i - B.map i⟩ (L₁ - L₂)
:= by
  simpa only [sub_eq_add_neg] using h_A.Add h_B.Neg

theorem NetLimit.Nonneg
    (h_lim : NetLimit A L)
    (h_nonneg : ∃ i₀, ∀ i, D.rel i₀ i → 0 ≤ A.map i)
  : 0 ≤ L
:= by
  by_contra h
  have hL : L < 0 := lt_of_not_ge h
  obtain ⟨i, hi⟩ := h_lim (-L / 2) (by linarith)
  obtain ⟨j, hj⟩ := h_nonneg
  obtain ⟨k, hik, hjk⟩ := D.upper i j
  have h_near := (abs_lt.mp (hi k hik)).2
  have h_pos := hj k hjk
  linarith

theorem NetLimit.Mono
    (h_A : NetLimit A L₁) (h_B : NetLimit B L₂)
    (h_le : ∃ i₀, ∀ i, D.rel i₀ i → A.map i ≤ B.map i)
  : L₁ ≤ L₂
:= by
  have h := (h_B.Sub h_A).Nonneg
  apply sub_nonneg.mp
  apply h
  obtain ⟨i, hi⟩ := h_le
  exact ⟨i, fun j hij => sub_nonneg.mpr (hi j hij)⟩

/-- Only a tail, rather than the entire net, is necessarily bounded. -/
theorem NetLimit.EventuallyBounded (h_lim : NetLimit A L)
  : ∃ M > 0, ∃ i₀, ∀ i, D.rel i₀ i → |A.map i| < M
:= by
  obtain ⟨i, hi⟩ := h_lim 1 zero_lt_one
  refine ⟨|L| + 1, by positivity, i, fun j hij => ?_⟩
  have h := abs_lt.mp (hi j hij)
  exact abs_lt.mpr ⟨by linarith [neg_abs_le L], by linarith [le_abs_self L]⟩

theorem NetLimit.Cauchy (h_lim : NetLimit A L)
  : NetCauchy A
:= by
  intro ε h_ε
  obtain ⟨i, hi⟩ := h_lim (ε / 2) (by positivity)
  refine ⟨i, fun j k hij hik => ?_⟩
  have hj := abs_lt.mp (hi j hij)
  have hk := abs_lt.mp (hi k hik)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end


/-! # Completeness of Real Nets -/

/-- Completeness follows from the supremum of eventual lower bounds.
    No sequential, topological or filter convergence is used. -/
theorem NetCauchy.Converges {D : DirectedSet} {A : RealNet D}
    (h_cauchy : NetCauchy A)
  : NetConverges A
:= by
  let S : Set ℝ := {x | ∃ i, ∀ j, D.rel i j → x ≤ A.map j}
  obtain ⟨i₀, hi₀⟩ := h_cauchy 1 zero_lt_one
  have hS_nonempty : S.Nonempty := by
    refine ⟨A.map i₀ - 1, i₀, fun j hij => ?_⟩
    have h := abs_lt.mp (hi₀ j i₀ hij (D.refl i₀))
    linarith
  have hS_bdd : BddAbove S := by
    refine ⟨A.map i₀ + 1, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hij, hi₀j⟩ := D.upper i i₀
    have h_lower := hi j hij
    have h_upper := abs_lt.mp (hi₀ j i₀ hi₀j (D.refl i₀))
    linarith
  refine ⟨sSup S, ?_⟩
  intro ε h_ε
  obtain ⟨i, hi⟩ := h_cauchy (ε / 2) (by positivity)
  refine ⟨i, fun j hij => ?_⟩
  have h_lower : A.map j - ε / 2 ≤ sSup S := by
    apply le_csSup hS_bdd
    refine ⟨i, fun k hik => ?_⟩
    have h := abs_lt.mp (hi j k hij hik)
    linarith
  have h_upper : sSup S ≤ A.map j + ε / 2 := by
    apply csSup_le hS_nonempty
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hil, hkl⟩ := D.upper i k
    have h_bound := hk l hkl
    have h_near := abs_lt.mp (hi l j hil hij)
    linarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem NetCauchy_iff_NetConverges {D : DirectedSet} {A : RealNet D}
  : NetCauchy A ↔ NetConverges A
:= by
  constructor
  · exact NetCauchy.Converges
  · rintro ⟨L, hL⟩
    exact hL.Cauchy

end Integral.PartitionNet


page_end
