/-
    «Calculus_21».Integral.Comparison
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Positive
set_option linter.style.header false


/-! # Comparing Partitions by the Lengths of Overlapping Cells -/

namespace Integral

/-- The length shared by two closed intervals. -/
noncomputable def overlap (l r u v : ℝ) : ℝ := max 0 (min r v - max l u)

theorem overlap_nonneg (l r u v : ℝ)
  : 0 ≤ overlap l r u v
:= le_max_left _ _

theorem overlap_comm (l r u v : ℝ)
  : overlap l r u v = overlap u v l r
:= by simp only [overlap, min_comm, max_comm]

private theorem overlap_difference {l r u v : ℝ} (hlr : l ≤ r) (huv : u ≤ v)
  : overlap l r u v = min r (max l v) - min r (max l u)
:= by
  unfold overlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem sum_overlap {a b : ℝ} (P : Partition a b) {l r : ℝ}
    (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b)
  : (∑ i : Fin P.count, overlap l r (P.point i.castSucc) (P.point i.succ)) = r - l
:= by
  have h_each : ∀ i : Fin P.count,
      overlap l r (P.point i.castSucc) (P.point i.succ) =
        min r (max l (P.point i.succ)) - min r (max l (P.point i.castSucc)) :=
    fun i => overlap_difference hlr (le_of_lt (P.increasing _ _ (by simp)))
  simp_rw [h_each]
  rw [Partition.sum_differences P.count (fun i => min r (max l (P.point i)))]
  rw [P.last_eq, P.first_eq, max_eq_right (le_trans hlr hrb), min_eq_left hrb,
    max_eq_left hal, min_eq_right hlr]

namespace TaggedPartition
variable {a b : ℝ}

/-- An overlap can contribute only when the two tags are close. -/
theorem tag_dist_of_overlap_pos (P Q : TaggedPartition a b)
    (i : Fin P.count) (j : Fin Q.count)
    (h : 0 < overlap (P.point i.castSucc) (P.point i.succ)
      (Q.point j.castSucc) (Q.point j.succ))
  : |P.tag i - Q.tag j| ≤ P.mesh + Q.mesh
:= by
  have hcross : max (P.point i.castSucc) (Q.point j.castSucc) <
      min (P.point i.succ) (Q.point j.succ) := by
    unfold overlap at h
    have := (lt_max_iff.mp h).resolve_left (lt_irrefl 0)
    linarith
  have h₁ := (lt_of_le_of_lt (le_max_left _ _) hcross).trans_le (min_le_right _ _)
  have h₂ := (lt_of_le_of_lt (le_max_right _ _) hcross).trans_le (min_le_left _ _)
  have hp := P.tag_mem i
  have hq := Q.tag_mem j
  have hwp := P.width_le_mesh i
  have hwq := Q.width_le_mesh j
  unfold Partition.width at hwp hwq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Comparing two sums uses only finite sums of overlap lengths. -/
theorem sum_sub_eq_overlap (P Q : TaggedPartition a b) (F : RFunction)
  : P.sum F - Q.sum F =
      ∑ i, ∑ j, (F.map (P.tag i) - F.map (Q.tag j)) *
        overlap (P.point i.castSucc) (P.point i.succ)
          (Q.point j.castSucc) (Q.point j.succ)
:= by
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · unfold sum
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, sum_overlap Q.toPartition (P.point_mem _).1
      (le_of_lt (P.increasing _ _ (by simp))) (P.point_mem _).2]
    rfl
  · rw [Finset.sum_comm]
    unfold sum
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    simp_rw [overlap_comm (P.point _) (P.point _)]
    rw [sum_overlap P.toPartition (Q.point_mem _).1
      (le_of_lt (Q.increasing _ _ (by simp))) (Q.point_mem _).2]
    rfl

theorem abs_sum_sub_le (P Q : TaggedPartition a b) (F : RFunction) {η : ℝ}
    (_hη : 0 ≤ η)
    (h_close : ∀ i j, 0 < overlap (P.point i.castSucc) (P.point i.succ)
      (Q.point j.castSucc) (Q.point j.succ) →
        |F.map (P.tag i) - F.map (Q.tag j)| ≤ η)
  : |P.sum F - Q.sum F| ≤ η * (b - a)
:= by
  rw [sum_sub_eq_overlap]
  have hterm : ∀ i j,
      |(F.map (P.tag i) - F.map (Q.tag j)) *
        overlap (P.point i.castSucc) (P.point i.succ)
          (Q.point j.castSucc) (Q.point j.succ)| ≤
      η * overlap (P.point i.castSucc) (P.point i.succ)
        (Q.point j.castSucc) (Q.point j.succ) := by
    intro i j
    let w := overlap (P.point i.castSucc) (P.point i.succ)
      (Q.point j.castSucc) (Q.point j.succ)
    have hw : 0 ≤ w := overlap_nonneg _ _ _ _
    by_cases hp : 0 < w
    · rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (h_close i j hp) hw
    · have hz : w = 0 := le_antisymm (le_of_not_gt hp) hw
      change |(_ : ℝ) * w| ≤ η * w
      simp only [hz, mul_zero, abs_zero, le_refl]
  calc
    _ ≤ ∑ i, ∑ j, |(F.map (P.tag i) - F.map (Q.tag j)) *
        overlap (P.point i.castSucc) (P.point i.succ)
          (Q.point j.castSucc) (Q.point j.succ)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, η * overlap (P.point i.castSucc) (P.point i.succ)
        (Q.point j.castSucc) (Q.point j.succ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = η * (b - a) := by
      simp_rw [← Finset.mul_sum]
      congr 1
      have heq : ∀ i : Fin P.count,
          (∑ j : Fin Q.count, overlap (P.point i.castSucc) (P.point i.succ)
            (Q.point j.castSucc) (Q.point j.succ)) = P.width i :=
        fun i => sum_overlap Q.toPartition (P.point_mem _).1
          (le_of_lt (P.increasing _ _ (by simp))) (P.point_mem _).2
      simp_rw [heq]
      exact P.sum_width

end TaggedPartition

theorem PositiveIntegral.of_uniform (F : RFunction) {a b : ℝ} (hab : a < b)
    (hdom : Icc a b ⊆ F.domain)
    (h_uniform : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |x - y| < δ → |F.map x - F.map y| < ε)
  : ∃ v, PositiveIntegral F a b v
:= by
  apply (PositiveIntegral.cauchy_iff hab hdom).mpr
  intro ε hε
  let η := ε / (2 * (b - a))
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hclose⟩ := h_uniform η hη
  refine ⟨δ / 2, by positivity, fun P Q hP hQ => ?_⟩
  have hbound := P.abs_sum_sub_le Q F (le_of_lt hη) (fun i j hij =>
    le_of_lt (hclose _ (P.tag_mem_Icc i) _ (Q.tag_mem_Icc j)
      (lt_of_le_of_lt (P.tag_dist_of_overlap_pos Q i j hij) (by linarith))))
  have heq : η * (b - a) = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  rw [heq] at hbound
  linarith

end Integral


page_end
