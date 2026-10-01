/-
    «Calculus_21».Integral.RiemannSum
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Partition
set_option linter.style.header false


/-! # Riemann Sums of RFunctions -/

namespace Integral
namespace TaggedPartition
variable {a b : ℝ}

noncomputable def sum (P : TaggedPartition a b) (F : RFunction) : ℝ :=
  ∑ i, F.map (P.tag i) * P.width i

theorem sum_const (P : TaggedPartition a b) (c : ℝ)
  : P.sum (Constant c) = c * (b - a)
:= by
  change (∑ i, c * P.width i) = c * (b - a)
  rw [← Finset.mul_sum, P.sum_width]

theorem sum_single (hab : a < b) (x : ℝ) (hx : x ∈ Icc a b) (F : RFunction)
  : (single hab x hx).sum F = F.map x * (b - a)
:= by simp only [sum, Fin.sum_univ_one]; rfl

theorem sum_tail (P : TaggedPartition a b) (hn : 1 < P.count) (F : RFunction)
  : P.sum F = F.map (P.tag ⟨0, P.count_pos⟩) * P.width ⟨0, P.count_pos⟩ +
      (P.tail hn).sum F
:= by
  have hsum : ∀ n (f : Fin n → ℝ) (hn : 0 < n),
      (∑ i, f i) = f ⟨0, hn⟩ + ∑ i : Fin (n - 1), f ⟨i.val + 1, by omega⟩ := by
    intro n f hn
    cases n with
    | zero => omega
    | succ n => exact Fin.sum_univ_succ f
  exact hsum P.count (fun i => F.map (P.tag i) * P.width i) P.count_pos

theorem sum_count_one (P : TaggedPartition a b) (hn : P.count = 1) (F : RFunction)
  : P.sum F = F.map (P.tag ⟨0, P.count_pos⟩) * (b - a)
:= by
  have hall : ∀ i : Fin P.count, i = ⟨0, P.count_pos⟩ := by intro i; apply Fin.ext; omega
  have hsum : P.sum F = F.map (P.tag ⟨0, P.count_pos⟩) * P.width ⟨0, P.count_pos⟩ := by
    unfold sum
    apply Finset.sum_eq_single (⟨0, P.count_pos⟩ : Fin P.count)
    · intro i _ hi; exact False.elim (hi (hall i))
    · simp
  rw [hsum]
  congr 1
  unfold Partition.width
  have heq : (⟨0, P.count_pos⟩ : Fin P.count).succ = Fin.last P.count := Fin.ext (by simp; omega)
  rw [heq, P.last_eq]
  exact congrArg (b - ·) P.first_eq

theorem sum_append {c : ℝ} (P : TaggedPartition a b) (Q : TaggedPartition b c)
    (F : RFunction)
  : (P.append Q).sum F = P.sum F + Q.sum F
:= by
  unfold sum
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [append, Fin.addCases_left, Partition.append_width_left]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [append, Fin.addCases_right, Partition.append_width_right]

theorem sum_add (P : TaggedPartition a b) (F G : RFunction)
  : P.sum (F + G) = P.sum F + P.sum G
:= by
  change (∑ i, (F.map (P.tag i) + G.map (P.tag i)) * P.width i) = _
  simp only [add_mul, Finset.sum_add_distrib, sum]

theorem sum_smul (P : TaggedPartition a b) (c : ℝ) (F : RFunction)
  : P.sum (c • F) = c * P.sum F
:= by
  change (∑ i, (c * F.map (P.tag i)) * P.width i) = _
  simp only [mul_assoc, ← Finset.mul_sum, sum]

theorem sum_congr (P : TaggedPartition a b) {F G : RFunction}
    (h_eq : ∀ x ∈ Icc a b, F.map x = G.map x)
  : P.sum F = P.sum G
:= by
  apply Finset.sum_congr rfl
  intro i _
  rw [h_eq _ (P.tag_mem_Icc i)]

theorem sum_mono (P : TaggedPartition a b) {F G : RFunction}
    (h_le : ∀ x ∈ Icc a b, F.map x ≤ G.map x)
  : P.sum F ≤ P.sum G
:= by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (h_le _ (P.tag_mem_Icc i))
    (le_of_lt (P.width_pos i))

theorem abs_sum_le (P : TaggedPartition a b) {F : RFunction} {M : ℝ}
    (h_bound : ∀ x ∈ Icc a b, |F.map x| ≤ M)
  : |P.sum F| ≤ M * (b - a)
:= by
  have h_upper : P.sum F ≤ P.sum (Constant M) :=
    P.sum_mono (fun x hx => (abs_le.mp (h_bound x hx)).2)
  have h_lower : P.sum (Constant (-M)) ≤ P.sum F :=
    P.sum_mono (fun x hx => (abs_le.mp (h_bound x hx)).1)
  rw [P.sum_const] at h_upper h_lower
  exact abs_le.mpr ⟨by linarith, h_upper⟩

theorem sum_replaceTag (P : TaggedPartition a b) (F : RFunction)
    (i : Fin P.count) (x : ℝ)
    (h_x : P.point i.castSucc ≤ x ∧ x ≤ P.point i.succ)
  : (P.replaceTag i x h_x).sum F - P.sum F =
      (F.map x - F.map (P.tag i)) * P.width i
:= by
  classical
  unfold sum
  change (∑ j, F.map (if j = i then x else P.tag j) * P.width j) -
    (∑ j, F.map (P.tag j) * P.width j) = _
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _ hji
    simp [hji]
  · simp

end TaggedPartition


/-! # The Riemann Sum Net -/

open PartitionNet

noncomputable def riemannNet (F : RFunction) {a b : ℝ} (h_ab : a < b)
  : RealNet (TaggedPartition.directedSet h_ab) :=
  ⟨fun P => P.sum F⟩

theorem riemannNet_limit_iff {F : RFunction} {a b value : ℝ} (h_ab : a < b)
  : NetLimit (riemannNet F h_ab) value ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
        P.mesh < δ → |P.sum F - value| < ε
:= by
  constructor
  · intro h ε h_ε
    obtain ⟨P, hP⟩ := h ε h_ε
    exact ⟨P.mesh, P.mesh_pos, fun Q hQ => hP Q (le_of_lt hQ)⟩
  · intro h ε h_ε
    obtain ⟨δ, h_δ, hδ⟩ := h ε h_ε
    obtain ⟨P, hP⟩ := TaggedPartition.exists_mesh_lt h_ab h_δ
    exact ⟨P, fun Q hQ => hδ Q (lt_of_le_of_lt hQ hP)⟩

theorem riemannNet_cauchy_iff {F : RFunction} {a b : ℝ} (h_ab : a < b)
  : NetCauchy (riemannNet F h_ab) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P Q : TaggedPartition a b,
        P.mesh < δ → Q.mesh < δ → |P.sum F - Q.sum F| < ε
:= by
  constructor
  · intro h ε h_ε
    obtain ⟨R, hR⟩ := h ε h_ε
    exact ⟨R.mesh, R.mesh_pos, fun P Q hP hQ => hR P Q (le_of_lt hP) (le_of_lt hQ)⟩
  · intro h ε h_ε
    obtain ⟨δ, h_δ, hδ⟩ := h ε h_ε
    obtain ⟨R, hR⟩ := TaggedPartition.exists_mesh_lt h_ab h_δ
    exact ⟨R, fun P Q hP hQ =>
      hδ P Q (lt_of_le_of_lt hP hR) (lt_of_le_of_lt hQ hR)⟩

end Integral


page_end
