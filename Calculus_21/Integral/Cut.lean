/-
    «Calculus_21».Integral.Cut
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.RiemannSum
set_option linter.style.header false


/-! # Cutting a Tagged Partition at an Interior Point -/

namespace Integral.TaggedPartition

private theorem cell_error {F : RFunction} {a b c x M : ℝ}
    (hab : a < b) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hM : ∀ y ∈ Icc a b, |F.map y| ≤ M)
  : |F.map x * (b - a) - (F.map a * (c - a) + F.map c * (b - c))| ≤
      2 * M * (b - a)
:= by
  have h₁ := abs_le.mp (hM x hx)
  have h₂ := abs_le.mp (hM a ⟨le_refl _, le_of_lt hab⟩)
  have h₃ := abs_le.mp (hM c hc)
  have hxlen := mul_le_mul_of_nonneg_right h₁.2 (le_of_lt (sub_pos.mpr hab))
  have hxlen' := mul_le_mul_of_nonneg_right h₁.1 (le_of_lt (sub_pos.mpr hab))
  have halen := mul_le_mul_of_nonneg_right h₂.2 (sub_nonneg.mpr hc.1)
  have halen' := mul_le_mul_of_nonneg_right h₂.1 (sub_nonneg.mpr hc.1)
  have hclen := mul_le_mul_of_nonneg_right h₃.2 (sub_nonneg.mpr hc.2)
  have hclen' := mul_le_mul_of_nonneg_right h₃.1 (sub_nonneg.mpr hc.2)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Splitting one cell changes the sum by at most twice the bound times the mesh. -/
theorem cut {a b c : ℝ} (P : TaggedPartition a b) (F : RFunction) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc a b, |F.map x| ≤ M)
    (hac : a < c) (hcb : c < b)
  : ∃ L : TaggedPartition a c, ∃ R : TaggedPartition c b,
      L.mesh ≤ P.mesh ∧ R.mesh ≤ P.mesh ∧
      |P.sum F - (L.sum F + R.sum F)| ≤ 2 * M * P.mesh
:= by
  generalize hn : P.count = n
  induction n using Nat.strong_induction_on generalizing a b c with
  | h n ih =>
    have hp := P.count_pos
    let i : Fin P.count := ⟨0, hp⟩
    have hi : P.point i.castSucc = a := P.first_eq
    by_cases hone : P.count = 1
    · let L := single hac a ⟨le_refl _, le_of_lt hac⟩
      let R := single hcb c ⟨le_refl _, le_of_lt hcb⟩
      have hm : P.mesh = b - a := by
        have hall : ∀ j : Fin P.count, P.width j = b - a := by
          intro j
          have hj : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          unfold Partition.width
          have hs : i.succ = Fin.last P.count := Fin.ext (by change 1 = P.count; omega)
          rw [hs, P.last_eq, hi]
        exact hall _
      refine ⟨L, R, ?_, ?_, ?_⟩
      · rw [single_mesh, hm]; linarith
      · rw [single_mesh, hm]; linarith
      · rw [P.sum_count_one hone, sum_single, sum_single, hm]
        exact cell_error (lt_trans hac hcb) ⟨le_of_lt hac, le_of_lt hcb⟩
          (P.tag_mem_Icc _) hbound
    have htwo : 1 < P.count := by omega
    let t := P.point i.succ
    let T : TaggedPartition t b := P.tail htwo
    have hat : a < t := by
      have h := P.increasing i.castSucc i.succ (by simp)
      rw [hi] at h
      exact h
    have htb : t < b := T.endpoints_lt
    have hwidth : P.width i = t - a := by unfold Partition.width; rw [hi]
    have htag : P.tag i ∈ Icc a t := ⟨hi.symm.trans_le (P.tag_mem i).1, (P.tag_mem i).2⟩
    let H := single hat (P.tag i) htag
    have hH : H.mesh ≤ P.mesh := by rw [single_mesh, ← hwidth]; exact P.width_le_mesh i
    have hsum : P.sum F = H.sum F + T.sum F := by
      rw [P.sum_tail htwo, sum_single, hwidth]
      rfl
    rcases lt_trichotomy c t with hct | hct | htc
    · let L := single hac a ⟨le_refl _, le_of_lt hac⟩
      let K := single hct c ⟨le_refl _, le_of_lt hct⟩
      let R := K.append T
      have hL : L.mesh ≤ P.mesh := by
        rw [single_mesh]
        have hw := P.width_le_mesh i
        rw [hwidth] at hw
        linarith
      have hK : K.mesh ≤ P.mesh := by
        rw [single_mesh]
        have hw := P.width_le_mesh i
        rw [hwidth] at hw
        linarith
      refine ⟨L, R, hL, K.append_mesh_le T hK (P.tail_mesh_le htwo), ?_⟩
      have herr := cell_error hat ⟨le_of_lt hac, le_of_lt hct⟩ htag
        (fun x hx => hbound x ⟨hx.1, hx.2.trans (le_of_lt htb)⟩)
      have hmul := mul_le_mul_of_nonneg_left (P.width_le_mesh i)
        (show 0 ≤ 2 * M by positivity)
      rw [hwidth] at hmul
      change |P.sum F - (L.sum F + (K.append T).sum F)| ≤ _
      rw [hsum, sum_append, sum_single, sum_single, sum_single]
      have heq : F.map (P.tag i) * (t - a) + T.sum F -
          (F.map a * (c - a) + (F.map c * (t - c) + T.sum F)) =
          F.map (P.tag i) * (t - a) - (F.map a * (c - a) + F.map c * (t - c)) := by ring
      rw [heq]
      exact herr.trans hmul
    · subst c
      refine ⟨H, T, hH, P.tail_mesh_le htwo, ?_⟩
      rw [hsum, sub_self, abs_zero]
      have := P.mesh_pos
      positivity
    · have hbT : ∀ x ∈ Icc t b, |F.map x| ≤ M :=
        fun x hx => hbound x ⟨(le_of_lt hat).trans hx.1, hx.2⟩
      obtain ⟨L, R, hL, hR, herr⟩ := ih (P.count - 1) (by omega)
        T hbT htc hcb rfl
      refine ⟨H.append L, R, H.append_mesh_le L hH (hL.trans (P.tail_mesh_le htwo)),
        hR.trans (P.tail_mesh_le htwo), ?_⟩
      rw [hsum, sum_append]
      have heq : H.sum F + T.sum F - (H.sum F + L.sum F + R.sum F) =
          T.sum F - (L.sum F + R.sum F) := by ring
      rw [heq]
      exact herr.trans (mul_le_mul_of_nonneg_left (P.tail_mesh_le htwo)
        (show 0 ≤ 2 * M by positivity))

end Integral.TaggedPartition


page_end
