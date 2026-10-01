/-
    «Calculus_21».Integral.Interval
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Positive
import «Calculus_21».Integral.Cut
set_option linter.style.header false


/-! # Restriction of Riemann Integrals -/

namespace Integral.PositiveIntegral
variable {F : RFunction} {a b c d v : ℝ}

theorem left_integrable (h : PositiveIntegral F a b v)
    (h_ac : a < c) (h_cb : c < b)
  : ∃ w, PositiveIntegral F a c w
:= by
  have hdom : Icc a c ⊆ F.domain := fun x hx =>
    h.domain ⟨hx.1, le_trans hx.2 (le_of_lt h_cb)⟩
  apply (cauchy_iff h_ac hdom).mpr
  intro ε h_ε
  obtain ⟨δ, hδ, h_close⟩ := (cauchy_iff h.1 h.domain).mp ⟨v, h⟩ ε h_ε
  obtain ⟨R, hR⟩ := TaggedPartition.exists_mesh_lt h_cb hδ
  refine ⟨δ, hδ, fun P Q hP hQ => ?_⟩
  have hc := h_close (P.append R) (Q.append R)
    (P.append_mesh_lt R hP hR) (Q.append_mesh_lt R hQ hR)
  simpa only [TaggedPartition.sum_append, add_sub_add_right_eq_sub] using hc

theorem right_integrable (h : PositiveIntegral F a b v)
    (h_ac : a < c) (h_cb : c < b)
  : ∃ w, PositiveIntegral F c b w
:= by
  have hdom : Icc c b ⊆ F.domain := fun x hx =>
    h.domain ⟨le_trans (le_of_lt h_ac) hx.1, hx.2⟩
  apply (cauchy_iff h_cb hdom).mpr
  intro ε h_ε
  obtain ⟨δ, hδ, h_close⟩ := (cauchy_iff h.1 h.domain).mp ⟨v, h⟩ ε h_ε
  obtain ⟨R, hR⟩ := TaggedPartition.exists_mesh_lt h_ac hδ
  refine ⟨δ, hδ, fun P Q hP hQ => ?_⟩
  have hc := h_close (R.append P) (R.append Q)
    (R.append_mesh_lt P hR hP) (R.append_mesh_lt Q hR hQ)
  simpa only [TaggedPartition.sum_append, add_sub_add_left_eq_sub] using hc

theorem subinterval (h : PositiveIntegral F a b v)
    (h_ac : a ≤ c) (h_cd : c < d) (h_db : d ≤ b)
  : ∃ w, PositiveIntegral F c d w
:= by
  have h_ad : a < d := lt_of_le_of_lt h_ac h_cd
  have h_left : ∃ w, PositiveIntegral F a d w := by
    rcases lt_or_eq_of_le h_db with hdb | hdb
    · exact h.left_integrable h_ad hdb
    · subst d
      exact ⟨v, h⟩
  obtain ⟨w, hw⟩ := h_left
  rcases lt_or_eq_of_le h_ac with hac | hac
  · exact hw.right_integrable hac h_cd
  · subst c
    exact ⟨w, hw⟩

/-- If all three integrals exist, their values agree with interval concatenation. -/
theorem split_value {u w : ℝ} (h : PositiveIntegral F a b v)
    (h_left : PositiveIntegral F a c u) (h_right : PositiveIntegral F c b w)
  : v = u + w
:= by
  by_contra hne
  let ε := |v - (u + w)| / 4
  have hε : 0 < ε := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  obtain ⟨δ, hδ, h_sum⟩ := (mesh_iff.mp h).2.2 ε hε
  obtain ⟨δ₁, hδ₁, h_sum₁⟩ := (mesh_iff.mp h_left).2.2 ε hε
  obtain ⟨δ₂, hδ₂, h_sum₂⟩ := (mesh_iff.mp h_right).2.2 ε hε
  obtain ⟨P, hP⟩ := TaggedPartition.exists_mesh_lt h_left.1 (lt_min hδ hδ₁)
  obtain ⟨Q, hQ⟩ := TaggedPartition.exists_mesh_lt h_right.1 (lt_min hδ hδ₂)
  have hp := abs_lt.mp (h_sum₁ P (lt_of_lt_of_le hP (min_le_right _ _)))
  have hq := abs_lt.mp (h_sum₂ Q (lt_of_lt_of_le hQ (min_le_right _ _)))
  have hpq := abs_lt.mp (h_sum (P.append Q)
    (P.append_mesh_lt Q (lt_of_lt_of_le hP (min_le_left _ _))
      (lt_of_lt_of_le hQ (min_le_left _ _))))
  rw [TaggedPartition.sum_append] at hpq
  have hbound : |v - (u + w)| < 3 * ε := abs_lt.mpr ⟨by linarith, by linarith⟩
  dsimp [ε] at hbound
  linarith [abs_nonneg (v - (u + w))]

theorem append {u w : ℝ} (h_left : PositiveIntegral F a c u)
    (h_right : PositiveIntegral F c b w)
  : PositiveIntegral F a b (u + w)
:= by
  have hab := lt_trans h_left.1 h_right.1
  obtain ⟨M₁, hM₁, hb₁⟩ := h_left.bounded
  obtain ⟨M₂, hM₂, hb₂⟩ := h_right.bounded
  let M := M₁ + M₂
  have hM : 0 < M := add_pos hM₁ hM₂
  have hb : ∀ x ∈ Icc a b, |F.map x| ≤ M := by
    intro x hx
    by_cases hxc : x ≤ c
    · have := hb₁ x ⟨hx.1, hxc⟩; dsimp [M]; linarith
    · have := hb₂ x ⟨le_of_not_ge hxc, hx.2⟩; dsimp [M]; linarith
  apply mesh_iff.mpr
  refine ⟨hab, ?_, ?_⟩
  · intro x hx
    by_cases hxc : x ≤ c
    · exact h_left.domain ⟨hx.1, hxc⟩
    · exact h_right.domain ⟨le_of_not_ge hxc, hx.2⟩
  · intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := (mesh_iff.mp h_left).2.2 (ε / 3) (by positivity)
    obtain ⟨δ₂, hδ₂, h₂⟩ := (mesh_iff.mp h_right).2.2 (ε / 3) (by positivity)
    refine ⟨min δ₁ (min δ₂ (ε / (6 * M))),
      lt_min hδ₁ (lt_min hδ₂ (div_pos hε (by positivity))), fun P hP => ?_⟩
    obtain ⟨L, R, hL, hR, herr⟩ := P.cut F (le_of_lt hM) hb h_left.1 h_right.1
    have hl := abs_lt.mp (h₁ L (lt_of_le_of_lt hL
      (lt_of_lt_of_le hP (min_le_left _ _))))
    have hr := abs_lt.mp (h₂ R (lt_of_le_of_lt hR
      (lt_of_lt_of_le hP ((min_le_right _ _).trans (min_le_left _ _)))))
    have hp := lt_of_lt_of_le hP ((min_le_right _ _).trans (min_le_right _ _))
    have hsmall := (lt_div_iff₀ (show 0 < 6 * M by positivity)).mp hp
    have he := abs_le.mp herr
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

end Integral.PositiveIntegral


page_end
