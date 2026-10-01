/-
    «Calculus_21».Integral.NewtonLeibniz
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Positive
import «Calculus_21».Differential.MeanValue
set_option linter.style.header false


/-! # Newton-Leibniz from Tagged Riemann Sums -/

namespace Integral

private theorem deriv_continuous {G : RFunction} {x d : ℝ}
    (hx : x ∈ G.domain) (hd : Deriv G x d)
  : G.isContinuousAt x
:= by
  refine ⟨hx, ?_, ?_⟩
  · obtain ⟨δ, hδ, hdom⟩ := hd.1
    exact ⟨δ, hδ, fun y hy => (hdom hy).1.1.1⟩
  · intro ε hε
    obtain ⟨r, hr, hnear⟩ := hd.2 1 zero_lt_one
    refine ⟨min r (ε / (|d| + 1)), lt_min hr (div_pos hε (by positivity)), ?_⟩
    intro y hy
    have hy' : y ∈ Nbhd x r := ⟨by linarith [hy.1, min_le_left r (ε / (|d| + 1))],
      by linarith [hy.2.1, min_le_left r (ε / (|d| + 1))], hy.2.2⟩
    have hq := hnear y hy'
    change d - 1 < (G.map y - G.map x) / (y - x) ∧
      (G.map y - G.map x) / (y - x) < d + 1 at hq
    have hbound : |(G.map y - G.map x) / (y - x)| < |d| + 1 :=
      abs_lt.mpr ⟨by linarith [neg_abs_le d], by linarith [le_abs_self d]⟩
    have hdist : |y - x| < ε / (|d| + 1) := abs_lt.mpr
      ⟨by linarith [hy.1, min_le_right r (ε / (|d| + 1))],
        by linarith [hy.2.1, min_le_right r (ε / (|d| + 1))]⟩
    have hmul := mul_lt_mul_of_pos_right hbound
      (abs_pos.mpr (sub_ne_zero.mpr hy.2.2))
    rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr (sub_ne_zero.mpr hy.2.2))] at hmul
    have hsmall := (lt_div_iff₀ (show 0 < |d| + 1 by positivity)).mp hdist
    have hfinal : |G.map y - G.map x| < ε := by nlinarith
    exact ⟨by linarith [(abs_lt.mp hfinal).1], by linarith [(abs_lt.mp hfinal).2]⟩

private theorem continuous_closed {G : RFunction} {l r : ℝ} (hlr : l < r)
    (h : G.isContinuousIn (Icc l r))
  : G.isContinuousInIcc l r
:= by
  refine ⟨fun x hx => h x ⟨le_of_lt hx.1, le_of_lt hx.2⟩, ?_, ?_⟩
  · have hl := h l ⟨le_refl _, le_of_lt hlr⟩
    refine ⟨hl.1, ?_, ?_⟩
    · obtain ⟨δ, hδ, hdom⟩ := hl.2.1
      exact ⟨δ, hδ, fun x hx => hdom ⟨by linarith [hx.1], hx.2, ne_of_gt hx.1⟩⟩
    · intro ε hε
      obtain ⟨δ, hδ, hnear⟩ := hl.2.2 ε hε
      exact ⟨δ, hδ, fun x hx => hnear x ⟨by linarith [hx.1], hx.2, ne_of_gt hx.1⟩⟩
  · have hr := h r ⟨le_of_lt hlr, le_refl _⟩
    refine ⟨hr.1, ?_, ?_⟩
    · obtain ⟨δ, hδ, hdom⟩ := hr.2.1
      exact ⟨δ, hδ, fun x hx => hdom ⟨hx.1, by linarith [hx.2], ne_of_lt hx.2⟩⟩
    · intro ε hε
      obtain ⟨δ, hδ, hnear⟩ := hr.2.2 ε hε
      exact ⟨δ, hδ, fun x hx => hnear x ⟨hx.1, by linarith [hx.2], ne_of_lt hx.2⟩⟩

/-- Mean-value tags make the Riemann sum telescope exactly. -/
theorem PositiveIntegral.newtonLeibniz {F G : RFunction} {a b v : ℝ}
    (h : PositiveIntegral F a b v) (hdom : Icc a b ⊆ G.domain)
    (hderiv : ∀ x ∈ Icc a b, Deriv G x (F.map x))
  : v = G.map b - G.map a
:= by
  classical
  have tags : ∀ P : Partition a b, ∃ Q : TaggedPartition a b,
      Q.toPartition = P ∧ Q.sum F = G.map b - G.map a := by
    intro P
    have hcell : ∀ i : Fin P.count, ∃ x,
        (P.point i.castSucc ≤ x ∧ x ≤ P.point i.succ) ∧
        F.map x * P.width i = G.map (P.point i.succ) - G.map (P.point i.castSucc) := by
      intro i
      have hsub : Icc (P.point i.castSucc) (P.point i.succ) ⊆ Icc a b :=
        fun x hx => ⟨(P.point_mem _).1.trans hx.1, hx.2.trans (P.point_mem _).2⟩
      have hi : P.point i.castSucc < P.point i.succ := P.increasing _ _ (by simp)
      obtain ⟨x, hx, heq⟩ := Lagrange_MeanValue hi (hsub.trans hdom)
        (continuous_closed hi (fun x hx => deriv_continuous (hdom (hsub hx))
          (hderiv x (hsub hx))))
        (fun x hx => ⟨F.map x, hderiv x (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)⟩)
      have hd := hderiv x (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      have hd' : (Diff G).map x = F.map x := (RFunction.isDerivableAt.toDeriv ⟨_, hd⟩).unique hd
      rw [hd'] at heq
      refine ⟨x, ⟨le_of_lt hx.1, le_of_lt hx.2⟩, ?_⟩
      exact (div_eq_iff (ne_of_gt (sub_pos.mpr hi))).mp heq |>.symm
    choose tag htag hvalue using hcell
    let Q : TaggedPartition a b := ⟨P, tag, htag⟩
    refine ⟨Q, rfl, ?_⟩
    change (∑ i, F.map (tag i) * P.width i) = _
    simp_rw [hvalue]
    rw [Partition.sum_differences P.count (fun i => G.map (P.point i)),
      P.last_eq, P.first_eq]
  by_contra hne
  have hε : 0 < |G.map b - G.map a - v| := abs_pos.mpr
    (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨δ, hδ, hnear⟩ := (PositiveIntegral.mesh_iff.mp h).2.2 _ hε
  obtain ⟨P, hP⟩ := TaggedPartition.exists_mesh_lt h.1 hδ
  obtain ⟨Q, hQ, hsum⟩ := tags P.toPartition
  have hmesh : Q.mesh = P.mesh := congrArg Partition.mesh hQ
  have hn := hnear Q (hmesh ▸ hP)
  rw [hsum] at hn
  exact lt_irrefl _ hn

end Integral


page_end
