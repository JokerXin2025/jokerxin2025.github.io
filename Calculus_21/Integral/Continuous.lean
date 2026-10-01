/-
    «Calculus_21».Integral.Continuous
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Comparison
import «Calculus_21».Limit.Continuity
set_option linter.style.header false


/-! # Continuous RFunctions on Closed Intervals -/

namespace Integral

private theorem continuous_local {F : RFunction} {a b : ℝ} (_hab : a < b)
    (h : F.isContinuousInIcc a b) {s : ℝ} (hs : s ∈ Icc a b)
    {ε : ℝ} (hε : 0 < ε)
  : ∃ r > 0, ∀ x ∈ Icc a b, |x - s| < r → |F.map x - F.map s| < ε
:= by
  by_cases ha : s = a
  · subst s
    obtain ⟨r, hr, hnear⟩ := h.2.1.2.2 ε hε
    refine ⟨r, hr, fun x hx hxs => ?_⟩
    by_cases heq : x = a
    · simpa only [heq, sub_self, abs_zero] using hε
    · have hn := hnear x ⟨lt_of_le_of_ne hx.1 (Ne.symm heq),
        by have := (abs_lt.mp hxs).2; linarith⟩
      exact abs_lt.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩
  by_cases hb : s = b
  · subst s
    obtain ⟨r, hr, hnear⟩ := h.2.2.2.2 ε hε
    refine ⟨r, hr, fun x hx hxs => ?_⟩
    by_cases heq : x = b
    · simpa only [heq, sub_self, abs_zero] using hε
    · have hn := hnear x ⟨by have := (abs_lt.mp hxs).1; linarith,
        lt_of_le_of_ne hx.2 heq⟩
      exact abs_lt.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩
  have hs' : s ∈ Ioo a b := ⟨lt_of_le_of_ne hs.1 (Ne.symm ha),
    lt_of_le_of_ne hs.2 hb⟩
  obtain ⟨r, hr, hnear⟩ := (h.1 s hs').2.2 ε hε
  refine ⟨r, hr, fun x _ hxs => ?_⟩
  by_cases heq : x = s
  · simpa only [heq, sub_self, abs_zero] using hε
  · have hn := hnear x ⟨by have := (abs_lt.mp hxs).1; linarith,
      by have := (abs_lt.mp hxs).2; linarith, heq⟩
    exact abs_lt.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩

/-- Uniform continuity proved by the supremum of prefixes with a uniform bound. -/
theorem uniform_of_continuousInIcc {F : RFunction} {a b : ℝ} (hab : a < b)
    (h : F.isContinuousInIcc a b)
  : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |x - y| < δ → |F.map x - F.map y| < ε
:= by
  intro ε hε
  let good := fun t => ∃ δ > 0, ∀ x ∈ Icc a t, ∀ y ∈ Icc a t,
    |x - y| < δ → |F.map x - F.map y| < ε
  let S : Set ℝ := {t | t ∈ Icc a b ∧ good t}
  have ha : a ∈ S := by
    refine ⟨⟨le_refl _, le_of_lt hab⟩, 1, zero_lt_one, ?_⟩
    intro x hx y hy _
    have hx' : x = a := le_antisymm hx.2 hx.1
    have hy' : y = a := le_antisymm hy.2 hy.1
    simpa only [hx', hy', sub_self, abs_zero] using hε
  have hne : S.Nonempty := ⟨a, ha⟩
  have hbdd : BddAbove S := ⟨b, fun _ ht => ht.1.2⟩
  let s := sSup S
  have has : a ≤ s := le_csSup hbdd ha
  have hsb : s ≤ b := csSup_le hne (fun _ ht => ht.1.2)
  obtain ⟨r, hr, hnear⟩ := continuous_local hab h ⟨has, hsb⟩
    (show 0 < ε / 2 by positivity)
  have ht_exists : ∃ t ∈ S, s - r / 4 < t := by
    by_contra hn
    push Not at hn
    have hs_le : s ≤ s - r / 4 := csSup_le hne hn
    linarith
  obtain ⟨t, ht, hst⟩ := ht_exists
  have hts : t ≤ s := le_csSup hbdd ht
  obtain ⟨δ, hδ, hgood⟩ := ht.2
  let u := min b (s + r / 4)
  have hau : a ≤ u := le_min (le_of_lt hab) (by linarith)
  have hu : good u := by
    refine ⟨min δ (r / 4), lt_min hδ (by positivity), ?_⟩
    intro x hx y hy hxy
    by_cases hxt : x ≤ t
    · by_cases hyt : y ≤ t
      · exact hgood x ⟨hx.1, hxt⟩ y ⟨hy.1, hyt⟩
          (lt_of_lt_of_le hxy (min_le_left _ _))
      · have hdist := abs_lt.mp (lt_of_lt_of_le hxy (min_le_right _ _))
        have hxnear : |x - s| < r := abs_lt.mpr ⟨by linarith, by
          have := min_le_right b (s + r / 4); dsimp [u] at hx; linarith [hx.2]⟩
        have hynear : |y - s| < r := abs_lt.mpr ⟨by linarith, by
          have := min_le_right b (s + r / 4); dsimp [u] at hy; linarith [hy.2]⟩
        have hfx := abs_lt.mp (hnear x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩ hxnear)
        have hfy := abs_lt.mp (hnear y ⟨hy.1, hy.2.trans (min_le_left _ _)⟩ hynear)
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · have hdist := abs_lt.mp (lt_of_lt_of_le hxy (min_le_right _ _))
      have hxnear : |x - s| < r := abs_lt.mpr ⟨by linarith, by
        have := min_le_right b (s + r / 4); dsimp [u] at hx; linarith [hx.2]⟩
      have hynear : |y - s| < r := abs_lt.mpr ⟨by linarith, by
        have := min_le_right b (s + r / 4); dsimp [u] at hy; linarith [hy.2]⟩
      have hfx := abs_lt.mp (hnear x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩ hxnear)
      have hfy := abs_lt.mp (hnear y ⟨hy.1, hy.2.trans (min_le_left _ _)⟩ hynear)
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hus : u ≤ s := le_csSup hbdd ⟨⟨hau, min_le_left _ _⟩, hu⟩
  have hbs : b ≤ s := by
    by_contra hn
    have : s < u := lt_min (lt_of_not_ge hn) (by linarith)
    linarith
  have hub : u = b := min_eq_left (by linarith)
  simpa only [hub] using hu

theorem PositiveIntegral.of_continuousInIcc {F : RFunction} {a b : ℝ}
    (hab : a < b) (h : F.isContinuousInIcc a b)
  : ∃ v, PositiveIntegral F a b v
:= by
  apply PositiveIntegral.of_uniform F hab
  · intro x hx
    by_cases ha : x = a
    · exact ha ▸ h.2.1.1
    by_cases hb : x = b
    · exact hb ▸ h.2.2.1
    exact (h.1 x ⟨lt_of_le_of_ne hx.1 (Ne.symm ha), lt_of_le_of_ne hx.2 hb⟩).1
  · exact uniform_of_continuousInIcc hab h

end Integral


page_end
