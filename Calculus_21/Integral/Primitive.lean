/-
    «Calculus_21».Integral.Primitive
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.Defs
set_option linter.style.header false


/-! # Variable-Upper-Limit Integrals as RFunctions -/

namespace Integral

open Classical in
/-- An auxiliary value; its specification is used only on integrable intervals. -/
noncomputable def value (F : RFunction) (a b : ℝ) : ℝ :=
  if h : F.isIntegrableOn a b then choose h else 0

theorem value_spec {F : RFunction} {a b : ℝ} (h : F.isIntegrableOn a b)
  : DefIntegral F a b (value F a b)
:= by
  classical
  simpa only [value, dif_pos h] using Classical.choose_spec h

/-- The closed-interval domain is part of the resulting function. -/
noncomputable def primitive (F : RFunction) (a b : ℝ) : RFunction :=
  ⟨fun x => value F a x, Icc a b⟩

theorem primitive_spec {F : RFunction} {a b x : ℝ}
    (h : F.isIntegrableOn a b) (hx : x ∈ Icc a b)
  : DefIntegral F a x ((primitive F a b).map x)
:= by
  apply value_spec
  apply h.subinterval
  have hab : a ≤ b := hx.1.trans hx.2
  simp only [interval, min_eq_left hx.1, max_eq_right hx.1,
    min_eq_left hab, max_eq_right hab]
  exact fun y hy => ⟨hy.1, hy.2.trans hx.2⟩

theorem primitive_increment {F : RFunction} {a b x y : ℝ}
    (h : F.isIntegrableOn a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
  : DefIntegral F x y ((primitive F a b).map y - (primitive F a b).map x)
:= by
  have hi := (primitive_spec h hx).reverse.split (primitive_spec h hy)
  simpa only [sub_eq_add_neg, add_comm] using hi

private theorem average_bound {F : RFunction} {x y v c ε : ℝ}
    (h : DefIntegral F x y v) (hne : x ≠ y)
    (hbound : ∀ t ∈ interval x y, |F.map t - c| ≤ ε)
  : |v / (y - x) - c| ≤ ε
:= by
  have forward : ∀ {x y v : ℝ}, x < y → DefIntegral F x y v →
      (∀ t ∈ interval x y, |F.map t - c| ≤ ε) →
      |v / (y - x) - c| ≤ ε := by
    intro x y v hxy hv hb
    have hl := (DefIntegral.const (c - ε) x y).mono (le_of_lt hxy) hv
      (fun t ht => by have := (abs_le.mp (hb t ht)).1; change c - ε ≤ F.map t; linarith)
    have hu := hv.mono (le_of_lt hxy) (DefIntegral.const (c + ε) x y)
      (fun t ht => by have := (abs_le.mp (hb t ht)).2; change F.map t ≤ c + ε; linarith)
    have hl' := (le_div_iff₀ (sub_pos.mpr hxy)).mpr hl
    have hu' := (div_le_iff₀ (sub_pos.mpr hxy)).mpr hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · exact forward hxy h hbound
  · have hb : ∀ t ∈ interval y x, |F.map t - c| ≤ ε := by
      simpa only [interval, min_comm y x, max_comm y x] using hbound
    have hf := forward hyx h.reverse hb
    have heq : -v / (x - y) = v / (y - x) := by
      rw [show x - y = -(y - x) by ring, neg_div_neg_eq]
    rwa [heq] at hf

/-- At every interior continuity point, the derivative of the primitive is F. -/
theorem primitive_deriv {F : RFunction} {a b x : ℝ}
    (h : F.isIntegrableOn a b) (hx : x ∈ Ioo a b) (hc : F.isContinuousAt x)
  : Deriv (primitive F a b) x (F.map x)
:= by
  let G := primitive F a b
  have hx' : x ∈ Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hlocal : ∀ y ∈ Nbhd x (min (x - a) (b - x)), y ∈ Icc a b := by
    intro y hy
    exact ⟨by linarith [hy.1, min_le_left (x - a) (b - x)],
      by linarith [hy.2.1, min_le_right (x - a) (b - x)]⟩
  constructor
  · refine ⟨min (x - a) (b - x), lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2), ?_⟩
    intro y hy
    exact ⟨⟨⟨hlocal y hy, trivial⟩, ⟨trivial, trivial⟩⟩, sub_ne_zero.mpr hy.2.2⟩
  · intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := hc.2.2 (ε / 2) (by positivity)
    let r := min δ (min (x - a) (b - x))
    have hr : 0 < r := lt_min hδ (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    refine ⟨r, hr, fun y hy => ?_⟩
    have hxy : |y - x| < δ := abs_lt.mpr
      ⟨by have := min_le_left δ (min (x - a) (b - x)); dsimp [r] at hy; linarith [hy.1],
        by have := min_le_left δ (min (x - a) (b - x)); dsimp [r] at hy; linarith [hy.2.1]⟩
    have hy' : y ∈ Icc a b := hlocal y ⟨by
      have := min_le_right δ (min (x - a) (b - x)); dsimp [r] at hy; linarith [hy.1],
      by have := min_le_right δ (min (x - a) (b - x)); dsimp [r] at hy; linarith [hy.2.1],
      hy.2.2⟩
    have hb : ∀ t ∈ interval x y, |F.map t - F.map x| ≤ ε / 2 := by
      intro t ht
      by_cases htx : t = x
      · rw [htx, sub_self, abs_zero]; positivity
      have hd : |t - x| < δ := by
        have hdist := abs_lt.mp hxy
        rcases le_total x y with hle | hle
        · simp only [interval, min_eq_left hle, max_eq_right hle, mem_Icc] at ht
          exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · simp only [interval, min_eq_right hle, max_eq_left hle, mem_Icc] at ht
          exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hn := hnear t ⟨by linarith [(abs_lt.mp hd).1],
        by linarith [(abs_lt.mp hd).2], htx⟩
      exact le_of_lt (abs_lt.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩)
    have hav := average_bound (primitive_increment h hx' hy') (Ne.symm hy.2.2) hb
    change F.map x - ε < (G.map y - G.map x) / (y - x) ∧
      (G.map y - G.map x) / (y - x) < F.map x + ε
    have hh := abs_le.mp hav
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

end Integral


page_end
