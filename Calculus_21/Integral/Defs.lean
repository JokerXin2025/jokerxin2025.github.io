import «Calculus_21».Differential.Defs
import «Calculus_21».Limit.Continuity
import «Calculus_21».Integral.Interval
import «Calculus_21».Integral.Continuous
import «Calculus_21».Integral.NewtonLeibniz


/-! # Definite integrals of domain-aware real functions

The integral is oriented, but domain coverage includes both endpoints in either
orientation. The value is defined by the tagged Riemann sum net.
All integral laws below are proved from this definition.
-/

namespace Integral

/-- The closed interval between the endpoints, irrespective of orientation. -/
abbrev interval (a b : ℝ) : Set ℝ := Icc (min a b) (max a b)

end Integral


def DefIntegral (F : RFunction) (a b value : ℝ) : Prop :=
  if a < b then Integral.PositiveIntegral F a b value
  else if b < a then Integral.PositiveIntegral F b a (-value)
  else a ∈ F.domain ∧ value = 0

def RFunction.isIntegrableOn (F : RFunction) (a b : ℝ) : Prop :=
  ∃ value, DefIntegral F a b value

namespace DefIntegral
variable {F G : RFunction} {a b c value value₁ value₂ : ℝ}

theorem iff_of_lt (hab : a < b)
  : DefIntegral F a b value ↔ Integral.PositiveIntegral F a b value
:= by simp only [DefIntegral, if_pos hab]

theorem iff_of_gt (hba : b < a)
  : DefIntegral F a b value ↔ Integral.PositiveIntegral F b a (-value)
:= by simp only [DefIntegral, if_neg (not_lt_of_gt hba), if_pos hba]

theorem iff_same
  : DefIntegral F a a value ↔ a ∈ F.domain ∧ value = 0
:= by simp only [DefIntegral, lt_self_iff_false, if_false]

theorem unique (h₁ : DefIntegral F a b value₁)
    (h₂ : DefIntegral F a b value₂) : value₁ = value₂
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact ((iff_of_lt hab).mp h₁).unique ((iff_of_lt hab).mp h₂)
  · subst b
    exact (iff_same.mp h₁).2.trans (iff_same.mp h₂).2.symm
  · exact neg_injective (((iff_of_gt hba).mp h₁).unique ((iff_of_gt hba).mp h₂))

theorem domain (h : DefIntegral F a b value) : Integral.interval a b ⊆ F.domain
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · simpa only [Integral.interval, min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)]
      using ((iff_of_lt hab).mp h).domain
  · subst b
    simpa only [Integral.interval, min_self, max_self, Set.Icc_self, Set.singleton_subset_iff]
      using (iff_same.mp h).1
  · simpa only [Integral.interval, min_eq_right (le_of_lt hba), max_eq_left (le_of_lt hba)]
      using ((iff_of_gt hba).mp h).domain

/-- Changing the map outside the interval or changing its domain is harmless
only when the target domain still covers the entire closed interval. -/
theorem congr (h : DefIntegral F a b value)
    (hdom : Integral.interval a b ⊆ G.domain)
    (heq : ∀ x ∈ Integral.interval a b, F.map x = G.map x) :
    DefIntegral G a b value
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · simp only [Integral.interval, min_eq_left (le_of_lt hab),
      max_eq_right (le_of_lt hab)] at hdom heq
    exact (iff_of_lt hab).mpr (((iff_of_lt hab).mp h).congr hdom heq)
  · subst b
    exact iff_same.mpr ⟨hdom ⟨min_le_left _ _, le_max_left _ _⟩, (iff_same.mp h).2⟩
  · simp only [Integral.interval, min_eq_right (le_of_lt hba),
      max_eq_left (le_of_lt hba)] at hdom heq
    exact (iff_of_gt hba).mpr (((iff_of_gt hba).mp h).congr hdom heq)

theorem same (ha : a ∈ F.domain) : DefIntegral F a a 0 := iff_same.mpr ⟨ha, rfl⟩

theorem reverse (h : DefIntegral F a b value) : DefIntegral F b a (-value)
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · apply (iff_of_gt hab).mpr
    simpa only [neg_neg] using (iff_of_lt hab).mp h
  · subst b
    obtain ⟨ha, hv⟩ := iff_same.mp h
    exact iff_same.mpr ⟨ha, by rw [hv, neg_zero]⟩
  · exact (iff_of_lt hba).mpr ((iff_of_gt hba).mp h)

theorem const (k a b : ℝ) : DefIntegral (Constant k) a b (k * (b - a))
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (iff_of_lt hab).mpr (Integral.PositiveIntegral.const k hab)
  · subst b
    simpa only [sub_self, mul_zero] using (same (F := Constant k) (a := a) trivial)
  · apply (iff_of_gt hba).mpr
    convert Integral.PositiveIntegral.const k hba using 1
    ring

theorem add (hF : DefIntegral F a b value₁) (hG : DefIntegral G a b value₂) :
    DefIntegral (F + G) a b (value₁ + value₂)
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (iff_of_lt hab).mpr (((iff_of_lt hab).mp hF).add ((iff_of_lt hab).mp hG))
  · subst b
    obtain ⟨hF, hv⟩ := iff_same.mp hF
    obtain ⟨hG, hw⟩ := iff_same.mp hG
    exact iff_same.mpr ⟨⟨hF, hG⟩, by rw [hv, hw, add_zero]⟩
  · apply (iff_of_gt hba).mpr
    simpa only [neg_add] using (((iff_of_gt hba).mp hF).add ((iff_of_gt hba).mp hG))

theorem smul (k : ℝ) (h : DefIntegral F a b value) :
    DefIntegral (k • F) a b (k * value)
:= by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (iff_of_lt hab).mpr (((iff_of_lt hab).mp h).smul k)
  · subst b
    obtain ⟨ha, hv⟩ := iff_same.mp h
    exact iff_same.mpr ⟨ha, by rw [hv, mul_zero]⟩
  · apply (iff_of_gt hba).mpr
    simpa only [mul_neg] using (((iff_of_gt hba).mp h).smul k)

/-- Both pieces must be integrable; no ordering of the three endpoints is needed. -/
theorem split (hab : DefIntegral F a b value₁) (hbc : DefIntegral F b c value₂) :
    DefIntegral F a c (value₁ + value₂)
:= by
  have forward : ∀ {l m r v w : ℝ}, l < m → m < r →
      DefIntegral F l m v → DefIntegral F m r w → DefIntegral F l r (v + w) := by
    intro l m r v w hlm hmr hl hr
    exact (iff_of_lt (lt_trans hlm hmr)).mpr
      (((iff_of_lt hlm).mp hl).append ((iff_of_lt hmr).mp hr))
  by_cases heq : a = b
  · subst b
    rw [(iff_same.mp hab).2, zero_add]
    exact hbc
  by_cases heq' : b = c
  · subst c
    rw [(iff_same.mp hbc).2, add_zero]
    exact hab
  by_cases heq'' : a = c
  · subst c
    have hv := hab.unique hbc.reverse
    have ha := hab.domain ⟨min_le_left _ _, le_max_left _ _⟩
    convert same ha using 1
    linarith
  rcases lt_or_gt_of_ne heq with h_ab | h_ba
  · rcases lt_or_gt_of_ne heq' with h_bc | h_cb
    · exact forward h_ab h_bc hab hbc
    · rcases lt_or_gt_of_ne heq'' with h_ac | h_ca
      · have hp := (iff_of_lt h_ab).mp hab
        obtain ⟨u, hu⟩ := hp.left_integrable h_ac h_cb
        have hv := hp.split_value hu ((iff_of_gt h_cb).mp hbc)
        apply (iff_of_lt h_ac).mpr
        convert hu using 1
        linarith
      · have hp := (iff_of_gt h_cb).mp hbc
        obtain ⟨u, hu⟩ := hp.left_integrable h_ca h_ab
        have hv := hp.split_value hu ((iff_of_lt h_ab).mp hab)
        apply (iff_of_gt h_ca).mpr
        convert hu using 1
        linarith
  · rcases lt_or_gt_of_ne heq' with h_bc | h_cb
    · rcases lt_or_gt_of_ne heq'' with h_ac | h_ca
      · have hp := (iff_of_lt h_bc).mp hbc
        obtain ⟨u, hu⟩ := hp.right_integrable h_ba h_ac
        have hv := hp.split_value ((iff_of_gt h_ba).mp hab) hu
        apply (iff_of_lt h_ac).mpr
        convert hu using 1
        linarith
      · have hp := (iff_of_gt h_ba).mp hab
        obtain ⟨u, hu⟩ := hp.right_integrable h_bc h_ca
        have hv := hp.split_value ((iff_of_lt h_bc).mp hbc) hu
        apply (iff_of_gt h_ca).mpr
        convert hu using 1
        linarith
    · have hr := (forward h_cb h_ba hbc.reverse hab.reverse).reverse
      convert hr using 1
      ring

theorem mono (hab : a ≤ b) (hF : DefIntegral F a b value₁)
    (hG : DefIntegral G a b value₂)
    (hle : ∀ x ∈ Integral.interval a b, F.map x ≤ G.map x) : value₁ ≤ value₂
:= by
  rcases lt_or_eq_of_le hab with hab | hab
  · simp only [Integral.interval, min_eq_left (le_of_lt hab),
      max_eq_right (le_of_lt hab)] at hle
    exact ((iff_of_lt hab).mp hF).mono ((iff_of_lt hab).mp hG) hle
  · subst b
    rw [(iff_same.mp hF).2, (iff_same.mp hG).2]

/-- A conservative Newton-Leibniz law requiring two-sided derivatives even at
the endpoints, as well as integrability of the integrand. -/
theorem newtonLeibniz {F G : RFunction} {a b : ℝ}
    (hInt : F.isIntegrableOn a b)
    (hGdom : Integral.interval a b ⊆ G.domain)
    (hDeriv : ∀ x ∈ Integral.interval a b, Deriv G x (F.map x)) :
    DefIntegral F a b (G.map b - G.map a)
:= by
  obtain ⟨v, hv⟩ := hInt
  rcases lt_trichotomy a b with hab | hab | hba
  · have hp := (iff_of_lt hab).mp hv
    simp only [Integral.interval, min_eq_left (le_of_lt hab),
      max_eq_right (le_of_lt hab)] at hGdom hDeriv
    exact (iff_of_lt hab).mpr ((hp.newtonLeibniz hGdom hDeriv) ▸ hp)
  · subst b
    simpa only [sub_self] using same (iff_same.mp hv).1
  · have hp := (iff_of_gt hba).mp hv
    simp only [Integral.interval, min_eq_right (le_of_lt hba),
      max_eq_left (le_of_lt hba)] at hGdom hDeriv
    apply (iff_of_gt hba).mpr
    have heq := hp.newtonLeibniz hGdom hDeriv
    convert heq ▸ hp using 1
    ring

theorem isIntegrableOn (h : DefIntegral F a b value) : F.isIntegrableOn a b :=
  ⟨value, h⟩

theorem changeDomain (h : DefIntegral F a b value) {dom : Set ℝ}
    (hdom : Integral.interval a b ⊆ dom) : DefIntegral ⟨F.map, dom⟩ a b value :=
  h.congr hdom (fun _ _ => rfl)

theorem total (h : DefIntegral F a b value) :
    DefIntegral (_root_.total F.map) a b value :=
  h.congr (fun _ _ => trivial) (fun _ _ => rfl)

end DefIntegral

namespace RFunction.isIntegrableOn
variable {F G : RFunction} {a b c d : ℝ}

theorem domain (h : F.isIntegrableOn a b) : Integral.interval a b ⊆ F.domain := by
  obtain ⟨value, h⟩ := h
  exact h.domain

theorem congr (h : F.isIntegrableOn a b)
    (hdom : Integral.interval a b ⊆ G.domain)
    (heq : ∀ x ∈ Integral.interval a b, F.map x = G.map x) :
    G.isIntegrableOn a b := by
  obtain ⟨value, h⟩ := h
  exact (h.congr hdom heq).isIntegrableOn

theorem reverse (h : F.isIntegrableOn a b) : F.isIntegrableOn b a := by
  obtain ⟨value, h⟩ := h
  exact h.reverse.isIntegrableOn

theorem add (hF : F.isIntegrableOn a b) (hG : G.isIntegrableOn a b) :
    (F + G).isIntegrableOn a b := by
  obtain ⟨v, hv⟩ := hF
  obtain ⟨w, hw⟩ := hG
  exact (hv.add hw).isIntegrableOn

theorem smul (k : ℝ) (h : F.isIntegrableOn a b) : (k • F).isIntegrableOn a b := by
  obtain ⟨value, h⟩ := h
  exact (h.smul k).isIntegrableOn

theorem split (hab : F.isIntegrableOn a b) (hbc : F.isIntegrableOn b c) :
    F.isIntegrableOn a c := by
  obtain ⟨v, hv⟩ := hab
  obtain ⟨w, hw⟩ := hbc
  exact (hv.split hw).isIntegrableOn

/-- Integrability restricts to any closed subinterval, in either orientation. -/
theorem subinterval (h : F.isIntegrableOn a b)
    (hsub : Integral.interval c d ⊆ Integral.interval a b) : F.isIntegrableOn c d
:= by
  have hdom := h.domain
  have hc : c ∈ F.domain := hdom (hsub ⟨min_le_left _ _, le_max_left _ _⟩)
  have hd : d ∈ F.domain := hdom (hsub ⟨min_le_right _ _, le_max_right _ _⟩)
  have restrict_positive : ∀ {l r : ℝ}, l < r →
      Integral.interval l r ⊆ Integral.interval a b →
      ∃ w, Integral.PositiveIntegral F l r w := by
    intro l r hlr hsub'
    have hl := hsub' (show l ∈ Integral.interval l r from
      ⟨min_le_left _ _, le_max_left _ _⟩)
    have hr := hsub' (show r ∈ Integral.interval l r from
      ⟨min_le_right _ _, le_max_right _ _⟩)
    obtain ⟨v, hv⟩ := h
    rcases lt_trichotomy a b with hab | hab | hba
    · simp only [Integral.interval, min_eq_left (le_of_lt hab),
        max_eq_right (le_of_lt hab)] at hl hr
      exact ((DefIntegral.iff_of_lt hab).mp hv).subinterval hl.1 hlr hr.2
    · subst b
      simp only [Integral.interval, min_self, max_self, mem_Icc] at hl hr
      exfalso
      linarith [hl.1, hr.2]
    · simp only [Integral.interval, min_eq_right (le_of_lt hba),
        max_eq_left (le_of_lt hba)] at hl hr
      exact ((DefIntegral.iff_of_gt hba).mp hv).subinterval hl.1 hlr hr.2
  rcases lt_trichotomy c d with hcd | hcd | hdc
  · obtain ⟨w, hw⟩ := restrict_positive hcd hsub
    exact ⟨w, (DefIntegral.iff_of_lt hcd).mpr hw⟩
  · subst d
    exact ⟨0, DefIntegral.same hc⟩
  · have hsub' : Integral.interval d c ⊆ Integral.interval a b := by
      simpa only [Integral.interval, min_comm d c, max_comm d c] using hsub
    obtain ⟨w, hw⟩ := restrict_positive hdc hsub'
    refine ⟨-w, (DefIntegral.iff_of_gt hdc).mpr ?_⟩
    simpa only [neg_neg] using hw

/-- The existing one-sided endpoint continuity notion requires a strict interval. -/
theorem of_continuousInIcc (hab : a < b) (h : F.isContinuousInIcc a b) :
    F.isIntegrableOn a b
:= by
  obtain ⟨v, hv⟩ := Integral.PositiveIntegral.of_continuousInIcc hab h
  exact ⟨v, (DefIntegral.iff_of_lt hab).mpr hv⟩

theorem of_continuous (h : F.isContinuousIn (Integral.interval a b)) :
    F.isIntegrableOn a b
:= by
  have ordered : ∀ {l r : ℝ}, l < r → F.isContinuousIn (Icc l r) →
      F.isIntegrableOn l r := by
    intro l r hlr hc
    apply of_continuousInIcc hlr
    refine ⟨fun x hx => hc x ⟨le_of_lt hx.1, le_of_lt hx.2⟩, ?_, ?_⟩
    · have hl := hc l ⟨le_refl _, le_of_lt hlr⟩
      refine ⟨hl.1, ?_, ?_⟩
      · obtain ⟨δ, hδ, hdom⟩ := hl.2.1
        exact ⟨δ, hδ, fun x hx => hdom ⟨by linarith [hx.1], hx.2, ne_of_gt hx.1⟩⟩
      · intro ε hε
        obtain ⟨δ, hδ, hnear⟩ := hl.2.2 ε hε
        exact ⟨δ, hδ, fun x hx => hnear x ⟨by linarith [hx.1], hx.2, ne_of_gt hx.1⟩⟩
    · have hr := hc r ⟨le_of_lt hlr, le_refl _⟩
      refine ⟨hr.1, ?_, ?_⟩
      · obtain ⟨δ, hδ, hdom⟩ := hr.2.1
        exact ⟨δ, hδ, fun x hx => hdom ⟨hx.1, by linarith [hx.2], ne_of_lt hx.2⟩⟩
      · intro ε hε
        obtain ⟨δ, hδ, hnear⟩ := hr.2.2 ε hε
        exact ⟨δ, hδ, fun x hx => hnear x ⟨hx.1, by linarith [hx.2], ne_of_lt hx.2⟩⟩
  rcases lt_trichotomy a b with hab | hab | hba
  · apply ordered hab
    simpa only [Integral.interval, min_eq_left (le_of_lt hab),
      max_eq_right (le_of_lt hab)] using h
  · subst b
    exact ⟨0, DefIntegral.same (h a ⟨min_le_left _ _, le_max_left _ _⟩).1⟩
  · apply RFunction.isIntegrableOn.reverse
    apply ordered hba
    simpa only [Integral.interval, min_eq_right (le_of_lt hba),
      max_eq_left (le_of_lt hba)] using h

end RFunction.isIntegrableOn
