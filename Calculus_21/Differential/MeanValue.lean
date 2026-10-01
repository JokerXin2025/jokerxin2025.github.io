/-
    «Calculus_21».Differential.MeanValue
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Continuity
import «Calculus_21».Differential.Tactics
set_option linter.style.header false

script_macro "apply" h:term => `(tactic|
  apply $h
)

script_macro "let" id:ident ":=" h:term => `(tactic|
  let $id := $h
)


/-! # Mean Value Theorems -/

section
variable {F G : RFunction} {a b x₀ δ : ℝ}

/-- Fermat's Lemma -/
theorem Fermat_Lemma
    (h_δ : 0 < δ)
    (_h_dom : Nbho x₀ δ ⊆ F.domain)
    (h_deriv : F.isDerivableAt x₀)
    (h_extre : (∀ x ∈ Nbho x₀ δ, F.map x ≤ F.map x₀)
               ∨ (∀ x ∈ Nbho x₀ δ, F.map x ≥ F.map x₀))
  : Deriv F x₀ 0
:= by
  script_obtain_exist ⟨L, hL⟩ := h_deriv
  suffices hzero : L = 0 by simpa [hzero] using hL
  by_contra hne
  obtain ⟨r, hr, hlim⟩ := hL.2 (|L| / 2) (by positivity)
  let t := min δ r / 2
  have ht : t > 0 := by positivity
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ r]
  have htr : t < r := by dsimp [t]; linarith [min_le_right δ r]
  have hleft := hlim (x₀ - t) (by grind)
  have hright := hlim (x₀ + t) (by grind)
  change L - |L| / 2 < (F.map (x₀ - t) - F.map x₀) / (x₀ - t - x₀) ∧
    (F.map (x₀ - t) - F.map x₀) / (x₀ - t - x₀) < L + |L| / 2 at hleft
  change L - |L| / 2 < (F.map (x₀ + t) - F.map x₀) / (x₀ + t - x₀) ∧
    (F.map (x₀ + t) - F.map x₀) / (x₀ + t - x₀) < L + |L| / 2 at hright
  have hleft_mem : x₀ - t ∈ Nbho x₀ δ := ⟨by linarith, by linarith⟩
  have hright_mem : x₀ + t ∈ Nbho x₀ δ := ⟨by linarith, by linarith⟩
  -- At an extremum the two difference quotients have opposite weak signs.
  script_cases_by h_extre
  · have hl := div_nonneg_of_nonpos (sub_nonpos.mpr (hp _ hleft_mem))
      (show x₀ - t - x₀ ≤ 0 by linarith)
    have hr := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hp _ hright_mem))
      (show 0 ≤ x₀ + t - x₀ by linarith)
    script_cases_by lt_or_gt_of_ne hne
    · rw [abs_of_neg hp] at hleft
      linarith
    · rw [abs_of_pos hq] at hright
      linarith
  · have hl := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hq _ hleft_mem))
      (show x₀ - t - x₀ ≤ 0 by linarith)
    have hr := div_nonneg (sub_nonneg.mpr (hq _ hright_mem))
      (show 0 ≤ x₀ + t - x₀ by linarith)
    script_cases_by lt_or_gt_of_ne hne
    · rw [abs_of_neg hp] at hright
      linarith
    · rw [abs_of_pos hq] at hleft
      linarith

/-- The derivative vanishes at an interior maximum of a closed interval. -/
lemma Deriv.atMaximumOnIcc {c : ℝ}
    (hc : c ∈ Ioo a b) (h_dom : Icc a b ⊆ F.domain)
    (h_deriv : F.isDerivableAt c)
    (hmax : isMaximumPointOn F (Icc a b) c) : Deriv F c 0 := by
  let δ := min (c - a) (b - c)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hsub : Nbho c δ ⊆ Icc a b := by
    intro x hx
    exact ⟨by linarith [hx.1, min_le_left (c - a) (b - c)],
      by linarith [hx.2, min_le_right (c - a) (b - c)]⟩
  exact Fermat_Lemma hδ (hsub.trans h_dom) h_deriv
    (Or.inl (fun x hx => hmax x (hsub hx)))

/-- The derivative vanishes at an interior minimum of a closed interval. -/
lemma Deriv.atMinimumOnIcc {c : ℝ}
    (hc : c ∈ Ioo a b) (h_dom : Icc a b ⊆ F.domain)
    (h_deriv : F.isDerivableAt c)
    (hmin : isMinimumPointOn F (Icc a b) c) : Deriv F c 0 := by
  let δ := min (c - a) (b - c)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hsub : Nbho c δ ⊆ Icc a b := by
    intro x hx
    exact ⟨by linarith [hx.1, min_le_left (c - a) (b - c)],
      by linarith [hx.2, min_le_right (c - a) (b - c)]⟩
  exact Fermat_Lemma hδ (hsub.trans h_dom) h_deriv
    (Or.inr (fun x hx => hmin x (hsub hx)))

/-- Rolle's Mean Value Theorem -/
theorem Rolle_MeanValue
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain)
    (h_eq : F.map a = F.map b)
    (h_cont : F.isContinuousInIcc a b)
    (h_deriv : ∀ x ∈ Ioo a b, F.isDerivableAt x)
  : ∃ ξ ∈ Ioo a b, Deriv F ξ 0
:= by
  let f := F.map
  script_obtain_exist ⟨m, hm, hmin⟩ := Min_Existence h_a_lt_b h_cont
  script_obtain_exist ⟨M, hM, hmax⟩ := Max_Existence h_a_lt_b h_cont
  have endpoint_value {c : ℝ} : c = a ∨ c = b → f c = f a := by grind
  have hcases : m ∈ Ioo a b ∨ M ∈ Ioo a b ∨ (m = a ∨ m = b) ∧ (M = a ∨ M = b) := by
    have endpoint (c : ℝ) (hc : c ∈ Icc a b) (hn : c ∉ Ioo a b) :
        c = a ∨ c = b := by
      by_contra h
      push Not at h
      exact hn ⟨lt_of_le_of_ne hc.1 (Ne.symm h.1), lt_of_le_of_ne hc.2 h.2⟩
    by_cases hm_int : m ∈ Ioo a b
    · exact Or.inl hm_int
    by_cases hM_int : M ∈ Ioo a b
    · exact Or.inr (Or.inl hM_int)
    exact Or.inr (Or.inr ⟨endpoint m hm hm_int, endpoint M hM hM_int⟩)
  rcases hcases with hm_int | hM_int | ⟨hm_end, hM_end⟩
  · exact ⟨m, hm_int, Deriv.atMinimumOnIcc hm_int h_dom (h_deriv m hm_int) hmin⟩
  · exact ⟨M, hM_int, Deriv.atMaximumOnIcc hM_int h_dom (h_deriv M hM_int) hmax⟩
  · script_remark
      "Equal endpoint extrema force the function to be constant on the interval."
    have h_const : ∀ x ∈ Icc a b, f x = f a := by
      intro x hx
      have hlower := hmin x hx
      have hupper := hmax x hx
      change f m ≤ f x at hlower
      change f x ≤ f M at hupper
      rw [endpoint_value hm_end] at hlower
      rw [endpoint_value hM_end] at hupper
      exact le_antisymm hupper hlower
    let c := (a + b) / 2
    have h_c : c ∈ Ioo a b := by grind
    script_exists c with h_c
    refine Deriv.atMaximumOnIcc h_c h_dom (h_deriv c h_c) ?_
    intro x hx
    change f x ≤ f c
    rw [h_const x hx, h_const c (by grind)]

open Classical in
lemma RFunction.isDerivableAt.toDeriv
  : F.isDerivableAt x₀ → Deriv F x₀ ((Diff F).map x₀)
:= by
  intro h
  simpa only [Diff, dif_pos h] using choose_spec h

/-- Lagrange's Mean Value Theorem -/
theorem Lagrange_MeanValue
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain)
    (h_cont : F.isContinuousInIcc a b)
    (h_deriv : ∀ x ∈ Ioo a b, F.isDerivableAt x)
  : ∃ ξ ∈ Ioo a b,
      (F.map b - F.map a) / (b - a) = (Diff F).map ξ
:= script
  let f := F.map
  let f' := (Diff F).map
  let k := (f b - f a) / (b - a)
  let H := F - ((f b - f a) / (b - a)) • Identity
  let h := H.map
  claim h_H_deriv : ∀ x ∈ Ioo a b, Deriv H x (f' x - k)
  | proof =>
    intro x h_x
    use_expr
    | calculation => calc
        D h x  =. D f x - D (k * ·) x
                  := by deriv_sub
        _      =  D f x - the k
                  := by deriv_calc
        _      =  the (f' x - k)
                  := by poly_rw [h_deriv x h_x |>.toDeriv.toDerivExpr]
    | side =>
      claim h_H_cont : H.isContinuousAt x
      | proof => infer_continuity
      exact_proj h_H_cont
  claim_exist ⟨ξ, h_ξ, h_zero⟩ : ∃ ξ ∈ Ioo a b, Deriv H ξ 0
  | proof =>
    apply Rolle_MeanValue
    · exact h_a_lt_b
    · intro x h_x
      split_and
      · exact h_dom h_x
      · apply mem_univ _
    · infer
        b - a ≠ 0  => (f b - f a) / (b - a) * (b - a) = f b - f a
                      := div_mul_cancel₀ _ (by positivity)
                   => f a - k * a = f b - k * b
                      := by linarith
                   => h a = h b
                      := ?_
    · infer_continuity
    · infer_derivability
  exists ξ with h_ξ
  infer
    Deriv H ξ (f' ξ - k) => f' ξ - k = 0
                            := (h_H_deriv ξ h_ξ).unique h_zero
                         => (f b - f a) / (b - a) = f' ξ
                            := (sub_eq_zero.mp ?_).symm

/-- Cauchy's Mean Value Theorem (Product Form) -/
theorem Cauchy_MeanValue
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_F_cont : F.isContinuousInIcc a b)
    (h_G_cont : G.isContinuousInIcc a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, F.isDerivableAt x)
    (h_G_deriv : ∀ x ∈ Ioo a b, G.isDerivableAt x)
  : ∃ ξ ∈ Ioo a b,
      (Diff F).map ξ * (G.map b - G.map a) = (Diff G).map ξ * (F.map b - F.map a)
:= script
  let f := F.map
  let f' := (Diff F).map
  let g := G.map
  let g' := (Diff G).map
  let H := (g b - g a) • F - (f b - f a) • G
  let h := H.map
  claim h_H_deriv : ∀ x ∈ Ioo a b,
      Deriv H x (f' x * (g b - g a) - g' x * (f b - f a))
  | proof =>
    intro x h_x
    use_expr
    | calculation => calc
        D h x  =. D ((g b - g a) • f) x - D ((f b - f a) • g) x
                  := by deriv_sub
        _      =. the (g b - g a) * D f x - the (f b - f a) * D g x
                  := by deriv_smul
        _      =  the ((g b - g a) * f' x - (f b - f a) * g' x)
                  := by
                    poly_rw [h_F_deriv x h_x |>.toDeriv.toDerivExpr]
                    poly_rw [h_G_deriv x h_x |>.toDeriv.toDerivExpr]
        _      =  the (f' x * (g b - g a) - g' x * (f b - f a))
                  := by ring_nf
    | side =>
      claim h_H_cont : H.isContinuousAt x
      | proof => infer_continuity
      exact_proj h_H_cont
  claim_exist ⟨ξ, h_ξ, h_zero⟩ : ∃ ξ ∈ Ioo a b, Deriv H ξ 0
  | proof =>
    apply Rolle_MeanValue
    · exact h_a_lt_b
    · exact h_dom
    · change (g b - g a) * f a - (f b - f a) * g a
          = (g b - g a) * f b - (f b - f a) * g b
      ring_nf
    · infer_continuity
    · infer_derivability
  exists ξ with h_ξ
  infer
        Deriv H ξ (f' ξ * (g b - g a) - g' ξ * (f b - f a))
     => f' ξ * (g b - g a) - g' ξ * (f b - f a) = 0
        := (h_H_deriv ξ h_ξ).unique h_zero
     => f' ξ * (g b - g a) = g' ξ * (f b - f a)
        := sub_eq_zero.mp ?_

/-- Cauchy's Mean Value Theorem (Normal Form) -/
theorem Cauchy_MeanValue'
    (h_a_lt_b : a < b)
    (h_dom : Icc a b ⊆ F.domain ∩ G.domain)
    (h_G'_ne_0 : ∀ x ∈ (Diff G).domain, (Diff G).map x ≠ 0)
    (h_F_cont : F.isContinuousInIcc a b)
    (h_G_cont : G.isContinuousInIcc a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, F.isDerivableAt x)
    (h_G_deriv : ∀ x ∈ Ioo a b, G.isDerivableAt x)
  : ∃ ξ ∈ Ioo a b,
      (F.map b - F.map a) / (G.map b - G.map a) = (Diff F).map ξ / (Diff G).map ξ
:= script
  let f := F.map
  let g := G.map
  let f' := (Diff F).map
  let g' := (Diff G).map
  claim hG_ne : g b - g a ≠ 0
  | proof =>
    contra h_eq
    claim_exist ⟨ξ, hξ, hzero⟩ : ∃ ξ ∈ Ioo a b, Deriv G ξ 0
    | proof =>
      apply Rolle_MeanValue
      · exact h_a_lt_b
      · exact (fun x hx => (h_dom hx).2)
      · symm; apply sub_eq_zero.mp h_eq
      · exact h_G_cont
      · exact h_G_deriv
    exact h_G'_ne_0 ξ (h_G_deriv ξ hξ)
      ((h_G_deriv ξ hξ).toDeriv.unique hzero)
  obtain_exist ⟨ξ, hξ, heq⟩
    := Cauchy_MeanValue h_a_lt_b h_dom h_F_cont h_G_cont h_F_deriv h_G_deriv
  exists ξ with hξ
  infer
    ξ ∈ Ioo a b  => G.isDerivableAt ξ
                    := h_G_deriv ξ hξ
                 => g' ξ ≠ 0
                    := h_G'_ne_0 ξ ?_
                 => f' ξ * (g b - g a) = g' ξ * (f b - f a)
                      → (f b - f a) / (g b - g a) = f' ξ / g' ξ
                    := by
                      intro h
                      apply (div_eq_div_iff hG_ne this).mpr
                      linarith
                 => (f b - f a) / (g b - g a) = f' ξ / g' ξ
                    := ?_ heq

end


page_end
