/-
    «Calculus_21».Continuity.ClosedInterval
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Continuity.Defs
set_option linter.style.header false


/-! # Continuous Functions on Closed Interval -/

section
variable {F : Function} {l r C : ℝ}

lemma isContinuousInIcc.continuousOn
    (h_cont : isContinuousInIcc F l r)
  : ContinuousOn F.map (Icc l r)
:= by
  intro x h_x
  apply Metric.continuousWithinAt_iff.mpr
  intro ε h_ε
  by_cases h_xl : x = l
  · subst x
    rcases h_cont.2.1.2.2 ε h_ε with ⟨δ, hδ, hmap⟩
    refine ⟨δ, hδ, ?_⟩
    intro y hy hydist
    by_cases hyl : y = l
    · subst y
      simpa using h_ε
    · have hyIoo : y ∈ Ioo l (l + δ) := by
        rw [Real.dist_eq] at hydist
        constructor
        · exact lt_of_le_of_ne hy.1 (Ne.symm hyl)
        · linarith [lt_of_abs_lt hydist]
      have := hmap y hyIoo
      rw [Nbho_abs] at this
      simpa [Real.dist_eq, abs_sub_comm] using this
  · by_cases h_xr : x = r
    · subst x
      rcases h_cont.2.2.2.2 ε h_ε with ⟨δ, hδ, hmap⟩
      refine ⟨δ, hδ, ?_⟩
      intro y hy hydist
      by_cases hyr : y = r
      · subst y
        simpa using h_ε
      · have hyIoo : y ∈ Ioo (r - δ) r := by
          rw [Real.dist_eq] at hydist
          constructor
          · linarith [neg_lt_of_abs_lt hydist]
          · exact lt_of_le_of_ne hy.2 hyr
        have := hmap y hyIoo
        rw [Nbho_abs] at this
        simpa [Real.dist_eq, abs_sub_comm] using this
    · rcases h_cont.1 x ⟨lt_of_le_of_ne h_x.1 (Ne.symm h_xl),
        lt_of_le_of_ne h_x.2 h_xr⟩ with ⟨_, hlim⟩
      rcases hlim.2 ε h_ε with ⟨δ, hδ, hmap⟩
      refine ⟨δ, hδ, ?_⟩
      intro y _ hydist
      by_cases hyx : y = x
      · subst y
        simpa using h_ε
      · have hyNbhd : y ∈ Nbhd x δ := by
          rw [Real.dist_eq] at hydist
          rw [mem_Nbhd]
          constructor
          · linarith [neg_lt_of_abs_lt hydist]
          · exact ⟨by linarith [lt_of_abs_lt hydist], hyx⟩
        have := hmap y hyNbhd
        rw [Nbho_abs] at this
        simpa [Real.dist_eq, abs_sub_comm] using this

/-- Minimum Values Theorem -/
@theorem Min_Existence
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMinimumPointOn F (Icc l r) m
:= by
  change ∃ m ∈ Icc l r, IsMinOn F.map (Icc l r) m
  apply isCompact_Icc.exists_isMinOn
  · exact nonempty_Icc.mpr h_l_lt_r.le
  · exact h_cont.continuousOn

/-- Maximum Values Theorem -/
@theorem Max_Existence
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMaximumPointOn F (Icc l r) m
:= by
  change ∃ m ∈ Icc l r, IsMaxOn F.map (Icc l r) m
  apply isCompact_Icc.exists_isMaxOn
  · exact nonempty_Icc.mpr h_l_lt_r.le
  · exact h_cont.continuousOn

/-- Intermediate Value Theorem -/
@theorem Interm_Existence
    (h_l_lt_r : l < r)
    (_h_l_in_dom : l ∈ F.domain)
    (_h_r_in_dom : r ∈ F.domain)
    (h_interm : F.map l < C ∧ C < F.map r
                ∨ F.map r < C ∧ C < F.map l)
    (h_cont : isContinuousInIcc F l r)
  : ∃ c ∈ Ioo l r, F.map c = C
:= by
  have hmath := h_cont.continuousOn
  rcases h_interm with hinc | hdec
  · rcases intermediate_value_Icc h_l_lt_r.le hmath ⟨hinc.1.le, hinc.2.le⟩ with
      ⟨c, hc, hfc⟩
    exists c
    refine ⟨?_, hfc⟩
    constructor
    · apply lt_of_le_of_ne hc.1
      intro h
      subst c
      linarith
    · apply lt_of_le_of_ne hc.2
      intro h
      subst c
      linarith
  · rcases intermediate_value_Icc' h_l_lt_r.le hmath ⟨hdec.1.le, hdec.2.le⟩ with
      ⟨c, hc, hfc⟩
    exists c
    refine ⟨?_, hfc⟩
    constructor
    · apply lt_of_le_of_ne hc.1
      intro h
      subst c
      linarith
    · apply lt_of_le_of_ne hc.2
      intro h
      subst c
      linarith

end


page_end
