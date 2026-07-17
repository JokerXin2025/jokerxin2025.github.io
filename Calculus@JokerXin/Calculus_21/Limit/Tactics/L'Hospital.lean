import «Calculus_21».Limit.Tactics.Simplify
import «Calculus_21».Differential.Tactic


/-! # Preparations -/

private theorem L'Hospital_x₀_zero {f f' g g' : ℝ → ℝ} {x₀ : ℝ}
    (h_f : lim f x₀ = the 0) (h_g : lim g x₀ = the 0)
    (h_f' : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, D f x = the (f' x))
    (h_g' : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, D g x = the (g' x))
  : lim (f / g) x₀ =? lim (f' / g') x₀
:= sorry


/-! # Tactics -/

/-- ## Single Application of L'Hôpital's Rules

    __Usage__ `lim_luo`

-/
macro "lim_luo" : tactic => `(tactic| {
  first
  | apply L'Hospital_x₀_zero
  · lim_simp
  · lim_simp
  · use 1
    constructor
    · repeat any_goals apply And.intro
      all_goals first
      | nlinarith
      | norm_num
    · intros
      repeat rw [autoDeriv]
      any_goals
        repeat any_goals apply And.intro
        all_goals try simp_all only [
          Nbhd, one_div, zero_sub, zero_add, ne_eq, mem_setOf_eq, gt_iff_lt
        ]
        all_goals first
        | trivial
        | tauto
        | positivity
        | nlinarith
        | norm_num
      try · auto_eq
  · use 1
    constructor
    · repeat any_goals apply And.intro
      all_goals first
      | nlinarith
      | norm_num
    · intros
      repeat rw [autoDeriv]
      any_goals
        repeat any_goals apply And.intro
        all_goals try simp_all only [
          Nbhd, one_div, zero_sub, zero_add, ne_eq, mem_setOf_eq, gt_iff_lt
        ]
        all_goals first
        | trivial
        | tauto
        | positivity
        | nlinarith
        | norm_num
      try · auto_eq
})
