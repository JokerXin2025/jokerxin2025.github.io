/-
    «Calculus_21».Limit.Tactics.Luo
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Cont
import «Calculus_21».Differential.Tactic
set_option linter.style.header false


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

    - `lim_luo` tries to apply L'Hospital's rule once to the limit expression.

    __Examples__
    ```lean
    ```
-/
macro "lim_luo" : tactic => `(tactic| {
  first
  | apply L'Hospital_x₀_zero
  · lim_cont; done
  · lim_cont; done
  all_goals
    use 1
    constructor
    · repeat any_goals apply And.intro
      all_goals first
      | nlinarith
      | norm_num
      done
    · intros
      repeat rw [autoDeriv]
      any_goals
        all_goals try simp_all only [
          Nbhd, one_div, zero_sub, zero_add, ne_eq, mem_setOf_eq, gt_iff_lt
        ]
        auto_side_condition
      try focus auto_eq
      done
})

page_end
