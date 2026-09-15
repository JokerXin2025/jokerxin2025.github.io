/-
    «Calculus_21».Ind_Integral.Tactics.ByParts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Ind_Integral.Tactics.Notice
set_option linter.style.header false


/-! # Preparations -/

lemma autoByParts {f f₀ g g' : ℝ → ℝ} {cond : Prop} (F : ℝ → ℝ)
    [AutoIndefIntegral F f₀ cond] [AutoIndefIntegral g g' cond]
    (h_cond : cond) (h_f_eq_f₀ : f = f₀)
  : ∫ (fun x ↦ f x * g x) = the ⟦fun x ↦ F x * g x⟧ - ∫ (fun x ↦ F x * g' x)
:= sorry


/-! # Tactics -/

macro "int_by_parts" F:term : tactic => `(tactic| (
  intros
  try simp only [except_bind_ok, except_pure_ok, addC_val, addC_func]
  rw [autoByParts (F := $F)]
  all_goals try {auto_side_condition}
  all_goals try {congr; auto_eq}
))

example
  : ∫ (fun x ↦ sin x * x^2)
    = the (fun x ↦ - x^2 * cos x + 2 * x * sin x - 2 * cos x +C)
:= by sorry
/- calc
        ∫ (fun x ↦ sin x * x^2)
  _  =  the (fun x ↦ - cos x * x^2 +C) - ∫ (fun x ↦ - cos x * (2 * x))
        := by int_by_parts (fun x ↦ - cos x)
  _  =  the (fun x ↦ - cos x * x^2 +C)
        - (the (fun x ↦ - sin x * (2 * x) +C) - ∫ (fun x ↦ - sin x * 2))
        := by int_by_parts (fun x ↦ - sin x)
  _  =  the (fun x ↦ - cos x * x^2 +C)
        - (the (fun x ↦ - sin x * (2 * x) +C) - the (fun x ↦ 2 * cos x +C))
        := by int_notice
  _  =  the ((fun x ↦ - x^2 * cos x + 2 * x * sin x - 2 * cos x) +C)
         := by admit -/

page_end
