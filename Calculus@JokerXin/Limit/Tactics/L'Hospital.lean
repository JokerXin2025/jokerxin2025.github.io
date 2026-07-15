import «Calculus@JokerXin».Tactics
import «Calculus@JokerXin».Limit.Tactics.Simplify
import «Calculus@JokerXin».Function.Differential.Tactic


/-! # Preparations -/

private theorem L'Hospital_x₀_zero {f g f' g' : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : lim f x₀ = the 0) (h_g : lim g x₀ = the 0)
    (h_f' : ∀ x > -1, D f x = the (f' x))
    (h_g' : ∀ x > 0, D g x = the (g' x))
    (h_luo : lim (f' / g') x₀ = L)
  : lim (f / g) x₀ = the L
:= sorry

example : lim (fun x ↦ ln (x + 1) / sin x) 0 = the 1 := by
  apply L'Hospital_x₀_zero
  · lim_simp
  · lim_simp
  ·

example : ∀ x > 0 , D (fun x ↦ ln x) x = the 1 := by deriv


/-! # Tactics -/

/-- ## Application of L'Hôpital's Rules

    __Usage__ `lim_luo`

-/
macro "lim_luo" : tactic => `(tactic| {
  first
  | apply L'Hospital_x₀_zero
  · lim_simp
  · lim_simp
  simp (
    discharger := (
      repeat any_goals apply And.intro
      try recover_form
      all_goals first
      | trivial
      | tauto
      | positivity
      | nlinarith
      | norm_num  -- the last choice
    )
  ) only [autoDeriv]
  try expr_simp
  try expr_convert
  lim_simp
})
macro "lim_luo!" : tactic => `(tactic| {
  repeat
    first
    | apply L'Hospital_x₀_zero
    · lim_simp
    · lim_simp
    simp (
      discharger := (
        repeat any_goals apply And.intro
        try recover_form
        all_goals first
        | trivial
        | tauto
        | positivity
        | nlinarith
        | norm_num  -- the last choice
      )
    ) only [autoDeriv]
    try expr_simp
  try expr_convert
  lim_simp
})

example
  : lim (fun x ↦ sin x / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ (exp x - 1) / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ ln (x + 1) / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ arctan x / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ (x^2 - 1) / (x - 1)) 1 = the 2
:= by lim_luo

example
  : lim (fun x ↦ (exp (2 * x) - 1) / sin x) 0 = the 2
:= by lim_luo

example
  : lim (fun x ↦ (1 - cos x) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - x - 1) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (cosh x - 1) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (x^4 - 4 * x + 3) / (x - 1)^2) 1 = the 6
:= by lim_luo!

example
  : lim (fun x ↦ (exp (x^2) - 1) / (1 - cos x)) 0 = the 2
:= by lim_luo!

example
  : lim (fun x ↦ (x - sin x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (tan x - x) / x^3) 0 = the (1 / 3)
:= by lim_luo!

example
  : lim (fun x ↦ (sinh x - x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (arcsin x - x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (cos x - 1 + x^2 / 2) / x^4) 0 = the (1 / 24)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2 - x^3 / 6) / x^4) 0 = the (1 / 24)
:= by lim_luo!

example
  : lim (fun x ↦ (sin x - x + x^3 / 6) / x^5) 0 = the (1 / 120)
:= by lim_luo!

example
  : lim (fun x ↦ (sinh x - x - x^3 / 6) / x^5) 0 = the (1 / 120)
:= by lim_luo!
