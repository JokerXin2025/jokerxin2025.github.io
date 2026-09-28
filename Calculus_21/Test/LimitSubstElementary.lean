import «Calculus_21».Limit.Tactics.Subst

section
variable (f : ℝ → ℝ) (a : ℝ)

example : lim a (f ∘ exp) =? Lim (lim a exp) f := by
  lim_subst

example (ha : 0 < a) : lim a (f ∘ ln) =? Lim (lim a ln) f := by
  lim_subst

example (ha : 0 < a) : lim a (f ∘ sqrt) =? Lim (lim a sqrt) f := by
  lim_subst

example : lim 0 (f ∘ sin) =? Lim (lim 0 sin) f := by
  lim_subst

example (ha : -(Real.pi / 2) < a ∧ a < Real.pi / 2) :
    lim a (f ∘ sin) =? Lim (lim a sin) f := by
  lim_subst

example : lim 0 (f ∘ cos) =? Lim (lim 0 cos) f := by
  lim_subst

example : lim 0 (fun x => f (cos x - 1)) =?
    Lim (lim 0 (fun x => cos x - 1)) f := by
  lim_subst

-- Composition uses the inner finite limit and its avoidance certificate.
example : lim a (fun x => f (exp (1 * x + -a))) =?
    Lim (lim a (fun x => exp (1 * x + -a))) f := by
  lim_subst

example : lim a (fun x => f (exp (x ^ 2))) =?
    Lim (lim a (fun x => exp (x ^ 2))) f := by
  lim_subst

example : lim 1 (fun x => f (ln (x ^ 2))) =?
    Lim (lim 1 (fun x => ln (x ^ 2))) f := by
  lim_subst

example : lim 1 (fun x => f (sqrt (x ^ 2))) =?
    Lim (lim 1 (fun x => sqrt (x ^ 2))) f := by
  lim_subst

-- Shifted elementary expressions compose with the algebraic avoidance instances.
example : lim a (fun x => f (sin (x - a))) =?
    Lim (lim a (fun x => sin (x - a))) f := by
  lim_subst

example : lim a (fun x => f (cos (x - a) - 1)) =?
    Lim (lim a (fun x => cos (x - a) - 1)) f := by
  lim_subst

example : lim a (fun x => f (exp (x - a) - 1)) =?
    Lim (lim a (fun x => exp (x - a) - 1)) f := by
  lim_subst

example (ha : a ≠ 0) : lim a (fun x => f (ln (1 + (x - a) / a))) =?
    Lim (lim a (fun x => ln (1 + (x - a) / a))) f := by
  lim_subst

example : lim a (fun x => f (sqrt (1 + (x - a)) - 1)) =?
    Lim (lim a (fun x => sqrt (1 + (x - a)) - 1)) f := by
  lim_subst

-- Arbitrary inner functions need not be continuous or defined by their limit at a.
example (g : ℝ → ℝ) (L : ℝ) [AutoLimit g a L True]
    [AutoAvoidsFiniteLimit g a True]
    (hL : -(Real.pi / 2) < L ∧ L < Real.pi / 2) :
    lim a (fun x => f (sin (g x))) =? Lim (lim a (fun x => sin (g x))) f := by
  lim_subst

example (g : ℝ → ℝ) (L : ℝ) [AutoLimit g a L True]
    [AutoAvoidsFiniteLimit g a True] (hL : L = 0) :
    lim a (fun x => f (sin (g x))) =? Lim (lim a (fun x => sin (g x))) f := by
  lim_subst

example (g : ℝ → ℝ) (L : ℝ) [AutoLimit g a L True]
    [AutoAvoidsFiniteLimit g a True] (hL : L = 0) :
    lim a (fun x => f (cos (g x))) =? Lim (lim a (fun x => cos (g x))) f := by
  lim_subst

example (g : ℝ → ℝ) (L : ℝ) [AutoLimit g a L True]
    [AutoAvoidsFiniteLimit g a True] (hL : 0 < L) :
    lim a (fun x => f (ln (g x))) =? Lim (lim a (fun x => ln (g x))) f := by
  lim_subst

-- Positivity cannot be omitted for logarithm and square root automation.
example : True := by
  fail_if_success
    have : AvoidsFiniteLimit ln 0 := by
      apply AutoAvoidsFiniteLimit.avoids
      auto_side_condition
  fail_if_success
    have : AvoidsFiniteLimit sqrt (-1) := by
      apply AutoAvoidsFiniteLimit.avoids
      auto_side_condition
  fail_if_success
    have : AvoidsFiniteLimit (fun _ : ℝ => exp a) a := by
      apply AutoAvoidsFiniteLimit.avoids
  fail_if_success
    have : AvoidsFiniteLimit (fun _ : ℝ => sin a) a := by
      apply AutoAvoidsFiniteLimit.avoids
  fail_if_success
    have : AvoidsFiniteLimit (fun x : ℝ => cos (x - a + 1)) a := by
      apply AutoAvoidsFiniteLimit.avoids
      auto_side_condition
  trivial

end
