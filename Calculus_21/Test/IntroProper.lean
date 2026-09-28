import «Calculus_21».Limit.Expr.ProperReflect

variable {A : LimitValue}

example : (the (0 : ℝ)) =. the 0 := by
  script_given_proper
  rfl

example : A =? A := by
  script_intro_proper' h_proper
  rfl

example (n : ℕ) : A =? A := by
  induction n with
  | zero =>
    script_intro_proper' h_proper
    rfl
  | succ _ ih =>
    script_intro_proper' h_proper
    rfl
