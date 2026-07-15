import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Function.Differential.Defs


/-- L'Hospital's Rule (`x → x₀`, 0/0 Type) -/
theorem FuncLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : FuncLimit F x₀ 0) (h_G : FuncLimit G x₀ 0)
    (h_deriv : FuncLimit ((Diff F) / (Diff G)) x₀ L)
  : FuncLimit (F / G) x₀ L
:= sorry

/-- L'Hospital's Rule (`x → x₀`, 0/0 Type) (Expression) -/
theorem FuncLimitExpr.L'Hospital_x₀_zero {f g : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : _lim f x₀ = the 0) (h_g : _lim g x₀ = the 0)
    (h_deriv : _lim (f / g) x₀ = the L)
  : _lim (f / g) x₀ = the L
:= sorry

/-- L'Hospital's Rule (`x → x₀`, 0/0 Type, Left Limit) -/
theorem LeftLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : LeftLimit F x₀ 0) (h_G : LeftLimit G x₀ 0)
    (h_deriv : LeftLimit ((Diff F) / (Diff G)) x₀ L)
  : LeftLimit (F / G) x₀ L
:= sorry

/-- L'Hospital's Rule (`x → x₀`, 0/0 Type, Right Limit) -/
theorem RightLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : RightLimit F x₀ 0) (h_G : RightLimit G x₀ 0)
    (h_deriv : RightLimit ((Diff F) / (Diff G)) x₀ L)
  : RightLimit (F / G) x₀ L
:= sorry
