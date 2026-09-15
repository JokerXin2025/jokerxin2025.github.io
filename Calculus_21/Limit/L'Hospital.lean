/-
    «Calculus_21».Limit.L'Hospital
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
import «Calculus_21».Differential.MeanValue
set_option linter.style.header false


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

/-- L'Hospital's Rule (`x → x₀`, 0/0 Type) -/
theorem FuncLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : FuncLimit F x₀ 0) (h_G : FuncLimit G x₀ 0)
    (h_deriv : FuncLimit ((Diff F) / (Diff G)) x₀ L)
  : FuncLimit (F / G) x₀ L
:= sorry

page_end
