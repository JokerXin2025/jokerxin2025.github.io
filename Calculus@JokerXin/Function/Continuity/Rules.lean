import «Calculus@JokerXin».Function.Continuity.Defs
import «Calculus@JokerXin».Limit.Rules


/-! # Properties of Function's Continuity -/

/-- Function Limit Composition (Special Version)
    - This version requires outer function `F` to be continuous at `u₀` -/
theorem FuncLimit.CompSV {x₀ u₀ L : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F_cont : isContinuousAt F u₀)
  : FuncLimit (F ⊙ G) x₀ (F.map u₀)
:= sorry

/-- Function Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be continuous at `u₀` -/
theorem FuncLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : _lim g x₀ = the u₀)
    (h_f_cont : _lim f u₀ = the (f u₀))
  : _lim (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= sorry

/-- Left Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be left continuous at `u₀` -/
theorem LeftLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : _lim₋ g x₀ = the u₀)
    (h_f_cont : _lim₋ f u₀ = the (f u₀))
  : _lim₋ (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= sorry

/-- Right Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be right continuous at `u₀` -/
theorem RightLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : _lim₊ g x₀ = the u₀)
    (h_f_cont : _lim₊ f u₀ = the (f u₀))
  : _lim₊ (f ∘ g : ℝ → ℝ) x₀ = the (f u₀)
:= sorry

/-- Continuity of Function Addition -/
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= FuncLimit.Add h_F h_G

/-- Continuity of Function Subtraction -/
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= FuncLimit.Sub h_F h_G

/-- Continuity of Function Multiplication -/
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= FuncLimit.Mul h_F h_G

/-- Continuity of Function Division -/
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_F : isContinuousAt F x₀) (h_G : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= FuncLimit.Div h_F h_G h_Gx₀_ne_0

/-- Continuity of Function Composition -/
theorem Continuity.Comp {F G : Function} {x₀ u₀ : ℝ}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F : isContinuousAt F u₀) (h_G : isContinuousAt G x₀)
  : isContinuousAt (F ⊙ G) x₀
:= sorry
