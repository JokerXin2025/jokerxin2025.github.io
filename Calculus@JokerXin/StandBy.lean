import «Calculus_21»


/-- Derivable ⇒ Continuous -/
theorem Derivable_implies_Continuous {F : Function} {x₀ : ℝ}
    (h_deriv : isDerivableAt F x₀)
  : isContinuousAt F x₀
:= sorry


/-- Function Limit → Sequence Limit -/
theorem FuncLimit_toSeq {A : Sequence} {F : Function} {x₀ L : ℝ}
    (h_lim_F : FuncLimit F x₀ L)
    (h_lim_A : SeqLimit A x₀)
    (h_A_in_dom : ∀ n ≥ A.init, A.map n ∈ F.domain)
    (h_A_ne_x₀ : ∃ N : ℕ, ∀ n > N, A.map n ≠ x₀)
  : SeqLimit ⟨F.map ∘ A.map, A.init, A.final⟩ L
:= sorry


/- 这些实例仅用于协助 `lim_luo` 推断导数以避免元变量的出现，不适用于正式的证明工作 -/

private class InferDeriv (f : ℝ → ℝ) (f' : outParam (ℝ → ℝ)) where

private instance deriv_patch₁ {k : ℝ}
  : InferDeriv (k + ·) (const 1) where

private instance deriv_patch₁' {f f' : ℝ → ℝ} {k : ℝ}
    [InferDeriv f f']
  : InferDeriv ((k + ·) ∘ f) f' where

private instance deriv_patch₂ {k : ℝ}
  : InferDeriv (k - ·) (const (-1)) where

private instance deriv_patch2' {f f' : ℝ → ℝ} {k : ℝ}
    [InferDeriv f f']
  : InferDeriv ((k - ·) ∘ f) (-f') where

private instance deriv_patch₃ {k : ℝ}
  : InferDeriv (k * ·) (const k) where

private instance deriv_patch₃' {f f' : ℝ → ℝ} {k : ℝ}
    [InferDeriv f f']
  : InferDeriv ((k * ·) ∘ f) (k • f') where

private instance deriv_patch₄ {k : ℝ}
  : InferDeriv (k / ·) (fun x ↦ -k / x ^ 2) where

private instance deriv_patch₄' {f f' : ℝ → ℝ} {k : ℝ}
    [InferDeriv f f']
  : InferDeriv ((k / ·) ∘ f) (fun x ↦ -k * f' x / (f x ^ 2)) where

private instance deriv_patch₅
  : InferDeriv (-·) (const (-1)) where

private instance deriv_patch₅' {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv ((-·) ∘ f) (-f') where

private instance deriv_patch₆
  : InferDeriv (·⁻¹) (fun x ↦ -1 / x ^ 2) where

private instance deriv_patch₆' {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv ((·⁻¹) ∘ f) (fun x ↦ - f' x / (f x ^ 2)) where

private instance deriv_Constant {C : ℝ}
  : InferDeriv (const C) (const 0) where

private instance deriv_Constant' {C : ℝ}
  : InferDeriv (fun _ ↦ C) (const 0) where

private instance deriv_Identity
  : InferDeriv id (const 1) where

private instance deriv_Identity'
  : InferDeriv (·) (const 1) where

private instance deriv_SMul {f f' : ℝ → ℝ} {k : ℝ}
    [InferDeriv f f']
  : InferDeriv (k • f) (k • f') where

private instance deriv_Neg {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv (-f) (-f') where

private instance deriv_Neg' {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv (fun x ↦ - f x) (-f') where

private instance deriv_Inv {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv f⁻¹ (fun x ↦ - f' x / f x ^ 2) where

private instance deriv_Inv' {f f' : ℝ → ℝ}
    [InferDeriv f f']
  : InferDeriv (fun x ↦ (f x)⁻¹) (fun x ↦ - f' x / f x ^ 2) where

private instance deriv_Add {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (f + g) (f' + g') where

private instance deriv_Add' {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (fun x ↦ f x + g x) (f' + g') where

private instance deriv_Sub {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (f - g) (f' - g') where

private instance deriv_Sub' {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (fun x ↦ f x - g x) (f' - g') where

private instance deriv_Mul {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (f * g) (fun x ↦ f' x * g x + f x * g' x) where

private instance deriv_Mul' {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (fun x ↦ f x * g x) (fun x ↦ f' x * g x + f x * g' x) where

private instance deriv_Div {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (f / g)
    (fun x ↦ (f' x * g x - f x * g' x) / g x ^ 2) where

private instance deriv_Div' {f f' g g' : ℝ → ℝ}
    [InferDeriv f f'] [InferDeriv g g']
  : InferDeriv (fun x ↦ f x / g x)
    (fun x ↦ (f' x * g x - f x * g' x) / g x ^ 2) where

private instance deriv_Abs
  : InferDeriv abs (fun x ↦ x / |x|) where

private instance deriv_Sqrt
  : InferDeriv sqrt (fun x ↦ 1 / (2 * √x)) where

private instance deriv_Power {a : ℝ}
  : InferDeriv (pow a) (fun x ↦ a * x ^ (a - 1)) where

private instance deriv_Power_ℤ {n : ℤ}
  : InferDeriv (npow n) (fun x ↦ n * x ^ (n - 1)) where

private instance deriv_Power_ℤ' {n : ℤ}
  : InferDeriv (· ^ n) (fun x ↦ n * x ^ (n - 1)) where

private instance deriv_Power_ℕ {n : ℕ}
  : InferDeriv (npow n) (fun x ↦ n * x ^ ((n - 1) : ℤ)) where

private instance deriv_Power_ℕ' {n : ℕ}
  : InferDeriv (· ^ n) (fun x ↦ n * x ^ ((n - 1) : ℤ)) where

private instance deriv_Exp
  : InferDeriv exp exp where

private instance deriv_Expow {a : ℝ}
  : InferDeriv (a ^ ·) (fun x ↦ ln a * a ^ x) where

private instance deriv_Ln
  : InferDeriv ln (·⁻¹) where

private instance deriv_Log {a : ℝ}
  : InferDeriv (log a) (fun x ↦ 1 / (ln a * x)) where

private instance deriv_Sin
  : InferDeriv sin cos where

private instance deriv_Cos
  : InferDeriv cos (-sin) where

private instance deriv_Tan
  : InferDeriv tan (sec ^ 2) where

private instance deriv_Cot
  : InferDeriv cot (- csc ^ 2) where

private instance deriv_Sec
  : InferDeriv sec (tan * sec) where

private instance deriv_Csc
  : InferDeriv csc (cot * csc) where

private instance deriv_Sinh
  : InferDeriv sinh cosh where

private instance deriv_Cosh
  : InferDeriv cosh sinh where

private instance deriv_Tanh
  : InferDeriv tanh (sech ^ 2) where

private instance deriv_Coth
  : InferDeriv coth (- csch ^ 2) where

private instance deriv_Sech
  : InferDeriv sech (tanh * sech) where

private instance deriv_Csch
  : InferDeriv csch (- coth * csch) where

private instance deriv_Arcsin
  : InferDeriv arcsin (fun x ↦ 1 / √(1 - x ^ 2)) where

private instance deriv_Arccos
  : InferDeriv arccos (fun x ↦ -1 / √(1 - x ^ 2)) where

private instance deriv_Arctan
  : InferDeriv arctan (fun x ↦ 1 / (1 + x ^ 2)) where

private instance deriv_Arccot
  : InferDeriv arccot (fun x ↦ -1 / (1 + x ^ 2)) where

private instance deriv_Arcsec
  : InferDeriv arcsec (fun x ↦ 1 / (|x| * √(x ^ 2 - 1))) where

private instance deriv_Arccsc
  : InferDeriv arccsc (fun x ↦ -1 / (|x| * √(x ^ 2 - 1))) where

/- # To be Modified ↓ -/
/-
/-- ### 单位分式的函数极限表达式 !!!!!
    ### Equal-to-one-fractional Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma FuncLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的左极限表达式 !!!!!
    ### Equal-to-one-fractional Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma LeftLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₋ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的右极限表达式 !!!!!
    ### Equal-to-one-fractional Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma RightLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₊ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的负无穷处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma NegInftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim₋∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 单位分式的正无穷处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma PosInftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim₊∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 单位分式的无穷远处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma InftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 函数极限表达式的强制左约分
    ### Forced Left Reduction of Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma FuncLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim ((f * g) / (f * g')) x₀ = lim (g / g') x₀
:= sorry

/-- ### 函数极限表达式的强制右约分
    ### Forced Right Reduction of Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma FuncLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim ((f * g) / (f' * g)) x₀ = lim (f / f') x₀
:= sorry

/-- ### 左极限表达式的强制左约分
    ### Forced Left Reduction of Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma LeftLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₋ ((f * g) / (f * g')) x₀ = lim₋ (g / g') x₀
:= sorry

/-- ### 左极限表达式的强制右约分
    ### Forced Right Reduction of Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma LeftLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₋ ((f * g) / (f' * g)) x₀ = lim₋ (f / f') x₀
:= sorry

/-- ### 右极限表达式的强制左约分
    ### Forced Left Reduction of Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma RightLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₊ ((f * g) / (f * g')) x₀ = lim₊ (g / g') x₀
:= sorry

/-- ### 右极限表达式的强制右约分
    ### Forced Right Reduction of Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma RightLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₊ ((f * g) / (f' * g)) x₀ = lim₊ (f / f') x₀
:= sorry

/-- ### 负无穷处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma NegInftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim₋∞ ((f * g) / (f * g')) = lim₋∞ (g / g')
:= sorry

/-- ### 负无穷处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma NegInftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim₋∞ ((f * g) / (f' * g)) = lim₋∞ (f / f')
:= sorry

/-- ### 正无穷处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma PosInftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim₊∞ ((f * g) / (f * g')) = lim₊∞ (g / g')
:= sorry

/-- ### 正无穷处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma PosInftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim₊∞ ((f * g) / (f' * g)) = lim₊∞ (f / f')
:= sorry

/-- ### 无穷远处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma InftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim∞ ((f * g) / (f * g')) = lim∞ (g / g')
:= sorry

/-- ### 无穷远处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma InftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim∞ ((f * g) / (f' * g)) = lim∞ (f / f')
:= sorry
-/
