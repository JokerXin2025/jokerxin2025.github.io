import «Calculus_21».Limit.Expr


/-! ## 无穷小 Infinitesimal -/

/-- ### 无穷小
    ### Infinitesimal -/
-- @[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0)$" Text]
abbrev isInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  FuncLimit F x₀ 0

/-- ### 左无穷小
    ### Left Infinitesimal -/
-- @[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^-)$" Text]
abbrev isLeftInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  LeftLimit F x₀ 0

/-- ### 右无穷小
    ### Right Infinitesimal -/
-- @[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^+)$" Text]
abbrev isRightInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  RightLimit F x₀ 0
