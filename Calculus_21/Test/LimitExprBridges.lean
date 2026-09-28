import «Calculus_21».Limit.Expr.Init

/-! # Tests for limit-expression bridges with custom domains -/

section
variable {a : ℕ → ℝ} {f : ℝ → ℝ} {x₀ L : ℝ} {init : ℕ} {dom : Set ℝ}

example (h : SeqLimit ⟨a, init, none⟩ L) : limₙ a =. the L :=
  h.toSeqLimitExpr

example (h : limₙ a =. the L) : SeqLimit ⟨a, init, none⟩ L :=
  SeqLimit.fromSeqLimitExpr h

example (h : SeqLimitPosInfty ⟨a, init, none⟩) : limₙ a =. pos_infty :=
  h.toSeqLimitExpr

example (h : limₙ a =. infty) : SeqLimitInfty ⟨a, init, none⟩ :=
  SeqLimitInfty.fromSeqLimitExpr h

example (h : FuncLimit ⟨f, dom⟩ x₀ L) : lim x₀ f =. the L :=
  h.toFuncLimitExpr

example (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim x₀ f =. the L) :
    FuncLimit ⟨f, dom⟩ x₀ L :=
  FuncLimit.fromFuncLimitExpr h_dom h

example (h : FuncLimitPosInfty ⟨f, dom⟩ x₀) : lim x₀ f =. pos_infty :=
  h.toFuncLimitExpr

example (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim x₀ f =. infty) :
    FuncLimitInfty ⟨f, dom⟩ x₀ :=
  FuncLimitInfty.fromFuncLimitExpr h_dom h

example (h : LeftLimitNegInfty ⟨f, dom⟩ x₀) : lim₋ x₀ f =. neg_infty :=
  h.toLeftLimitExpr

example (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ x₀ f =. infty) :
    LeftLimitInfty ⟨f, dom⟩ x₀ :=
  LeftLimitInfty.fromLeftLimitExpr h_dom h

example (h : RightLimitInfty ⟨f, dom⟩ x₀) : lim₊ x₀ f =. infty :=
  h.toRightLimitExpr

example (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ x₀ f =. pos_infty) :
    RightLimitPosInfty ⟨f, dom⟩ x₀ :=
  RightLimitPosInfty.fromRightLimitExpr h_dom h

example (h : PosInftyLimitNegInfty ⟨f, dom⟩) : lim pos_infty f =. neg_infty :=
  h.toPosInftyLimitExpr

example (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. infty) :
    PosInftyLimitInfty ⟨f, dom⟩ :=
  PosInftyLimitInfty.fromPosInftyLimitExpr h_dom h

example (h : NegInftyLimitInfty ⟨f, dom⟩) : lim neg_infty f =. infty :=
  h.toNegInftyLimitExpr

example (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. pos_infty) :
    NegInftyLimitPosInfty ⟨f, dom⟩ :=
  NegInftyLimitPosInfty.fromNegInftyLimitExpr h_dom h

example (h : InftyLimitPosInfty ⟨f, dom⟩) : lim infty f =. pos_infty :=
  h.toInftyLimitExpr

example (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. infty) : InftyLimitInfty ⟨f, dom⟩ :=
  InftyLimitInfty.fromInftyLimitExpr h_dom h

example (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
    (h : ¬ FuncConvergesAt ⟨f, dom⟩ x₀) : lim x₀ f =. diverg :=
  FuncLimitExpr.ofNotConverges h_dom h

example (h : lim x₀ f =. diverg) : ¬ FuncConvergesAt ⟨f, dom⟩ x₀ :=
  FuncLimitExpr.toNotConverges h

example (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
    (h : ¬ ConvergesAtInfty ⟨f, dom⟩) : lim infty f =. diverg :=
  InftyLimitExpr.ofNotConverges h_dom h

example (h : lim infty f =. diverg) : ¬ ConvergesAtInfty ⟨f, dom⟩ :=
  InftyLimitExpr.toNotConverges h

end
