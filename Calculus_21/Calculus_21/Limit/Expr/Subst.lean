import «Calculus_21».Limit.Expr.Init

set_option linter.style.header false

/-- A limit whose approach point is itself a limit expression. Divergence without
an infinite limit, and unknown values, do not specify an approach point. -/
noncomputable def LimitAtExpr (A : LimitValue) (f : ℝ → ℝ) : LimitValue :=
  match A with
  | .finite b => FuncLimitExpr b f
  | .posInfty => PosInftyLimitExpr f
  | .negInfty => NegInftyLimitExpr f
  | .unsignedInfty => InftyLimitExpr f
  | _ => .unknownLimit

macro "Lim" : term => `(LimitAtExpr)

@[simp] theorem LimitAtExpr.finite (b : ℝ) (f : ℝ → ℝ) :
    Lim (the b) f = lim b f := rfl

@[simp] theorem LimitAtExpr.unknown (f : ℝ → ℝ) :
    Lim unknown f = unknown := rfl

@[simp] theorem LimitAtExpr.divergence (f : ℝ → ℝ) :
    Lim diverg f = unknown := rfl

@[simp] theorem LimitAtExpr.posInfty (f : ℝ → ℝ) :
    Lim pos_infty f = lim pos_infty f := rfl

@[simp] theorem LimitAtExpr.negInfty (f : ℝ → ℝ) :
    Lim neg_infty f = lim neg_infty f := rfl

@[simp] theorem LimitAtExpr.unsignedInfty (f : ℝ → ℝ) :
    Lim infty f = lim infty f := rfl

/-- The inner function eventually avoids the puncture of the outer limit. -/
def LocallyAvoids (g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ Nbhd a δ, g x ≠ b

/-- A conditional certificate; it does not assert that a finite limit exists. -/
def AvoidsFiniteLimit (g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ b : ℝ, lim a g =. the b → LocallyAvoids g a b

/-- Finite composition, proved directly without the unfinished `FuncLimit.Comp`. -/
theorem FuncLimitExpr.CompFinite {f g : ℝ → ℝ} {a b L : ℝ}
    (hg : lim a g =. the b) (havoid : LocallyAvoids g a b)
    (hf : lim b f =. the L) : lim a (f ∘ g) =. the L := by
  have hg' := FuncLimit.fromFuncLimitExpr (dom := Set.univ)
    ⟨1, zero_lt_one, by simp⟩ hg
  have hf' := FuncLimit.fromFuncLimitExpr (dom := Set.univ)
    ⟨1, zero_lt_one, by simp⟩ hf
  apply FuncLimit.toFuncLimitExpr (dom := Set.univ)
  refine ⟨⟨1, zero_lt_one, by simp⟩, ?_⟩
  intro ε hε
  obtain ⟨η, hη, houter⟩ := hf'.2 ε hε
  obtain ⟨δ, hδ, hinner⟩ := hg'.2 η hη
  obtain ⟨r, hr, hne⟩ := havoid
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro x hx
  have hxδ : x ∈ Nbhd a δ :=
    ⟨by linarith [hx.1, min_le_left δ r],
      by linarith [hx.2.1, min_le_left δ r], hx.2.2⟩
  have hxr : x ∈ Nbhd a r :=
    ⟨by linarith [hx.1, min_le_right δ r],
      by linarith [hx.2.1, min_le_right δ r], hx.2.2⟩
  exact houter (g x) ⟨(hinner x hxδ).1, (hinner x hxδ).2, hne x hxr⟩

/-- Composition through positive infinity requires no finite-value avoidance. -/
theorem FuncLimitExpr.CompPosInfty {f g : ℝ → ℝ} {a L : ℝ}
    (hg : lim a g =. pos_infty) (hf : lim pos_infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  have hg' : FuncLimitPosInfty ⟨g, Set.univ⟩ a := GenericExprBridge.mp hg
  have hf' : PosInftyLimit ⟨f, Set.univ⟩ L := GenericExprBridge.mp hf
  apply FuncLimit.toFuncLimitExpr (dom := Set.univ)
  refine ⟨⟨1, zero_lt_one, by simp⟩, ?_⟩
  intro ε hε
  obtain ⟨M, hM, houter⟩ := hf'.2 ε hε
  obtain ⟨δ, hδ, hinner⟩ := hg'.2 M hM
  exact ⟨δ, hδ, fun x hx => houter (g x) (hinner x hx)⟩

/-- Composition through negative infinity requires no finite-value avoidance. -/
theorem FuncLimitExpr.CompNegInfty {f g : ℝ → ℝ} {a L : ℝ}
    (hg : lim a g =. neg_infty) (hf : lim neg_infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  have hg' : FuncLimitNegInfty ⟨g, Set.univ⟩ a := GenericExprBridge.mp hg
  have hf' : NegInftyLimit ⟨f, Set.univ⟩ L := GenericExprBridge.mp hf
  apply FuncLimit.toFuncLimitExpr (dom := Set.univ)
  refine ⟨⟨1, zero_lt_one, by simp⟩, ?_⟩
  intro ε hε
  obtain ⟨M, hM, houter⟩ := hf'.2 ε hε
  obtain ⟨δ, hδ, hinner⟩ := hg'.2 M hM
  exact ⟨δ, hδ, fun x hx => houter (g x) (hinner x hx)⟩

/-- With unsigned infinity the outer limit must control both tails. -/
theorem FuncLimitExpr.CompInfty {f g : ℝ → ℝ} {a L : ℝ}
    (hg : lim a g =. infty) (hf : lim infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  have hg' : FuncLimitInfty ⟨g, Set.univ⟩ a := GenericExprBridge.mp hg
  have hf' : InftyLimit ⟨f, Set.univ⟩ L := GenericExprBridge.mp hf
  apply FuncLimit.toFuncLimitExpr (dom := Set.univ)
  refine ⟨⟨1, zero_lt_one, by simp⟩, ?_⟩
  intro ε hε
  obtain ⟨M, hM, hneg, hpos⟩ := hf'.2 ε hε
  obtain ⟨δ, hδ, hinner⟩ := hg'.2 M hM
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rcases lt_abs.mp (hinner x hx) with h | h
  · exact hpos (g x) h
  · apply hneg (g x)
    change g x < -M
    change M < -g x at h
    linarith

/-- Substitute before computing the inner limit. Properness supplies a finite
outer limit; the inner limit may be finite or any of the three infinities. -/
theorem FuncLimitExpr.SubstNested {f g : ℝ → ℝ} {a : ℝ}
    (havoid : AvoidsFiniteLimit g a) :
    lim a (f ∘ g) =? Lim (lim a g) f := by
  intro hproper
  cases hg : lim a g with
  | finite b =>
      rw [hg] at hproper
      change (lim b f).isProper at hproper
      obtain ⟨L, hL⟩ := LimitValue.isProper.getEqual! hproper
      have hg' : lim a g =. the b := PolyCalc.pe_of_eq hg
      change lim a (f ∘ g) =. lim b f
      rw [hL]
      exact FuncLimitExpr.CompFinite hg' (havoid b hg') (PolyCalc.pe_of_eq hL)
  | posInfty =>
      rw [hg] at hproper
      change (lim pos_infty f).isProper at hproper
      obtain ⟨L, hL⟩ := LimitValue.isProper.getEqual! hproper
      change lim a (f ∘ g) =. lim pos_infty f
      rw [hL]
      exact CompPosInfty (PolyCalc.pe_of_eq hg) (PolyCalc.pe_of_eq hL)
  | negInfty =>
      rw [hg] at hproper
      change (lim neg_infty f).isProper at hproper
      obtain ⟨L, hL⟩ := LimitValue.isProper.getEqual! hproper
      change lim a (f ∘ g) =. lim neg_infty f
      rw [hL]
      exact CompNegInfty (PolyCalc.pe_of_eq hg) (PolyCalc.pe_of_eq hL)
  | unsignedInfty =>
      rw [hg] at hproper
      change (lim infty f).isProper at hproper
      obtain ⟨L, hL⟩ := LimitValue.isProper.getEqual! hproper
      change lim a (f ∘ g) =. lim infty f
      rw [hL]
      exact CompInfty (PolyCalc.pe_of_eq hg) (PolyCalc.pe_of_eq hL)
  | unknownLimit | divergence =>
      rw [hg] at hproper
      exact False.elim hproper
