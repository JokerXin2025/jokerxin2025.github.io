import «Calculus_21».Integral.Expr

/-! # Fundamental calculus laws

All interval hypotheses use the closed, orientation-independent `Integral.interval`.
Derivatives are two-sided, including at both endpoints. Integrability is required
explicitly; no global differentiability or continuity is inferred from an indefinite result.
-/

namespace IntegralExpr

/-- Newton-Leibniz from derivatives only on the closed interval. -/
theorem newtonLeibniz {f F : ℝ → ℝ} {a b : ℝ}
    (hDeriv : ∀ x ∈ Integral.interval a b, D F x =. the (f x))
    (hInt : (total f).isIntegrableOn a b) :
    IntegralExpr f a b =. the (F b - F a) := by
  apply Integral.toIntegralExpr (F := total f)
  apply DefIntegral.newtonLeibniz (G := total F) hInt (fun _ _ => trivial)
  intro x hx
  exact Deriv.fromDerivExpr ⟨1, zero_lt_one, fun _ _ => trivial⟩ (hDeriv x hx)

end IntegralExpr

/-- Evaluate an indefinite result with explicit avoidance of derivative failures.
The hypothesis `h` records the result but is logically redundant. -/
theorem IndefiniteExpr.toIntegralExpr {f F : ℝ → ℝ} {a b : ℝ}
    (h : ∫ f =. prim F)
    (havoid : Disjoint (Integral.interval a b) {x | ¬ (D F x =. the (f x))})
    (hInt : (total f).isIntegrableOn a b) :
    IntegralExpr f a b =. the (F b - F a) :=
  IntegralExpr.newtonLeibniz (fun x hx => by
    simpa only [Set.mem_setOf_eq, not_not] using Set.disjoint_left.mp havoid hx) hInt

/-- An indefinite result supplies one countable exceptional set and the definite
evaluation law for every integrable interval avoiding that same set. -/
theorem IndefiniteExpr.newtonLeibniz {f F : ℝ → ℝ} (h : ∫ f =. prim F) :
    ∃ s : Set ℝ, s.Countable ∧ (∀ x ∉ s, D F x =. the (f x)) ∧
      ∀ a b, (∀ x ∈ Integral.interval a b, x ∉ s) →
        (total f).isIntegrableOn a b → IntegralExpr f a b =. the (F b - F a) := by
  obtain ⟨s, hsc, hs⟩ := IndefiniteExpr.spec.mp h
  exact ⟨s, hsc, hs, fun _ _ havoid hInt =>
    IntegralExpr.newtonLeibniz (fun x hx => hs x (havoid x hx)) hInt⟩

namespace IntegralExpr

/-- Integration by parts with interval-local derivatives and both integrands
integrable. This also applies to reversed and degenerate intervals. -/
theorem integrationByParts {F G f g : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Integral.interval a b, D F x =. the (f x))
    (hG : ∀ x ∈ Integral.interval a b, D G x =. the (g x))
    (hIntFg : (total (fun x => F x * g x)).isIntegrableOn a b)
    (hIntfG : (total (fun x => f x * G x)).isIntegrableOn a b) :
    IntegralExpr (fun x => F x * g x) a b =.
      the (F b * G b - F a * G a) - IntegralExpr (fun x => f x * G x) a b := by
  obtain ⟨v, hv⟩ := hIntFg
  obtain ⟨w, hw⟩ := hIntfG
  have hprod : IntegralExpr (fun x => F x * g x + f x * G x) a b =.
      the (F b * G b - F a * G a) := by
    apply newtonLeibniz (F := fun x => F x * G x) _ (hv.add hw).total.isIntegrableOn
    intro x hx
    apply EqualIfProper.reintroduce (by trivial)
    calc
      _ =? D F x * the (G x) + D G x * the (F x) := DerivExpr.Mul
      _ = the (F x * g x + f x * G x) := by
        poly_rw [hF x hx, hG x hx]
        change the (f x * G x + g x * F x) = the (F x * g x + f x * G x)
        congr 1
        ring
  have hsum : v + w = F b * G b - F a * G a :=
    (hv.add hw).total.unique (finite_iff.mp (LimitValue.finite_iff.mp hprod))
  apply PolyCalc.pe_of_eq
  have hvExpr : IntegralExpr (fun x => F x * g x) a b = the v := finite_iff.mpr hv
  have hwExpr : IntegralExpr (fun x => f x * G x) a b = the w := finite_iff.mpr hw
  rw [hvExpr, hwExpr]
  change the v = the (F b * G b - F a * G a - w)
  congr 1
  linarith

/-- Substitution from an indefinite result and avoidance of actual derivative
failures on the image. Its preimage need not be countable, and `g` need not be
globally differentiable or monotone. The result `h` is logically redundant. -/
theorem substitutionValue {f F g g' : ℝ → ℝ} {a b : ℝ}
    (h : ∫ f =. prim F)
    (hg : ∀ x ∈ Integral.interval a b, D g x =. the (g' x))
    (himage : Disjoint (g '' Integral.interval a b) {y | ¬ (D F y =. the (f y))})
    (hInt : (total (fun x => f (g x) * g' x)).isIntegrableOn a b) :
    IntegralExpr (fun x => f (g x) * g' x) a b =. the (F (g b) - F (g a)) := by
  apply newtonLeibniz (F := F ∘ g) _ hInt
  intro x hx
  have hF : D F (g x) =. the (f (g x)) := by
    simpa only [Set.mem_setOf_eq, not_not] using
      Set.disjoint_left.mp himage (Set.mem_image_of_mem g hx)
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _ =? D F (g x) * D g x := DerivExpr.Comp
    _ = the (f (g x) * g' x) := by poly_rw [hF, hg x hx]

/-- Change of variables between two definite integrals. In addition to image
avoidance, the entire closed interval between the image endpoints must avoid
all derivative failures, and the original integrand must be integrable there.
Neither orientation requires an ordering hypothesis. -/
theorem substitution {f F g g' : ℝ → ℝ} {a b : ℝ}
    (h : ∫ f =. prim F)
    (hg : ∀ x ∈ Integral.interval a b, D g x =. the (g' x))
    (himage : Disjoint (g '' Integral.interval a b) {y | ¬ (D F y =. the (f y))})
    (hInt : (total (fun x => f (g x) * g' x)).isIntegrableOn a b)
    (havoid : Disjoint (Integral.interval (g a) (g b)) {y | ¬ (D F y =. the (f y))})
    (hOriginal : (total f).isIntegrableOn (g a) (g b)) :
    IntegralExpr (fun x => f (g x) * g' x) a b = IntegralExpr f (g a) (g b) := by
  exact (LimitValue.finite_iff.mp (substitutionValue h hg himage hInt)).trans
    (LimitValue.finite_iff.mp (IndefiniteExpr.toIntegralExpr h havoid hOriginal)).symm

end IntegralExpr
