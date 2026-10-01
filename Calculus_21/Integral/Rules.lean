import «Calculus_21».Integral.Expr.Init

set_option linter.style.header false

namespace DefIntegral

variable {F G : RFunction} {a b v w : ℝ}

theorem neg (h : DefIntegral F a b v) : DefIntegral (-F) a b (-v) := by
  have heq : (-1 : ℝ) • F = -F := by
    apply RFunction.ext
    · funext x
      exact neg_one_mul (F.map x)
    · rfl
  simpa only [heq, neg_one_mul] using h.smul (-1)

theorem sub (hF : DefIntegral F a b v) (hG : DefIntegral G a b w) :
    DefIntegral (F - G) a b (v - w) := by
  have h := hF.add hG.neg
  exact h.congr h.domain (fun x _ => (sub_eq_add_neg (F.map x) (G.map x)).symm)

theorem nonneg (hab : a ≤ b) (h : DefIntegral F a b v)
    (hf : ∀ x ∈ Integral.interval a b, 0 ≤ F.map x) : 0 ≤ v := by
  simpa only [zero_mul] using (DefIntegral.const 0 a b).mono hab h hf

end DefIntegral

namespace RFunction.isIntegrableOn

variable {F G : RFunction} {a b : ℝ}

theorem neg (h : F.isIntegrableOn a b) : (-F).isIntegrableOn a b := by
  obtain ⟨v, hv⟩ := h
  exact hv.neg.isIntegrableOn

theorem sub (hF : F.isIntegrableOn a b) (hG : G.isIntegrableOn a b) :
    (F - G).isIntegrableOn a b := by
  obtain ⟨v, hv⟩ := hF
  obtain ⟨w, hw⟩ := hG
  exact (hv.sub hw).isIntegrableOn

end RFunction.isIntegrableOn

namespace IntegralExpr

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem neg_eq : IntegralExpr (-f) a b = -IntegralExpr f a b := by
  classical
  by_cases h : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := h
    simp only [finite_iff.mpr hv, LimitValue.finite_neg]
    exact finite_iff.mpr hv.neg.total
  · have hn : ¬ (total (-f)).isIntegrableOn a b := by
      rintro ⟨v, hv⟩
      exact h (hv.neg.congr (G := total f) (fun _ _ => trivial)
        (fun x _ => neg_neg (f x))).isIntegrableOn
    simp only [unknown_iff.mpr h, unknown_iff.mpr hn]
    rfl

theorem sub_of_add : IntegralExpr (f - g) a b =.
    IntegralExpr f a b - IntegralExpr g a b := by
  change IntegralExpr (f - g) a b =. IntegralExpr f a b + -IntegralExpr g a b
  rw [sub_eq_add_neg, ← neg_eq]
  exact Add

end IntegralExpr
