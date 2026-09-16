/-
    «Calculus_21».Ind_Integral.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Ind_Integral.Expr
set_option linter.style.header false


/-! # Indefinite Integral Calculation Rules -/

/-!
The rules for __Multiplicative Scalar Power__ are not provided here, which can be
regarded as a composite function by the following conclusion:
```lean
example {f : ℝ → ℝ} {n : ℕ} : f ^ n = npow n ∘ f := rfl
```
-/

/-! ## Linearity -/

/-- Integral of Scalar Multiplication (Expression) -/
theorem IndefIntegralExpr.SMul {f : ℝ → ℝ} {k : ℝ}
  : ∫ (k • f) =?
      (Except.ok k : Except IntegralError ℝ) * ∫ f
:= by sorry

/-- Integral of Additive Inverse (Expression) -/
theorem IndefIntegralExpr.Neg {f : ℝ → ℝ}
  : ∫ (-f) =? - ∫ f
:= by sorry

/-- Integral Addition (Expression) -/
theorem IndefIntegralExpr.Add {f g : ℝ → ℝ}
  : ∫ (f + g) =? ∫ f + ∫ g
:= by sorry

/-- Integral Subtraction (Expression) -/
theorem IndefIntegralExpr.Sub {f g : ℝ → ℝ}
  : ∫ (f - g) =? ∫ f - ∫ g
:= by sorry

/-! ## Substitution Rule (Reverse Chain Rule) -/

/-- Substitution Rule: if F' = f and g' = Dg, then (F ∘ g)' = (f ∘ g) · g' -/
theorem HasAntiderivRaw.chain {f F g g' : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F) (h_g : HasAntiderivRaw g' g)
  : HasAntiderivRaw ((f ∘ g) * g') (F ∘ g)
:= by sorry

/-- Substitution Rule (Expression) -/
theorem IndefIntegralExpr.Chain {f g : ℝ → ℝ}
  : ∫ (f ∘ g * (fun x ↦ (D g x).getD 0)) =? ∫ f
:= by sorry

/-! ## Integration by Parts -/

/-- Integration by Parts:
    If f' = Df and g' = Dg, then ∫ f·g' = f·g - ∫ f'·g -/
theorem HasAntiderivRaw.by_parts {f f' g g' H : ℝ → ℝ}
    (h_f' : HasAntiderivRaw f' f) (h_g' : HasAntiderivRaw g' g)
    (h_H : HasAntiderivRaw (f * g') H)
  : HasAntiderivRaw (f' * g) (f * g - H)
:= by sorry

/-- Integration by Parts (Expression) -/
theorem IndefIntegralExpr.ByParts {f g : ℝ → ℝ}
  : ∫ (f * (fun x ↦ (D g x).getD 0))
    =? the (⟦f * g⟧ : PrimFunc) - ∫ ((fun x ↦ (D f x).getD 0) * g)
:= by sorry

page_end
