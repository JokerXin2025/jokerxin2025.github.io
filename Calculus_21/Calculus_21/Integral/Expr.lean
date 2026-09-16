/-
    «Calculus_21».Integral.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Integral.Defs
import «Calculus_21».Ind_Integral.Expr
set_option linter.style.header false


/-! # Definite Integral Expression -/

noncomputable section

open Classical in
/-- Definite Integral Expression: `∫_[a,b] f` returns the value of the
     definite integral if `f` is Riemann integrable, or an `IntegralError` otherwise. -/
def DefIntegralExpr (f : ℝ → ℝ) (a b : ℝ) : Except IntegralError ℝ :=
  if h : isRiemannIntegrable f a b then the (choose h)
  else .error .nonIntegrable

end

/-- Notation: `∫_[a,b] f` for definite integral expression -/
notation "∫_[" a ", " b "] " f:max => DefIntegralExpr f a b

/-! # Bridges between Definite Integral Relation & Expression -/

open Classical in
/-- Relation → Expression: if `HasDefIntegral f a b I`, then `∫_[a,b] f = the I` -/
theorem HasDefIntegral.to_expr {f : ℝ → ℝ} {a b I : ℝ}
    (h : HasDefIntegral f a b I)
  : ∫_[a,b] f = the I
:= by sorry

open Classical in
/-- Expression → Relation -/
theorem DefIntegralExpr.to_has {f : ℝ → ℝ} {a b I : ℝ}
    (h : ∫_[a,b] f = the I)
  : HasDefIntegral f a b I
:= by sorry


/-! # Newton-Leibniz in Expression Form -/

open Classical in
/-- Newton-Leibniz Formula (Expression Form):
    `∫_[a,b] f = the (F b - F a)` whenever `F` is an antiderivative of `f`. -/
theorem DefIntegralExpr.newton_leibniz {f F : ℝ → ℝ} {a b : ℝ}
    (h_anti : HasAntiderivRaw f F)
  : ∫_[a,b] f = the (F b - F a)
:= by sorry


/-! # Conversion: Definite Integral ↔ Indefinite Integral -/

open Classical in
/--
  **Core conversion lemma**: To compute a definite integral, find an antiderivative.

  If `∫ f = the ⟦F⟧` (i.e. `F` is an antiderivative of `f`, up to a constant),
  then `∫_[a,b] f = the (F b - F a)`.

  This enables the natural workflow:
  1. Compute the indefinite integral: `∫ f = the ⟦F⟧`
  2. Convert to definite integral: `∫_[a,b] f = the (F b - F a)`
-/
theorem integral_via_indef {f F : ℝ → ℝ} {a b : ℝ}
    (h_indef : ∫ f = the ⟦F⟧)
  : ∫_[a,b] f = the (F b - F a)
:= by sorry

open Classical in
/--
  Variant with explicit `HasAntiderivRaw` hypothesis:
  if `F' = f`, then `∫_[a,b] f = the (F b - F a)`.
-/
theorem integral_of_antideriv {f F : ℝ → ℝ} {a b : ℝ}
    (h_anti : HasAntiderivRaw f F)
  : ∫_[a,b] f = the (F b - F a)
:= DefIntegralExpr.newton_leibniz h_anti

/--
  If two antiderivatives differ by a constant, their evaluations
  `F(b) - F(a)` and `G(b) - G(a)` are equal.
  (Useful when the indefinite integral gives a class `⟦F⟧` but we
   want to evaluate a different representative `G`.)
-/
lemma antideriv_eval_invariant {f F G : ℝ → ℝ} {a b : ℝ}
    (h_anti_F : HasAntiderivRaw f F) (h_anti_G : HasAntiderivRaw f G)
  : F b - F a = G b - G a := by
  have h_diff := HasAntiderivRaw.differ_by_const h_anti_F h_anti_G
  rcases h_diff with ⟨S, hC⟩
  -- hC: ∀ x ∉ S, D (F - G) x = the 0
  sorry

open Classical in
/--
  **Tactic-friendly conversion**: to prove `∫_[a,b] f = the V`,
  it suffices to exhibit an antiderivative `F` of `f` and show `F(b) - F(a) = V`.
-/
theorem integral_eq_of_antideriv {f F : ℝ → ℝ} {a b V : ℝ}
    (h_anti : HasAntiderivRaw f F) (h_val : F b - F a = V)
  : ∫_[a,b] f = the V := by
  calc
    ∫_[a,b] f = the (F b - F a) := integral_of_antideriv h_anti
    _ = the V := by rw [h_val]
