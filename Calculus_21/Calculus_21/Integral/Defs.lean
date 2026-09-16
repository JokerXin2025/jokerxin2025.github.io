/-
    «Calculus_21».Integral.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Ind_Integral.Expr
set_option linter.style.header false


/-! # Definite Integral (Riemann Integral) -/

/-- The definite (Riemann) integral of `f` from `a` to `b` equals `I`.
    This is currently an axiom (temporary); a constructive definition
    via Riemann sums will be provided later. -/
axiom HasDefIntegral (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) : Prop

/-- `f` is Riemann integrable on the interval with endpoints `a` and `b` -/
abbrev isRiemannIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ I : ℝ, HasDefIntegral f a b I

/-! # Basic Properties of Definite Integral -/

/-- Uniqueness of the definite integral -/
axiom HasDefIntegral.unique {f : ℝ → ℝ} {a b I₁ I₂ : ℝ}
    (h₁ : HasDefIntegral f a b I₁) (h₂ : HasDefIntegral f a b I₂)
  : I₁ = I₂

/-- Linearity w.r.t. scalar multiplication: `∫_a^b (k·f) = k · ∫_a^b f` -/
axiom HasDefIntegral.smul {f : ℝ → ℝ} {a b k I : ℝ}
    (h : HasDefIntegral f a b I)
  : HasDefIntegral (k • f) a b (k * I)

/-- Linearity w.r.t. addition: `∫_a^b (f + g) = ∫_a^b f + ∫_a^b g` -/
axiom HasDefIntegral.add {f g : ℝ → ℝ} {a b I J : ℝ}
    (hf : HasDefIntegral f a b I) (hg : HasDefIntegral g a b J)
  : HasDefIntegral (f + g) a b (I + J)

/-- Negation: `∫_a^b (-f) = -∫_a^b f` -/
axiom HasDefIntegral.neg {f : ℝ → ℝ} {a b I : ℝ}
    (h : HasDefIntegral f a b I)
  : HasDefIntegral (-f) a b (-I)

/-- Subtraction: `∫_a^b (f - g) = ∫_a^b f - ∫_a^b g` -/
axiom HasDefIntegral.sub {f g : ℝ → ℝ} {a b I J : ℝ}
    (hf : HasDefIntegral f a b I) (hg : HasDefIntegral g a b J)
  : HasDefIntegral (f - g) a b (I - J)

/-- Interval additivity: `∫_a^b f + ∫_b^c f = ∫_a^c f` -/
axiom HasDefIntegral.interval_add {f : ℝ → ℝ} {a b c I J : ℝ}
    (hab : HasDefIntegral f a b I) (hbc : HasDefIntegral f b c J)
  : HasDefIntegral f a c (I + J)

/-- Reversal of integration bounds: `∫_a^b f = -∫_b^a f` -/
axiom HasDefIntegral.rev {f : ℝ → ℝ} {a b I : ℝ}
    (h : HasDefIntegral f a b I)
  : HasDefIntegral f b a (-I)

/-- Integral over a zero-length interval is zero -/
axiom HasDefIntegral.same_point {f : ℝ → ℝ} {a : ℝ}
  : HasDefIntegral f a a 0

/-- Monotonicity: if f ≤ g on the interval, then ∫ f ≤ ∫ g -/
axiom HasDefIntegral.mono {f g : ℝ → ℝ} {a b I J : ℝ}
    (hf : HasDefIntegral f a b I) (hg : HasDefIntegral g a b J)
    (hle : ∀ x, min a b ≤ x ∧ x ≤ max a b → f x ≤ g x)
  : I ≤ J


/-! # Fundamental Theorem of Calculus -/

/-- **Newton-Leibniz Formula** (FTC Part 2 / Evaluation Theorem):
    If `F` is an antiderivative of `f` (i.e. `F' = f` everywhere),
    then the definite integral of `f` from `a` to `b` equals `F(b) - F(a)`.

    This is the core bridge between definite and indefinite integrals:
    to compute `∫_a^b f`, find an antiderivative `F` and evaluate `F(b) - F(a)`. -/
axiom HasDefIntegral.newton_leibniz {f F : ℝ → ℝ} (a b : ℝ)
    (h_anti : HasAntiderivRaw f F)
  : HasDefIntegral f a b (F b - F a)

/-- **FTC Part 1** (Differentiation of the Integral):
    If `G(x) := ∫_a^x f(t) dt`, then `G` is an antiderivative of `f`,
    i.e. `G'(x) = f(x)` for all `x`. -/
axiom HasDefIntegral.ftc_part1 {f G : ℝ → ℝ} (a : ℝ)
    (h_G : ∀ x, HasDefIntegral f a x (G x))
  : HasAntiderivRaw f G

/-! # Conversion Lemmas: Definite → Indefinite -/

/-- Compute a definite integral via an antiderivative:
    `∫_a^b f = I` whenever `F' = f` and `F(b) - F(a) = I`. -/
theorem HasDefIntegral.eq_of_antideriv {f F : ℝ → ℝ} (a b : ℝ) {I : ℝ}
    (h_anti : HasAntiderivRaw f F) (h_val : F b - F a = I)
  : HasDefIntegral f a b I := by
  have h := HasDefIntegral.newton_leibniz a b h_anti
  rw [h_val] at h
  exact h

/-- From an indefinite integral result, directly obtain the definite integral:
    Given `∫ f = the ⟦F⟧` and `HasAntiderivRaw f F`, we have `∫_a^b f = F(b) - F(a)`.
    This is the primary workflow: find an antiderivative → evaluate at bounds. -/
theorem HasDefIntegral.of_antideriv_eval {f F : ℝ → ℝ} (a b : ℝ)
    (h_anti : HasAntiderivRaw f F)
  : HasDefIntegral f a b (F b - F a) :=
  HasDefIntegral.newton_leibniz a b h_anti

/-- Variant: if we know the definite integral of `f` from `a` to `b` equals `I`,
    then for any antiderivative `F`, we must have `F(b) - F(a) = I`. -/
theorem HasDefIntegral.antideriv_eval_eq {f F : ℝ → ℝ} (a b : ℝ) {I : ℝ}
    (h_int : HasDefIntegral f a b I) (h_anti : HasAntiderivRaw f F)
  : F b - F a = I := by
  have h_nl := HasDefIntegral.newton_leibniz a b h_anti
  exact HasDefIntegral.unique h_nl h_int
