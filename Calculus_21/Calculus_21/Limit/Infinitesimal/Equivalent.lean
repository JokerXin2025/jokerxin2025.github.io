/-
    «Calculus_21».Limit.Infinitesimal.Equivalent
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Infinitesimal.Defs
set_option linter.style.header false


/-! # Definitions of Equivalent Infinitesimal -/

/-- Equivalent Infinitesimal -/
abbrev EquivInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  (isInfinitesimal F x₀) ∧ (isInfinitesimal G x₀)
  ∧ FuncLimit (F / G) x₀ 1

/-- Equivalent Left Infinitesimal -/
abbrev EquivLeftInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  (isLeftInfinitesimal F x₀) ∧ (isLeftInfinitesimal G x₀)
  ∧ LeftLimit (F / G) x₀ 1

/-- Equivalent Right Infinitesimal -/
abbrev EquivRightInfinitesimal (F G : RFunction) (x₀ : ℝ) : Prop :=
  (isRightInfinitesimal F x₀) ∧ (isRightInfinitesimal G x₀)
  ∧ RightLimit (F / G) x₀ 1


/-! # Basic Equivalent Infinitesimals -/

/-- Square Root's Equivalent Infinitesimal (Expression) -/
lemma SqrtEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ (√(1 + f x) - 1) / (f x / 2)) x₀ = the 1
:= sorry

/-- Square Root's Equivalent Left Infinitesimal (Expression) -/
lemma SqrtLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ (√(1 + f x) - 1) / (f x / 2)) x₀ = the 1
:= sorry

/-- Square Root's Equivalent Right Infinitesimal (Expression) -/
lemma SqrtRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ (√(1 + f x) - 1) / (f x / 2)) x₀ = the 1
:= sorry

/-- Power's Equivalent Infinitesimal (Expression) -/
lemma PowerEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a ≠ 0)
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ ((1 + f x) ^ a - 1) / (a * f x)) x₀ = the 1
:= sorry

/-- Power's Equivalent Left Infinitesimal (Expression) -/
lemma PowerLeftEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a ≠ 0)
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ ((1 + f x) ^ a - 1) / (a * f x)) x₀ = the 1
:= sorry

/-- Power's Equivalent Right Infinitesimal (Expression) -/
lemma PowerRightEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a ≠ 0)
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ ((1 + f x) ^ a - 1) / (a * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Infinitesimal (ℤ) (Expression) -/
lemma NPowerEquiv_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Left Infinitesimal (ℤ) (Expression) -/
lemma NPowerLeftEquiv_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Right Infinitesimal (ℤ) (Expression) -/
lemma NPowerRightEquiv_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Infinitesimal (ℕ) (Expression) -/
lemma NPowerEquiv_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Left Infinitesimal (ℕ) (Expression) -/
lemma NPowerLeftEquiv_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Integral Power's Equivalent Right Infinitesimal (ℕ) (Expression) -/
lemma NPowerRightEquiv_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ : ℝ}
    (h_dom : n ≠ 0)
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ ((1 + f x) ^ n - 1) / (n * f x)) x₀ = the 1
:= sorry

/-- Natural Exponent's Equivalent Infinitesimal (Expression) -/
lemma ExpEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ (exp (f x) - 1) / f x) x₀ = the 1
:= sorry

/-- Natural Exponent's Equivalent Left Infinitesimal (Expression) -/
lemma ExpLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ (exp (f x) - 1) / f x) x₀ = the 1
:= sorry

/-- Natural Exponent's Equivalent Right Infinitesimal (Expression) -/
lemma ExpRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ (exp (f x) - 1) / f x) x₀ = the 1
:= sorry

/-- Exponent's Equivalent Infinitesimal (Expression) -/
lemma ExpowEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ (a ^ f x - 1) / (f x * ln a)) x₀ = the 1
:= sorry

/-- Exponent's Equivalent Left Infinitesimal (Expression) -/
lemma ExpowLeftEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ (a ^ f x - 1) / (f x * ln a)) x₀ = the 1
:= sorry

/-- Exponent's Equivalent Right Infinitesimal (Expression) -/
lemma ExpowRightEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ (a ^ f x - 1) / (f x * ln a)) x₀ = the 1
:= sorry

/-- Natural Logarithm's Equivalent Infinitesimal (Expression) -/
lemma LnEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ ln (1 + f x) / f x) x₀ = the 1
:= sorry

/-- Natural Logarithm's Equivalent Left Infinitesimal (Expression) -/
lemma LnLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ ln (1 + f x) / f x) x₀ = the 1
:= sorry

/-- Natural Logarithm's Equivalent Right Infinitesimal (Expression) -/
lemma LnRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ ln (1 + f x) / f x) x₀ = the 1
:= sorry

/-- Logarithm's Equivalent Infinitesimal (Expression) -/
lemma LogEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ log a (1 + f x) / (f x / ln a)) x₀ = the 1
:= sorry

/-- Logarithm's Equivalent Left Infinitesimal (Expression) -/
lemma LogLeftEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ log a (1 + f x) / (f x / ln a)) x₀ = the 1
:= sorry

/-- Logarithm's Equivalent Right Infinitesimal (Expression) -/
lemma LogRightEquiv {f : ℝ → ℝ} {a x₀ : ℝ}
    (h_dom : a > 0 ∧ a ≠ 1)
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ log a (1 + f x) / (f x / ln a)) x₀ = the 1
:= sorry

/-- Sine's Equivalent Infinitesimal (Expression) -/
lemma SinEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ sin (f x) / f x) x₀ = the 1
:= sorry

/-- Sine's Equivalent Left Infinitesimal (Expression) -/
lemma SinLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ sin (f x) / f x) x₀ = the 1
:= sorry

/-- Sine's Equivalent Right Infinitesimal (Expression) -/
lemma SinRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ sin (f x) / f x) x₀ = the 1
:= sorry

/-- Tangent's Equivalent Infinitesimal (Expression) -/
lemma TanEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ tan (f x) / f x) x₀ = the 1
:= sorry

/-- Tangent's Equivalent Left Infinitesimal (Expression) -/
lemma TanLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ tan (f x) / f x) x₀ = the 1
:= sorry

/-- Tangent's Equivalent Right Infinitesimal (Expression) -/
lemma TanRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ tan (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Sine's Equivalent Infinitesimal (Expression) -/
lemma ArcsinEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ arcsin (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Sine's Equivalent Left Infinitesimal (Expression) -/
lemma ArcsinLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ arcsin (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Sine's Equivalent Right Infinitesimal (Expression) -/
lemma ArcsinRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ arcsin (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Tangent's Equivalent Infinitesimal (Expression) -/
lemma ArctanEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (fun x ↦ arctan (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Tangent's Equivalent Left Infinitesimal (Expression) -/
lemma ArctanLeftEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₋ f x₀ = the 0)
  : lim₋ (fun x ↦ arctan (f x) / f x) x₀ = the 1
:= sorry

/-- Arc-Tangent's Equivalent Right Infinitesimal (Expression) -/
lemma ArctanRightEquiv {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim₊ f x₀ = the 0)
  : lim₊ (fun x ↦ arctan (f x) / f x) x₀ = the 1
:= sorry


/-! # Rules of Equivalent Infinitesimal Substitution -/

/-- Equivalent Substitution (Expression) -/
theorem EquivSubst {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim (f / f') x₀ = the 1)
  : lim (f * g) x₀ =? lim (f' * g) x₀
:= sorry

/-- Equivalent Substitution on Denominator (Expression) -/
theorem EquivSubst' {f g g' h : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim (g / g') x₀ = the 1)
  : lim (f / (g * h)) x₀ =? lim (f / (g' * h)) x₀
:= sorry

/-- Equivalent Substitution of Left Limit (Expression) -/
theorem LeftEquivSubst {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₋ (f / f') x₀ = the 1)
  : lim₋ (f * g) x₀ =? lim₋ (f' * g) x₀
:= sorry

/-- Equivalent Substitution of Left Limit on Denominator (Expression) -/
theorem LeftEquivSubst' {f g g' h : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₋ (g / g') x₀ = the 1)
  : lim₋ (f / (g * h)) x₀ =? lim₋ (f / (g' * h)) x₀
:= sorry

/-- Equivalent Substitution of Right Limit (Expression) -/
theorem RightEquivSubst {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₊ (f / f') x₀ = the 1)
  : lim₊ (f * g) x₀ =? lim₊ (f' * g) x₀
:= sorry

/-- Equivalent Substitution of Right Limit on Denominator (Expression) -/
theorem RightEquivSubst' {f g g' h : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₊ (g / g') x₀ = the 1)
  : lim₊ (f / (g * h)) x₀ =? lim₊ (f / (g' * h)) x₀
:= sorry

page_end
