/-
    «Calculus_21».Limit.Expr.GCongr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)

open LimitValue

private lemma add_fallback_left {A B : LimitValue}
    (h : LimitFallbackCore A B) (C : LimitValue) : A + C =. B + C := by
  cases h with
  | finite_unknown _ => cases C <;> apply unknown_always
  | divergence_unknown => cases C <;> apply unknown_always
  | infty_divergence =>
      cases C with
      | finite _ => poly_fallback
      | _ => rfl
  | pos_infty_infty =>
      cases C with
      | finite _ => poly_fallback
      | _ => apply unknown_always
  | neg_infty_infty =>
      cases C with
      | finite _ => poly_fallback
      | negInfty => exact unknown_always _
      | _ => rfl

private lemma add_fallback_right {A B : LimitValue}
    (C : LimitValue) (h : LimitFallbackCore A B) : C + A =. C + B := by
  cases h with
  | finite_unknown _ => cases C <;> apply unknown_always
  | divergence_unknown => cases C <;> apply unknown_always
  | infty_divergence =>
      cases C with
      | finite _ => poly_fallback
      | _ => rfl
  | pos_infty_infty =>
      cases C with
      | finite _ => poly_fallback
      | _ => apply unknown_always
  | neg_infty_infty =>
      cases C with
      | finite _ => poly_fallback
      | negInfty => exact unknown_always _
      | _ => rfl

private lemma add_congr_left {A A' : LimitValue} (h : A =. A') (B : LimitValue) :
    A + B =. A' + B :=
  PolyEqual.map (· + B) (fun h => add_fallback_left h B) h

private lemma add_congr_right (A : LimitValue) {B B' : LimitValue} (h : B =. B') :
    A + B =. A + B' :=
  PolyEqual.map (A + ·) (add_fallback_right A) h

@[gcongr]
theorem add_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A + B =. A' + B' :=
  PolyEqual_trans (add_congr_left hA B) (add_congr_right A' hB)

private lemma neg_fallback {A B : LimitValue}
    (h : LimitFallbackCore A B) : -A =. -B := by
  cases h <;> poly_fallback

@[gcongr]
theorem neg_congr {A B : LimitValue} (h : A =. B) : -A =. -B :=
  PolyEqual.map (-·) neg_fallback h

@[gcongr]
theorem sub_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A - B =. A' - B' :=
  add_congr hA (neg_congr hB)

private lemma mul_fallback_left {A B : LimitValue}
    (h : LimitFallbackCore A B) (C : LimitValue) : A * C =. B * C := by
  cases h <;> cases C <;> simp only [HMul.hMul, Mul.mul]
  all_goals
    repeat' split
    all_goals first
      | apply unknown_always
      | grind
      | poly_fallback

private lemma mul_comm_ (A B : LimitValue) : A * B = B * A := by
  cases A <;> cases B <;> simp only [HMul.hMul, Mul.mul]
  case finite.finite a b => exact congrArg LimitValue.finite (_root_.mul_comm a b)

private lemma mul_fallback_right (C : LimitValue) {A B : LimitValue}
    (h : LimitFallbackCore A B) : C * A =. C * B := by
  rw [mul_comm_ C A, mul_comm_ C B]
  exact mul_fallback_left h C

private lemma mul_congr_left {A A' : LimitValue} (h : A =. A') (B : LimitValue) :
    A * B =. A' * B :=
  PolyEqual.map (· * B) (fun h => mul_fallback_left h B) h

private lemma mul_congr_right (A : LimitValue) {B B' : LimitValue} (h : B =. B') :
    A * B =. A * B' :=
  PolyEqual.map (A * ·) (mul_fallback_right A) h

@[gcongr]
theorem mul_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A * B =. A' * B' :=
  PolyEqual_trans (mul_congr_left hA B) (mul_congr_right A' hB)

private lemma inv_fallback {A B : LimitValue}
    (h : LimitFallbackCore A B) : A⁻¹ =. B⁻¹ := by
  cases h with
  | finite_unknown a =>
      change (if a ≠ 0 then the a⁻¹ else infty) =. unknown
      split <;> apply unknown_always
  | divergence_unknown => rfl
  | infty_divergence => poly_fallback
  | pos_infty_infty => rfl
  | neg_infty_infty => rfl

@[gcongr]
theorem inv_congr {A B : LimitValue} (h : A =. B) : A⁻¹ =. B⁻¹ :=
  PolyEqual.map (·⁻¹) inv_fallback h

@[gcongr]
theorem div_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A / B =. A' / B' :=
  mul_congr hA (inv_congr hB)
