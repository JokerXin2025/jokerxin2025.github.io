/-
    «Calculus_21».Limit.Expr.GCongr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false

open PolyCalc LimitValue
variable {A A' B B' : LimitValue}


@[gcongr]
private theorem add_congr
  : A =. A' → B =. B' → A + B =. A' + B'
:= by
  intro h₁ h₂
  rw [polyEq_iff_lessPreciseThan] at h₁ h₂ ⊢
  cases A <;> cases A' <;> cases B <;> cases B'
  <;> simp_all only [LessPreciseThan]

@[gcongr]
private theorem add_congr_eq
  : A = A' → B = B' → A + B = A' + B'
:= by grind

@[gcongr]
private theorem neg_congr
  : A =. A' → -A =. -A'
:= by
  intro h
  rw [polyEq_iff_lessPreciseThan] at h ⊢
  cases A <;> cases A'
  <;> simp_all only [LessPreciseThan]

@[gcongr]
private theorem neg_congr_eq
  : A = A' → -A = -A'
:= by grind

@[gcongr]
private theorem sub_congr
  : A =. A' → B =. B' → A - B =. A' - B'
:= (add_congr · <| neg_congr ·)

@[gcongr]
private theorem sub_congr_eq
  : A = A' → B = B' → A - B = A' - B'
:= by grind

@[gcongr]
private theorem mul_congr
  : A =. A' → B =. B' → A * B =. A' * B'
:= by
  intro h₁ h₂
  rw [polyEq_iff_lessPreciseThan] at h₁ h₂ ⊢
  cases A <;> cases A' <;> cases B <;> cases B'
  <;> simp only [LessPreciseThan] at h₁ h₂ ⊢
  <;> simp only [HMul.hMul, Mul.mul] at ⊢
  <;> grind

@[gcongr]
private theorem mul_congr_eq
  : A = A' → B = B' → A * B = A' * B'
:= by grind

@[gcongr]
private theorem inv_congr
  : A =. A' → A⁻¹ =. A'⁻¹
:= by
  intro h
  rw [polyEq_iff_lessPreciseThan] at h ⊢
  cases A <;> cases A'
  <;> simp only [LessPreciseThan, Inv.inv] at h ⊢
  <;> grind

@[gcongr]
private theorem inv_congr_eq
  : A = A' → A⁻¹ = A'⁻¹
:= by grind

@[gcongr]
private theorem div_congr
  : A =. A' → B =. B' → A / B =. A' / B'
:= (mul_congr · <| inv_congr ·)

@[gcongr]
private theorem div_congr_eq
  : A = A' → B = B' → A / B = A' / B'
:= by grind

@[gcongr]
private theorem pow_congr
  : A =. A' → B =. B' → A ^ B =. A' ^ B'
:= by
  intro h₁ h₂
  rw [polyEq_iff_lessPreciseThan] at h₁ h₂ ⊢
  cases A <;> cases A' <;> cases B <;> cases B'
  <;> simp only [LessPreciseThan] at h₁ h₂ ⊢
  <;> simp only [HPow.hPow, Pow.pow]
  <;> grind

@[gcongr]
private theorem pow_congr_eq
  : A = A' → B = B' → A ^ B = A' ^ B'
:= by grind
