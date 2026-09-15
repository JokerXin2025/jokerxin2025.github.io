/-
    «Calculus_21».Limit.Tactics.Cont
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr
import «Calculus_21».Limit.Expr.BasicRules
import «Calculus_21».Limit.Tactics.Congr
set_option linter.style.header false

open LimitValue (finite_iff finite_div)
local macro "~" op:term : term => `(finite_iff.mp <| $op)


/-! # Preparations -/

class AutoLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim f x₀ =. the val

class AutoLeftLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₋ f x₀ =. the val

class AutoRightLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₊ f x₀ =. the val

open FuncLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c c₁ c₂ : Prop}

private instance funclimit_patch₁
  : AutoLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim (k + ·) x₀
         =. lim (const k) x₀ + lim id x₀
            := Add
      _  =. the k + the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k + x₀)
            := by rfl

private instance funclimit_patch₁'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance funclimit_patch₂
  : AutoLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim (k - ·) x₀
         =. lim (const k) x₀ - lim id x₀
            := Sub
      _  =. the k - the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k - x₀)
            := by rfl

private instance funclimit_patch₂'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance funclimit_patch₃
  : AutoLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim (k * ·) x₀
         =. lim (const k) x₀ * lim id x₀
            := Mul
      _  =. the k * the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k * x₀)
            := by rfl

private instance funclimit_patch₃'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance funclimit_patch₄
  : AutoLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (k / ·) x₀
         =. lim (const k) x₀ / lim id x₀
            := Div
      _  =. the k / the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k / x₀)
             := finite_div h_x₀_ne0

private instance funclimit_patch₄'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance funclimit_patch₅
  : AutoLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim (-·) x₀
         =. - lim id x₀
            := Neg
      _  =. - the x₀
            := by rw [~ Identity]
      _  =. the (-x₀)
            := by rfl

private instance funclimit_patch₅'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance funclimit_patch₆
  : AutoLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim (·⁻¹) x₀
         =. (lim id x₀)⁻¹
            := Inv
      _  =. (the x₀)⁻¹
            := by rw [~ Identity]
      _  =. the x₀⁻¹
             := by
               change (if x₀ ≠ 0 then the x₀⁻¹ else infty) =. the x₀⁻¹
               rw [if_pos h_x₀_ne0]

private instance funclimit_patch₆'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance funclimit_Constant
  : AutoLimit (const C) x₀ C True where
  eq := directly Constant

private instance funclimit_Constant'
  : AutoLimit (fun _ ↦ C) x₀ C True where
  eq := funclimit_Constant.eq

private instance funclimit_Identity
  : AutoLimit id x₀ x₀ True where
  eq := directly Identity

private instance funclimit_Identity'
  : AutoLimit (·) x₀ x₀ True where
  eq := funclimit_Identity.eq

private instance funclimit_Neg
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim (-f) x₀
         =. - lim f x₀
            := Neg
      _  =. - the L₁
            := by rw [~ AutoLimit.eq h_cond]
      _  =. the (-L₁)
            := by rfl

private instance funclimit_Neg'
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := funclimit_Neg.eq

private instance funclimit_SMul
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim (k • f) x₀
         =. the k * lim f x₀
            := SMul
      _  =. the k * the L₁
            := by rw [~ AutoLimit.eq h_cond]
      _  =. the (k * L₁)
            := by rfl

private instance funclimit_Inv
    [AutoLimit f x₀ L₁ c]
  : AutoLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim f⁻¹ x₀
         =. (lim f x₀)⁻¹
            := Inv
      _  =. (the L₁)⁻¹
            := by rw [~ AutoLimit.eq h_cond]
      _  =. the L₁⁻¹
             := by
               change (if L₁ ≠ 0 then the L₁⁻¹ else infty) =. the L₁⁻¹
               rw [if_pos h_L_ne0]

private instance funclimit_Inv'
    [AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := funclimit_Inv.eq

private instance funclimit_Add
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f + g) x₀
         =. lim f x₀ + lim g x₀
            := Add
      _  =. the L₁ + the L₂
            := by rw [~ AutoLimit.eq h₁, ~ AutoLimit.eq h₂]
      _  =. the (L₁ + L₂)
            := by rfl

private instance funclimit_Add'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := funclimit_Add.eq

private instance funclimit_Sub
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f - g) x₀
         =. lim f x₀ - lim g x₀
            := Sub
      _  =. the L₁ - the L₂
            := by rw [~ AutoLimit.eq h₁, ~ AutoLimit.eq h₂]
      _  =. the (L₁ - L₂)
            := by rfl

private instance funclimit_Sub'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := funclimit_Sub.eq

private instance funclimit_Mul
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim (f * g) x₀
         =. lim f x₀ * lim g x₀
            := Mul
      _  =. the L₁ * the L₂
            := by rw [~ AutoLimit.eq h₁, ~ AutoLimit.eq h₂]
      _  =. the (L₁ * L₂)
            := by rfl

private instance funclimit_Mul'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := funclimit_Mul.eq

private instance funclimit_Div
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim (f / g) x₀
         =. lim f x₀ / lim g x₀
            := Div
      _  =. the L₁ / the L₂
            := by rw [~ AutoLimit.eq h₁, ~ AutoLimit.eq h₂]
      _  =. the (L₁ / L₂)
             := finite_div h_L₂_ne0

private instance funclimit_Div'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := funclimit_Div.eq

private instance funclimit_Abs
  : AutoLimit abs x₀ |x₀| True where
  eq := directly Abs

private instance funclimit_Sqrt
  : AutoLimit sqrt x₀ √x₀ (x₀ > 0) where
  eq := Sqrt

private instance funclimit_Power
  : AutoLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  eq := Power

private instance funclimit_Power_ℤ {n : ℤ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0) where
  eq := Power_ℤ

private instance funclimit_Power_ℕ {n : ℕ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply Power_ℤ
    exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance funclimit_Exp
  : AutoLimit exp x₀ (exp x₀) True where
  eq := directly Exp

private instance funclimit_Expow
  : AutoLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := Expow

private instance funclimit_Ln
  : AutoLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := Ln

private instance funclimit_Log
  : AutoLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := Log

private instance funclimit_Sin
  : AutoLimit sin x₀ (sin x₀) True where
  eq := directly Sin

private instance funclimit_Cos
  : AutoLimit cos x₀ (cos x₀) True where
  eq := directly Cos

private instance funclimit_Tan
  : AutoLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := Tan

private instance funclimit_Cot
  : AutoLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := Cot

private instance funclimit_Sec
  : AutoLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := Sec

private instance funclimit_Csc
  : AutoLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := Csc

private instance funclimit_Sinh
  : AutoLimit sinh x₀ (sinh x₀) True where
  eq := directly Sinh

private instance funclimit_Cosh
  : AutoLimit cosh x₀ (cosh x₀) True where
  eq := directly Cosh

private instance funclimit_Tanh
  : AutoLimit tanh x₀ (tanh x₀) True where
  eq := directly Tanh

private instance funclimit_Coth
  : AutoLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := Coth

private instance funclimit_Sech
  : AutoLimit sech x₀ (sech x₀) True where
  eq := directly Sech

private instance funclimit_Csch
  : AutoLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := Csch

private instance funclimit_Arcsin
  : AutoLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := Arcsin

private instance funclimit_Arccos
  : AutoLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ < 1) where
  eq := Arccos

private instance funclimit_Arctan
  : AutoLimit arctan x₀ (arctan x₀) True where
  eq := directly Arctan

private instance funclimit_Arccot
  : AutoLimit arccot x₀ (arccot x₀) True where
  eq := directly Arccot

private instance funclimit_Arcsec
  : AutoLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := Arcsec

private instance funclimit_Arccsc
  : AutoLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ > 1) where
  eq := Arccsc

private instance funclimit_compAbs
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Abs

private instance funclimit_compAbs'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := funclimit_compAbs.eq

private instance funclimit_compSqrt
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Sqrt h_dom

private instance funclimit_compSqrt'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := funclimit_compSqrt.eq

private instance funclimit_compPower
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Power h_dom

private instance funclimit_compPower'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance funclimit_compPower''
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := funclimit_compPower.eq

private instance funclimit_compPower_ℤ {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Power_ℤ h_dom

private instance funclimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance funclimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℤ.eq

private instance funclimit_compPower_ℕ {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · apply Power_ℤ
      exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance funclimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance funclimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := funclimit_compPower_ℕ.eq

private instance funclimit_compExp
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Exp

private instance funclimit_compExp'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := funclimit_compExp.eq

private instance funclimit_compExpow
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Expow h_dom

private instance funclimit_compExpow'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := funclimit_compExpow.eq

private instance funclimit_compLn
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Ln h_dom

private instance funclimit_compLn'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := funclimit_compLn.eq

private instance funclimit_compLog
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Log h_dom

private instance funclimit_compLog'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := funclimit_compLog.eq

private instance funclimit_compSin
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Sin

private instance funclimit_compSin'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := funclimit_compSin.eq

private instance funclimit_compCos
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Cos

private instance funclimit_compCos'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := funclimit_compCos.eq

private instance funclimit_compTan
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Tan h_dom

private instance funclimit_compTan'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compTan.eq

private instance funclimit_compCot
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Cot h_dom

private instance funclimit_compCot'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCot.eq

private instance funclimit_compSec
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Sec h_dom

private instance funclimit_compSec'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := funclimit_compSec.eq

private instance funclimit_compCsc
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Csc h_dom

private instance funclimit_compCsc'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := funclimit_compCsc.eq

private instance funclimit_compSinh
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Sinh

private instance funclimit_compSinh'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := funclimit_compSinh.eq

private instance funclimit_compCosh
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Cosh

private instance funclimit_compCosh'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := funclimit_compCosh.eq

private instance funclimit_compTanh
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Tanh

private instance funclimit_compTanh'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := funclimit_compTanh.eq

private instance funclimit_compCoth
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Coth h_dom

private instance funclimit_compCoth'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCoth.eq

private instance funclimit_compSech
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Sech

private instance funclimit_compSech'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := funclimit_compSech.eq

private instance funclimit_compCsch
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Csch h_dom

private instance funclimit_compCsch'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := funclimit_compCsch.eq

private instance funclimit_compArcsin
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arcsin h_dom

private instance funclimit_compArcsin'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArcsin.eq

private instance funclimit_compArccos
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arccos h_dom

private instance funclimit_compArccos'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := funclimit_compArccos.eq

private instance funclimit_compArctan
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arctan

private instance funclimit_compArctan'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := funclimit_compArctan.eq

private instance funclimit_compArccot
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arccot

private instance funclimit_compArccot'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := funclimit_compArccot.eq

private instance funclimit_compArcsec
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arcsec h_dom

private instance funclimit_compArcsec'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArcsec.eq

private instance funclimit_compArccsc
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact Arccsc h_dom

private instance funclimit_compArccsc'
    [h_f : AutoLimit f x₀ L₁ c]
  : AutoLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := funclimit_compArccsc.eq

end

open LeftLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c c₁ c₂ : Prop}

private instance leftlimit_patch₁
  : AutoLeftLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim₋ (k + ·) x₀
         =. lim₋ (const k) x₀ + lim₋ id x₀
            := Add
      _  =. the k + the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k + x₀)
            := by rfl

private instance leftlimit_patch₁'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance leftlimit_patch₂
  : AutoLeftLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim₋ (k - ·) x₀
         =. lim₋ (const k) x₀ - lim₋ id x₀
            := Sub
      _  =. the k - the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k - x₀)
            := by rfl

private instance leftlimit_patch₂'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance leftlimit_patch₃
  : AutoLeftLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim₋ (k * ·) x₀
         =. lim₋ (const k) x₀ * lim₋ id x₀
            := Mul
      _  =. the k * the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k * x₀)
            := by rfl

private instance leftlimit_patch₃'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance leftlimit_patch₄
  : AutoLeftLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₋ (k / ·) x₀
         =. lim₋ (const k) x₀ / lim₋ id x₀
            := Div
      _  =. the k / the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k / x₀)
             := finite_div h_x₀_ne0

private instance leftlimit_patch₄'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance leftlimit_patch₅
  : AutoLeftLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim₋ (-·) x₀
         =. - lim₋ id x₀
            := Neg
      _  =. - the x₀
            := by rw [~ Identity]
      _  =. the (-x₀)
            := by rfl

private instance leftlimit_patch₅'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance leftlimit_patch₆
  : AutoLeftLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₋ (·⁻¹) x₀
         =. (lim₋ id x₀)⁻¹
            := Inv
      _  =. (the x₀)⁻¹
            := by rw [~ Identity]
      _  =. the x₀⁻¹
             := by
               change (if x₀ ≠ 0 then the x₀⁻¹ else infty) =. the x₀⁻¹
               rw [if_pos h_x₀_ne0]

private instance leftlimit_patch₆'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance leftlimit_Constant
  : AutoLeftLimit (const C) x₀ C True where
  eq := directly Constant

private instance leftlimit_Constant'
  : AutoLeftLimit (fun _ ↦ C) x₀ C True where
  eq := leftlimit_Constant.eq

private instance leftlimit_Identity
  : AutoLeftLimit id x₀ x₀ True where
  eq := directly Identity

private instance leftlimit_Identity'
  : AutoLeftLimit (·) x₀ x₀ True where
  eq := leftlimit_Identity.eq

private instance leftlimit_Neg
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim₋ (-f) x₀
         =. - lim₋ f x₀
            := Neg
      _  =. - the L₁
            := by rw [~ AutoLeftLimit.eq h_cond]
      _  =. the (-L₁)
            := by rfl

private instance leftlimit_Neg'
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := leftlimit_Neg.eq

private instance leftlimit_SMul
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim₋ (k • f) x₀
         =. the k * lim₋ f x₀
            := SMul
      _  =. the k * the L₁
            := by rw [~ AutoLeftLimit.eq h_cond]
      _  =. the (k * L₁)
            := by rfl

private instance leftlimit_Inv
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim₋ f⁻¹ x₀
         =. (lim₋ f x₀)⁻¹
            := Inv
      _  =. (the L₁)⁻¹
            := by rw [~ AutoLeftLimit.eq h_cond]
      _  =. the L₁⁻¹
             := by
               change (if L₁ ≠ 0 then the L₁⁻¹ else infty) =. the L₁⁻¹
               rw [if_pos h_L_ne0]

private instance leftlimit_Inv'
    [AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := leftlimit_Inv.eq

private instance leftlimit_Add
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f + g) x₀
         =. lim₋ f x₀ + lim₋ g x₀
            := Add
      _  =. the L₁ + the L₂
            := by rw [~ AutoLeftLimit.eq h₁, ~ AutoLeftLimit.eq h₂]
      _  =. the (L₁ + L₂)
            := by rfl

private instance leftlimit_Add'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Add.eq

private instance leftlimit_Sub
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f - g) x₀
         =. lim₋ f x₀ - lim₋ g x₀
            := Sub
      _  =. the L₁ - the L₂
            := by rw [~ AutoLeftLimit.eq h₁, ~ AutoLeftLimit.eq h₂]
      _  =. the (L₁ - L₂)
            := by rfl

private instance leftlimit_Sub'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Sub.eq

private instance leftlimit_Mul
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₋ (f * g) x₀
         =. lim₋ f x₀ * lim₋ g x₀
            := Mul
      _  =. the L₁ * the L₂
            := by rw [~ AutoLeftLimit.eq h₁, ~ AutoLeftLimit.eq h₂]
      _  =. the (L₁ * L₂)
            := by rfl

private instance leftlimit_Mul'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := leftlimit_Mul.eq

private instance leftlimit_Div
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim₋ (f / g) x₀
         =. lim₋ f x₀ / lim₋ g x₀
            := Div
      _  =. the L₁ / the L₂
            := by rw [~ AutoLeftLimit.eq h₁, ~ AutoLeftLimit.eq h₂]
      _  =. the (L₁ / L₂)
             := finite_div h_L₂_ne0

private instance leftlimit_Div'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := leftlimit_Div.eq

private instance leftlimit_Abs
  : AutoLeftLimit abs x₀ |x₀| True where
  eq := directly Abs

private instance leftlimit_Sqrt
  : AutoLeftLimit sqrt x₀ √x₀ (x₀ > 0) where
  eq := Sqrt

private instance leftlimit_Power
  : AutoLeftLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0) where
  eq := Power

private instance leftlimit_Power_ℤ {n : ℤ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0) where
  eq := Power_ℤ

private instance leftlimit_Power_ℕ {n : ℕ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply Power_ℤ
    exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance leftlimit_Exp
  : AutoLeftLimit exp x₀ (exp x₀) True where
  eq := directly Exp

private instance leftlimit_Expow
  : AutoLeftLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := Expow

private instance leftlimit_Ln
  : AutoLeftLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := Ln

private instance leftlimit_Log
  : AutoLeftLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := Log

private instance leftlimit_Sin
  : AutoLeftLimit sin x₀ (sin x₀) True where
  eq := directly Sin

private instance leftlimit_Cos
  : AutoLeftLimit cos x₀ (cos x₀) True where
  eq := directly Cos

private instance leftlimit_Tan
  : AutoLeftLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := Tan

private instance leftlimit_Cot
  : AutoLeftLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := Cot

private instance leftlimit_Sec
  : AutoLeftLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := Sec

private instance leftlimit_Csc
  : AutoLeftLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := Csc

private instance leftlimit_Sinh
  : AutoLeftLimit sinh x₀ (sinh x₀) True where
  eq := directly Sinh

private instance leftlimit_Cosh
  : AutoLeftLimit cosh x₀ (cosh x₀) True where
  eq := directly Cosh

private instance leftlimit_Tanh
  : AutoLeftLimit tanh x₀ (tanh x₀) True where
  eq := directly Tanh

private instance leftlimit_Coth
  : AutoLeftLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := Coth

private instance leftlimit_Sech
  : AutoLeftLimit sech x₀ (sech x₀) True where
  eq := directly Sech

private instance leftlimit_Csch
  : AutoLeftLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := Csch

private instance leftlimit_Arcsin
  : AutoLeftLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ ≤ 1) where
  eq := Arcsin

private instance leftlimit_Arccos
  : AutoLeftLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ ≤ 1) where
  eq := Arccos

private instance leftlimit_Arctan
  : AutoLeftLimit arctan x₀ (arctan x₀) True where
  eq := directly Arctan

private instance leftlimit_Arccot
  : AutoLeftLimit arccot x₀ (arccot x₀) True where
  eq := directly Arccot

private instance leftlimit_Arcsec
  : AutoLeftLimit arcsec x₀ (arcsec x₀) (x₀ ≤ -1 ∨ x₀ > 1) where
  eq := Arcsec

private instance leftlimit_Arccsc
  : AutoLeftLimit arccsc x₀ (arccsc x₀) (x₀ ≤ -1 ∨ x₀ > 1) where
  eq := Arccsc

private instance leftlimit_compAbs
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance leftlimit_compAbs'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := leftlimit_compAbs.eq

private instance leftlimit_compSqrt
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance leftlimit_compSqrt'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := leftlimit_compSqrt.eq

private instance leftlimit_compPower
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance leftlimit_compPower'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := leftlimit_compPower.eq

private instance leftlimit_compPower''
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := leftlimit_compPower.eq

private instance leftlimit_compPower_ℤ {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance leftlimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℤ.eq

private instance leftlimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℤ.eq

private instance leftlimit_compPower_ℕ {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance leftlimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℕ.eq

private instance leftlimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := leftlimit_compPower_ℕ.eq

private instance leftlimit_compExp
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance leftlimit_compExp'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := leftlimit_compExp.eq

private instance leftlimit_compExpow
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance leftlimit_compExpow'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := leftlimit_compExpow.eq

private instance leftlimit_compLn
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance leftlimit_compLn'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := leftlimit_compLn.eq

private instance leftlimit_compLog
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance leftlimit_compLog'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := leftlimit_compLog.eq

private instance leftlimit_compSin
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance leftlimit_compSin'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := leftlimit_compSin.eq

private instance leftlimit_compCos
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance leftlimit_compCos'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := leftlimit_compCos.eq

private instance leftlimit_compTan
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance leftlimit_compTan'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := leftlimit_compTan.eq

private instance leftlimit_compCot
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance leftlimit_compCot'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := leftlimit_compCot.eq

private instance leftlimit_compSec
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance leftlimit_compSec'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := leftlimit_compSec.eq

private instance leftlimit_compCsc
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance leftlimit_compCsc'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := leftlimit_compCsc.eq

private instance leftlimit_compSinh
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance leftlimit_compSinh'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := leftlimit_compSinh.eq

private instance leftlimit_compCosh
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance leftlimit_compCosh'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := leftlimit_compCosh.eq

private instance leftlimit_compTanh
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance leftlimit_compTanh'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := leftlimit_compTanh.eq

private instance leftlimit_compCoth
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance leftlimit_compCoth'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := leftlimit_compCoth.eq

private instance leftlimit_compSech
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance leftlimit_compSech'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := leftlimit_compSech.eq

private instance leftlimit_compCsch
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance leftlimit_compCsch'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := leftlimit_compCsch.eq

private instance leftlimit_compArcsin
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance leftlimit_compArcsin'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := leftlimit_compArcsin.eq

private instance leftlimit_compArccos
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance leftlimit_compArccos'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := leftlimit_compArccos.eq

private instance leftlimit_compArctan
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance leftlimit_compArctan'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := leftlimit_compArctan.eq

private instance leftlimit_compArccot
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance leftlimit_compArccot'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := leftlimit_compArccot.eq

private instance leftlimit_compArcsec
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance leftlimit_compArcsec'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := leftlimit_compArcsec.eq

private instance leftlimit_compArccsc
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance leftlimit_compArccsc'
    [h_f : AutoLeftLimit f x₀ L₁ c]
  : AutoLeftLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := leftlimit_compArccsc.eq

end

open RightLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c c₁ c₂ : Prop}

private instance rightlimit_patch₁
  : AutoRightLimit (k + ·) x₀ (k + x₀) True where
  eq := by
    intros
    calc
            lim₊ (k + ·) x₀
         =. lim₊ (const k) x₀ + lim₊ id x₀
            := Add
      _  =. the k + the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k + x₀)
            := by rfl

private instance rightlimit_patch₁'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoLeftLimit ((k + ·) ∘ f) x₀ (k + L₁) c where
  eq := sorry

private instance rightlimit_patch₂
  : AutoRightLimit (k - ·) x₀ (k - x₀) True where
  eq := by
    intros
    calc
            lim₊ (k - ·) x₀
         =. lim₊ (const k) x₀ - lim₊ id x₀
            := Sub
      _  =. the k - the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k - x₀)
            := by rfl

private instance rightlimit_patch₂'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k - ·) ∘ f) x₀ (k - L₁) c where
  eq := sorry

private instance rightlimit_patch₃
  : AutoRightLimit (k * ·) x₀ (k * x₀) True where
  eq := by
    intros
    calc
            lim₊ (k * ·) x₀
         =. lim₊ (const k) x₀ * lim₊ id x₀
            := Mul
      _  =. the k * the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k * x₀)
            := by rfl

private instance rightlimit_patch₃'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k * ·) ∘ f) x₀ (k * L₁) c where
  eq := sorry

private instance rightlimit_patch₄
  : AutoRightLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₊ (k / ·) x₀
         =. lim₊ (const k) x₀ / lim₊ id x₀
            := Div
      _  =. the k / the x₀
            := by rw [~ Constant, ~ Identity]
      _  =. the (k / x₀)
             := finite_div h_x₀_ne0

private instance rightlimit_patch₄'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((k / ·) ∘ f) x₀ (k / L₁) (c ∧ f x₀ ≠ 0) where
  eq := sorry

private instance rightlimit_patch₅
  : AutoRightLimit (-·) x₀ (-x₀) True where
  eq := by
    intros
    calc
            lim₊ (-·) x₀
         =. - lim₊ id x₀
            := Neg
      _  =. - the x₀
            := by rw [~ Identity]
      _  =. the (-x₀)
            := by rfl

private instance rightlimit_patch₅'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((-·) ∘ f) x₀ (-L₁) c where
  eq := sorry

private instance rightlimit_patch₆
  : AutoRightLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    calc
            lim₊ (·⁻¹) x₀
         =. (lim₊ id x₀)⁻¹
            := Inv
      _  =. (the x₀)⁻¹
            := by rw [~ Identity]
      _  =. the x₀⁻¹
             := by
               change (if x₀ ≠ 0 then the x₀⁻¹ else infty) =. the x₀⁻¹
               rw [if_pos h_x₀_ne0]

private instance rightlimit_patch₆'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ c where
  eq := sorry

private instance rightlimit_Constant
  : AutoRightLimit (const C) x₀ C True where
  eq := directly Constant

private instance rightlimit_Constant'
  : AutoRightLimit (fun _ ↦ C) x₀ C True where
  eq := rightlimit_Constant.eq

private instance rightlimit_Identity
  : AutoRightLimit id x₀ x₀ True where
  eq := directly Identity

private instance rightlimit_Identity'
  : AutoRightLimit (·) x₀ x₀ True where
  eq := rightlimit_Identity.eq

private instance rightlimit_SMul
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (k • f) x₀ (k * L₁) c where
  eq := by
    intro h_cond
    calc
            lim₊ (k • f) x₀
         =. the k * lim₊ f x₀
            := SMul
      _  =. the k * the L₁
            := by rw [~ AutoRightLimit.eq h_cond]
      _  =. the (k * L₁)
            := by rfl

private instance rightlimit_Neg
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (-f) x₀ (-L₁) c where
  eq := by
    intro h_cond
    calc
            lim₊ (-f) x₀
         =. - lim₊ f x₀
            := Neg
      _  =. - the L₁
            := by rw [~ AutoRightLimit.eq h_cond]
      _  =. the (-L₁)
            := by rfl

private instance rightlimit_Neg'
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ - f x) x₀ (-L₁) c where
  eq := rightlimit_Neg.eq

private instance rightlimit_Inv
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit f⁻¹ x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_L_ne0⟩
    calc
            lim₊ f⁻¹ x₀
         =. (lim₊ f x₀)⁻¹
            := Inv
      _  =. (the L₁)⁻¹
            := by rw [~ AutoRightLimit.eq h_cond]
      _  =. the L₁⁻¹
             := by
               change (if L₁ ≠ 0 then the L₁⁻¹ else infty) =. the L₁⁻¹
               rw [if_pos h_L_ne0]

private instance rightlimit_Inv'
    [AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c ∧ L₁ ≠ 0) where
  eq := rightlimit_Inv.eq

private instance rightlimit_Add
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f + g) x₀
         =. lim₊ f x₀ + lim₊ g x₀
            := Add
      _  =. the L₁ + the L₂
            := by rw [~ AutoRightLimit.eq h₁, ~ AutoRightLimit.eq h₂]
      _  =. the (L₁ + L₂)
            := by rfl

private instance rightlimit_Add'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Add.eq

private instance rightlimit_Sub
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f - g) x₀
         =. lim₊ f x₀ - lim₊ g x₀
            := Sub
      _  =. the L₁ - the L₂
            := by rw [~ AutoRightLimit.eq h₁, ~ AutoRightLimit.eq h₂]
      _  =. the (L₁ - L₂)
            := by rfl

private instance rightlimit_Sub'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Sub.eq

private instance rightlimit_Mul
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h₁, h₂⟩
    calc
            lim₊ (f * g) x₀
         =. lim₊ f x₀ * lim₊ g x₀
            := Mul
      _  =. the L₁ * the L₂
            := by rw [~ AutoRightLimit.eq h₁, ~ AutoRightLimit.eq h₂]
      _  =. the (L₁ * L₂)
            := by rfl

private instance rightlimit_Mul'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂) where
  eq := rightlimit_Mul.eq

private instance rightlimit_Div
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := by
    intro ⟨h₁, h₂, h_L₂_ne0⟩
    calc
            lim₊ (f / g) x₀
         =. lim₊ f x₀ / lim₊ g x₀
            := Div
      _  =. the L₁ / the L₂
            := by rw [~ AutoRightLimit.eq h₁, ~ AutoRightLimit.eq h₂]
      _  =. the (L₁ / L₂)
             := finite_div h_L₂_ne0

private instance rightlimit_Div'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0) where
  eq := rightlimit_Div.eq

private instance rightlimit_Abs
  : AutoRightLimit abs x₀ |x₀| True where
  eq := directly Abs

private instance rightlimit_Sqrt
  : AutoRightLimit sqrt x₀ √x₀ (x₀ ≥ 0) where
  eq := Sqrt

private instance rightlimit_Power
  : AutoRightLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0 ∨ a ≥ 0 ∧ x₀ = 0) where
  eq := Power

private instance rightlimit_Power_ℤ {n : ℤ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0) where
  eq := Power_ℤ

private instance rightlimit_Power_ℕ {n : ℕ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply Power_ℤ
    exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance rightlimit_Exp
  : AutoRightLimit exp x₀ (exp x₀) True where
  eq := directly Exp

private instance rightlimit_Expow
  : AutoRightLimit (a ^ ·) x₀ (a ^ x₀) (a > 0) where
  eq := Expow

private instance rightlimit_Ln
  : AutoRightLimit ln x₀ (ln x₀) (x₀ > 0) where
  eq := Ln

private instance rightlimit_Log
  : AutoRightLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := Log

private instance rightlimit_Sin
  : AutoRightLimit sin x₀ (sin x₀) True where
  eq := directly Sin

private instance rightlimit_Cos
  : AutoRightLimit cos x₀ (cos x₀) True where
  eq := directly Cos

private instance rightlimit_Tan
  : AutoRightLimit tan x₀ (tan x₀) (cos x₀ ≠ 0) where
  eq := Tan

private instance rightlimit_Cot
  : AutoRightLimit cot x₀ (cot x₀) (sin x₀ ≠ 0) where
  eq := Cot

private instance rightlimit_Sec
  : AutoRightLimit sec x₀ (sec x₀) (cos x₀ ≠ 0) where
  eq := Sec

private instance rightlimit_Csc
  : AutoRightLimit csc x₀ (csc x₀) (sin x₀ ≠ 0) where
  eq := Csc

private instance rightlimit_Sinh
  : AutoRightLimit sinh x₀ (sinh x₀) True where
  eq := directly Sinh

private instance rightlimit_Cosh
  : AutoRightLimit cosh x₀ (cosh x₀) True where
  eq := directly Cosh

private instance rightlimit_Tanh
  : AutoRightLimit tanh x₀ (tanh x₀) True where
  eq := directly Tanh

private instance rightlimit_Coth
  : AutoRightLimit coth x₀ (coth x₀) (x₀ ≠ 0) where
  eq := Coth

private instance rightlimit_Sech
  : AutoRightLimit sech x₀ (sech x₀) True where
  eq := directly Sech

private instance rightlimit_Csch
  : AutoRightLimit csch x₀ (csch x₀) (x₀ ≠ 0) where
  eq := Csch

private instance rightlimit_Arcsin
  : AutoRightLimit arcsin x₀ (arcsin x₀) (x₀ ≥ -1 ∧ x₀ < 1) where
  eq := Arcsin

private instance rightlimit_Arccos
  : AutoRightLimit arccos x₀ (arccos x₀) (x₀ ≥ -1 ∧ x₀ < 1) where
  eq := Arccos

private instance rightlimit_Arctan
  : AutoRightLimit arctan x₀ (arctan x₀) True where
  eq := directly Arctan

private instance rightlimit_Arccot
  : AutoRightLimit arccot x₀ (arccot x₀) True where
  eq := directly Arccot

private instance rightlimit_Arcsec
  : AutoRightLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ ≥ 1) where
  eq := Arcsec

private instance rightlimit_Arccsc
  : AutoRightLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ ≥ 1) where
  eq := Arccsc

private instance rightlimit_compAbs
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (abs ∘ f) x₀ (|L₁|) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Abs

private instance rightlimit_compAbs'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ |f x|) x₀ |L₁| c where
  eq := rightlimit_compAbs.eq

private instance rightlimit_compSqrt
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sqrt ∘ f) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sqrt h_dom

private instance rightlimit_compSqrt'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ √(f x)) x₀ √L₁ (c ∧ L₁ > 0) where
  eq := rightlimit_compSqrt.eq

private instance rightlimit_compPower
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power h_dom

private instance rightlimit_compPower'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := rightlimit_compPower.eq

private instance rightlimit_compPower''
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c ∧ L₁ > 0) where
  eq := rightlimit_compPower.eq

private instance rightlimit_compPower_ℤ {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Power_ℤ h_dom

private instance rightlimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℤ.eq

private instance rightlimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n ≥ 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℤ.eq

private instance rightlimit_compPower_ℕ {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · apply FuncLimitExpr.Power_ℤ
      exact h_dom.imp (fun _ ↦ Int.natCast_nonneg n) id

private instance rightlimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℕ.eq

private instance rightlimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c ∧ (n > 0 ∨ L₁ ≠ 0)) where
  eq := rightlimit_compPower_ℕ.eq

private instance rightlimit_compExp
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (exp ∘ f) x₀ (exp L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Exp

private instance rightlimit_compExp'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c where
  eq := rightlimit_compExp.eq

private instance rightlimit_compExpow
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Expow h_dom

private instance rightlimit_compExpow'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c ∧ a > 0) where
  eq := rightlimit_compExpow.eq

private instance rightlimit_compLn
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (ln ∘ f) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Ln h_dom

private instance rightlimit_compLn'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c ∧ L₁ > 0) where
  eq := rightlimit_compLn.eq

private instance rightlimit_compLog
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (log a ∘ f) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Log h_dom

private instance rightlimit_compLog'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := rightlimit_compLog.eq

private instance rightlimit_compSin
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sin ∘ f) x₀ (sin L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sin

private instance rightlimit_compSin'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c where
  eq := rightlimit_compSin.eq

private instance rightlimit_compCos
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cos ∘ f) x₀ (cos L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cos

private instance rightlimit_compCos'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c where
  eq := rightlimit_compCos.eq

private instance rightlimit_compTan
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (tan ∘ f) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tan h_dom

private instance rightlimit_compTan'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := rightlimit_compTan.eq

private instance rightlimit_compCot
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cot ∘ f) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cot h_dom

private instance rightlimit_compCot'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := rightlimit_compCot.eq

private instance rightlimit_compSec
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sec ∘ f) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sec h_dom

private instance rightlimit_compSec'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c ∧ (cos L₁ ≠ 0)) where
  eq := rightlimit_compSec.eq

private instance rightlimit_compCsc
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (csc ∘ f) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csc h_dom

private instance rightlimit_compCsc'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c ∧ (sin L₁ ≠ 0)) where
  eq := rightlimit_compCsc.eq

private instance rightlimit_compSinh
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sinh ∘ f) x₀ (sinh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sinh

private instance rightlimit_compSinh'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c where
  eq := rightlimit_compSinh.eq

private instance rightlimit_compCosh
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (cosh ∘ f) x₀ (cosh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Cosh

private instance rightlimit_compCosh'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c where
  eq := rightlimit_compCosh.eq

private instance rightlimit_compTanh
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (tanh ∘ f) x₀ (tanh L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Tanh

private instance rightlimit_compTanh'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c where
  eq := rightlimit_compTanh.eq

private instance rightlimit_compCoth
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (coth ∘ f) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Coth h_dom

private instance rightlimit_compCoth'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c ∧ L₁ ≠ 0) where
  eq := rightlimit_compCoth.eq

private instance rightlimit_compSech
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (sech ∘ f) x₀ (sech L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Sech

private instance rightlimit_compSech'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c where
  eq := rightlimit_compSech.eq

private instance rightlimit_compCsch
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (csch ∘ f) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Csch h_dom

private instance rightlimit_compCsch'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c ∧ L₁ ≠ 0) where
  eq := rightlimit_compCsch.eq

private instance rightlimit_compArcsin
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arcsin ∘ f) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsin h_dom

private instance rightlimit_compArcsin'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := rightlimit_compArcsin.eq

private instance rightlimit_compArccos
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccos ∘ f) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccos h_dom

private instance rightlimit_compArccos'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c ∧ (L₁ > -1 ∧ L₁ < 1)) where
  eq := rightlimit_compArccos.eq

private instance rightlimit_compArctan
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arctan ∘ f) x₀ (arctan L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arctan

private instance rightlimit_compArctan'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c where
  eq := rightlimit_compArctan.eq

private instance rightlimit_compArccot
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccot ∘ f) x₀ (arccot L₁) c where
  eq := by
    intro h_cond
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccot

private instance rightlimit_compArccot'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c where
  eq := rightlimit_compArccot.eq

private instance rightlimit_compArcsec
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arcsec ∘ f) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arcsec h_dom

private instance rightlimit_compArcsec'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := rightlimit_compArcsec.eq

private instance rightlimit_compArccsc
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (arccsc ∘ f) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    apply CompSV
    · exact h_f.eq h_cond
    · exact FuncLimitExpr.Arccsc h_dom

private instance rightlimit_compArccsc'
    [h_f : AutoRightLimit f x₀ L₁ c]
  : AutoRightLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c ∧ (L₁ < -1 ∨ L₁ > 1)) where
  eq := rightlimit_compArccsc.eq

end

section
variable {f : ℝ → ℝ} {x₀ L₁ : ℝ} {cond : Prop}

lemma autoFuncLimit
    [AutoLimit f x₀ L₁ cond] (h_cond : cond)
  : lim f x₀ = the L₁
:= ~ AutoLimit.eq h_cond

lemma autoLeftLimit
    [AutoLeftLimit f x₀ L₁ cond] (h_cond : cond)
  : lim₋ f x₀ = the L₁
:= ~ AutoLeftLimit.eq h_cond

lemma autoRightLimit
    [AutoRightLimit f x₀ L₁ cond] (h_cond : cond)
  : lim₊ f x₀ = the L₁
:= ~ AutoRightLimit.eq h_cond

end


/-- # Limit Calculator (Based on Continuity)

    __Usage__ `lim_cont`

    - Only used for limit expression, including
      - `SeqLimitExpr` (not yet)
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`
      - `NegInftyLimitExpr` (not yet)
      - `PosInftyLimitExpr` (not yet)
      - `InftyLimitExpr` (not yet)

    - `lim_cont` calculates limit expressions as much as possible in standard
      forms, and then uses built-in tactic `auto_eq` to solve the remaining goal.

    - `lim_cont` requires some side-conditions to exist in the context, which are
      the sum of the corresponding conditions for these different functions:

      - `f x ≠ 0` for `lim f⁻¹ x` and other two
      - `g x ≠ 0` for `lim (f / g) x` and other two
      - `x > 0` for `lim sqrt x` and `lim₋ sqrt x`
      - `x ≥ 0` for `lim₊ sqrt x`
      - `x > 0` for `lim (pow a) x` and `lim₋ (pow a) x`
      - `x > 0 ∨ a > 0 ∧ x = 0` for `lim₊ (pow a) x`
      - `n > 0 ∨ x ≠ 0` for `lim (npow n) x` and other two
      - `a > 0` for `lim (a ^ ·) x` and other two
      - `x > 0` for `lim ln x` and other two
      - `x > 0 ∧ a > 0 ∧ a ≠ 1` for `lim (log a) x` and other two
      - `cos x ≠ 0` for `lim tan x` and other two
      - `sin x ≠ 0` for `lim cot x` and other two
      - `cos x ≠ 0` for `lim sec x` and other two
      - `sin x ≠ 0` for `lim csc x` and other two
      - `x ≠ 0` for `lim coth x` and other two
      - `x ≠ 0` for `lim csch x` and other two
      - `x > -1 ∧ x < 1` for `lim arcsin x`
      - `x > -1 ∧ x ≤ 1` for `lim₋ arcsin x`
      - `x ≥ -1 ∧ x < 1` for `lim₊ arcsin x`
      - `x > -1 ∧ x < 1` for `lim arccos x`
      - `x > -1 ∧ x ≤ 1` for `lim₋ arccos x`
      - `x ≥ -1 ∧ x < 1` for `lim₊ arccos x`
      - `x < -1 ∨ x > 1` for `lim arcsec x`
      - `x ≤ -1 ∨ x > 1` for `lim₋ arcsec x`
      - `x < -1 ∨ x ≥ 1` for `lim₊ arcsec x`
      - `x < -1 ∨ x > 1` for `lim arccsc x`
      - `x ≤ -1 ∨ x > 1` for `lim₋ arccsc x`
      - `x < -1 ∨ x ≥ 1` for `lim₊ arccsc x`

      For composite functions, the `x` above represents the inner function.

    - The side-conditions should preferably be provided as they are. If not, the
      following tactics will be used to complete the remaining conditions:
      - `trivial`
      - `tauto`
      - `positivity`
      - `nlinarith`
      - `norm_num`

    __Examples__
    ```lean
    variable {x : ℝ}
    example
      : lim (fun t ↦ ln t / t) 1 = the 0
    := by lim_cont
    example
      : lim (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x))
    := by lim_cont
    example (_ : x ≠ 0)
      : lim (fun t ↦ t⁻¹ + t) x = the ((x ^ 2 + 1) / x)
    := by lim_cont
    ```
-/
macro "lim_cont" : tactic => `(tactic| (
  intros
  repeat rw [autoFuncLimit]
  repeat rw [autoLeftLimit]
  repeat rw [autoRightLimit]
  all_goals try auto_side_condition
  try focus norm_num
  try focus field
  try focus ring
  try focus lim_congr_by field within 1
))

variable {x : ℝ}
example
  : lim (fun t ↦ ln t / t) 1 = the 0
:= by lim_cont
example
  : lim (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x))
:= by lim_cont
example (_ : x ≠ 0)
  : lim (fun t ↦ t⁻¹ + t) x = the ((x ^ 2 + 1) / x)
:= by lim_cont


page_end
