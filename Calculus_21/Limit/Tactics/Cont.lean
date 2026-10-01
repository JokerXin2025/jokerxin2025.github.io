/-
    «Calculus_21».Limit.Tactics.Cont
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc
import «Calculus_21».Limit.Expr.Elementary
import «Calculus_21».Limit.Tactics.Rules
set_option linter.style.header false

open LimitValue (finite_iff finite_div)


class AutoLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim x₀ f =. the val

class AutoLeftLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₋ x₀ f =. the val

class AutoRightLimit (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → lim₊ x₀ f =. the val

open FuncLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c₁ c₂ : Prop}

private instance funclimit_patch₁
  : AutoLimit (k + ·) x₀ (k + x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim x₀ (const k) + lim x₀ id
          := by lim_add
    _  =  the k + the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k + x₀)
          := rfl

private instance funclimit_patch₁'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((k + ·) ∘ f) x₀ (k + L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₁.eq trivial)⟩

private instance funclimit_patch₂
  : AutoLimit (k - ·) x₀ (k - x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim x₀ (const k) - lim x₀ id
          := by lim_sub
    _  =  the k - the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k - x₀)
          := rfl

private instance funclimit_patch₂'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((k - ·) ∘ f) x₀ (k - L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₂.eq trivial)⟩

private instance funclimit_patch₃
  : AutoLimit (k * ·) x₀ (k * x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim x₀ (const k) * lim x₀ id
          := by lim_mul
    _  =  the k * the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k * x₀)
          := rfl

private instance funclimit_patch₃'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((k * ·) ∘ f) x₀ (k * L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₃.eq trivial)⟩

private instance funclimit_patch₄
  : AutoLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. lim x₀ (const k) / lim x₀ id
          := by lim_div
    _  =  the k / the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k / x₀)
          := by poly_rw [finite_div h_dom]

private instance funclimit_patch₄'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((k / ·) ∘ f) x₀ (k / L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₄.eq h_dom)⟩

private instance funclimit_patch₅
  : AutoLimit (-·) x₀ (-x₀) True
:= by
  constructor
  intro _
  calc
    _  =. - lim x₀ id
          := by lim_neg
    _  =  - the x₀
          := by poly_rw [Identity]
    _  =  the (-x₀)
          := rfl

private instance funclimit_patch₅'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((-·) ∘ f) x₀ (-L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₅.eq trivial)⟩

private instance funclimit_patch₆
  : AutoLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. (lim x₀ id)⁻¹
          := by lim_inv
    _  =  (the x₀)⁻¹
          := by poly_rw [Identity]
    _  =  the x₀⁻¹
          := by
            change (if x₀ ≠ 0 then the x₀⁻¹ else infty) = the x₀⁻¹
            rw_pos h_dom

private instance funclimit_patch₆'
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₆.eq h_dom)⟩

private instance funclimit_Constant
  : AutoLimit (const C) x₀ C True
:= ⟨directly Constant⟩

private instance funclimit_Constant'
  : AutoLimit (fun _ ↦ C) x₀ C True
:= funclimit_Constant

private instance funclimit_Identity
  : AutoLimit id x₀ x₀ True
:= ⟨directly Identity⟩

private instance funclimit_Identity'
  : AutoLimit (·) x₀ x₀ True
:= funclimit_Identity

private instance funclimit_Neg
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (-f) x₀ (-L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. - lim x₀ f
          := by lim_neg
    _  =  - the L₁
          := by poly_rw [AutoLimit.eq h₁]
    _  =  the (-L₁)
          := rfl

private instance funclimit_Neg'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ - f x) x₀ (-L₁) c₁
:= funclimit_Neg

private instance funclimit_SMul
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (k • f) x₀ (k * L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. the k * lim x₀ f
          := by lim_smul
    _  =  the k * the L₁
          := by poly_rw [AutoLimit.eq h₁]
    _  =  the (k * L₁)
          := rfl

private instance funclimit_Inv
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit f⁻¹ x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  calc
    _  =. (lim x₀ f)⁻¹
          := by lim_inv
    _  =  (the L₁)⁻¹
          := by poly_rw [AutoLimit.eq h₁]
    _  =  the L₁⁻¹
          := by
            change (if L₁ ≠ 0 then the L₁⁻¹ else infty) = the L₁⁻¹
            rw_pos h_dom

private instance funclimit_Inv'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= funclimit_Inv

private instance funclimit_Add
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim x₀ f + lim x₀ g
          := by lim_add
    _  =  the L₁ + the L₂
          := by poly_rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
    _  =  the (L₁ + L₂)
          := rfl

private instance funclimit_Add'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= funclimit_Add

private instance funclimit_Sub
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim x₀ f - lim x₀ g
          := by lim_sub
    _  =  the L₁ - the L₂
          := by poly_rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
    _  =  the (L₁ - L₂)
          := rfl

private instance funclimit_Sub'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= funclimit_Sub

private instance funclimit_Mul
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim x₀ f * lim x₀ g
          := by lim_mul
    _  =  the L₁ * the L₂
          := by poly_rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
    _  =  the (L₁ * L₂)
          := rfl

private instance funclimit_Mul'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= funclimit_Mul

private instance funclimit_Div
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h₂, h_dom⟩
  calc
    _  =. lim x₀ f / lim x₀ g
          := by lim_div
    _  =  the L₁ / the L₂
          := by poly_rw [AutoLimit.eq h₁, AutoLimit.eq h₂]
    _  =  the (L₁ / L₂)
          := by poly_rw [finite_div h_dom]

private instance funclimit_Div'
    [AutoLimit f x₀ L₁ c₁] [AutoLimit g x₀ L₂ c₂]
  : AutoLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= funclimit_Div

private instance funclimit_Abs
  : AutoLimit abs x₀ |x₀| True
:= ⟨directly Abs⟩

private instance funclimit_Sqrt
  : AutoLimit sqrt x₀ √x₀ (x₀ > 0)
:= ⟨Sqrt⟩

private instance funclimit_Power
  : AutoLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0)
:= ⟨Power⟩

private instance funclimit_Power_ℤ {n : ℤ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0)
:= ⟨Power_ℤ⟩

private instance funclimit_Power_ℕ {n : ℕ}
  : AutoLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0)
:= ⟨fun h_dom => Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id)⟩

private instance funclimit_Exp
  : AutoLimit exp x₀ (exp x₀) True
:= ⟨directly Exp⟩

private instance funclimit_Expow
  : AutoLimit (a ^ ·) x₀ (a ^ x₀) (a > 0)
:= ⟨Expow⟩

private instance funclimit_Ln
  : AutoLimit ln x₀ (ln x₀) (x₀ > 0)
:= ⟨Ln⟩

private instance funclimit_Log
  : AutoLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨Log⟩

private instance funclimit_Sin
  : AutoLimit sin x₀ (sin x₀) True
:= ⟨directly Sin⟩

private instance funclimit_Cos
  : AutoLimit cos x₀ (cos x₀) True
:= ⟨directly Cos⟩

private instance funclimit_Tan
  : AutoLimit tan x₀ (tan x₀) (cos x₀ ≠ 0)
:= ⟨Tan⟩

private instance funclimit_Cot
  : AutoLimit cot x₀ (cot x₀) (sin x₀ ≠ 0)
:= ⟨Cot⟩

private instance funclimit_Sec
  : AutoLimit sec x₀ (sec x₀) (cos x₀ ≠ 0)
:= ⟨Sec⟩

private instance funclimit_Csc
  : AutoLimit csc x₀ (csc x₀) (sin x₀ ≠ 0)
:= ⟨Csc⟩

private instance funclimit_Sinh
  : AutoLimit sinh x₀ (sinh x₀) True
:= ⟨directly Sinh⟩

private instance funclimit_Cosh
  : AutoLimit cosh x₀ (cosh x₀) True
:= ⟨directly Cosh⟩

private instance funclimit_Tanh
  : AutoLimit tanh x₀ (tanh x₀) True
:= ⟨directly Tanh⟩

private instance funclimit_Coth
  : AutoLimit coth x₀ (coth x₀) (x₀ ≠ 0)
:= ⟨Coth⟩

private instance funclimit_Sech
  : AutoLimit sech x₀ (sech x₀) True
:= ⟨directly Sech⟩

private instance funclimit_Csch
  : AutoLimit csch x₀ (csch x₀) (x₀ ≠ 0)
:= ⟨Csch⟩

private instance funclimit_Arcsin
  : AutoLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ < 1)
:= ⟨Arcsin⟩

private instance funclimit_Arccos
  : AutoLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ < 1)
:= ⟨Arccos⟩

private instance funclimit_Arctan
  : AutoLimit arctan x₀ (arctan x₀) True
:= ⟨directly Arctan⟩

private instance funclimit_Arccot
  : AutoLimit arccot x₀ (arccot x₀) True
:= ⟨directly Arccot⟩

private instance funclimit_Arcsec
  : AutoLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ > 1)
:= ⟨Arcsec⟩

private instance funclimit_Arccsc
  : AutoLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ > 1)
:= ⟨Arccsc⟩

private instance funclimit_compAbs
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (abs ∘ f) x₀ (|L₁|) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Abs⟩

private instance funclimit_compAbs'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ |f x|) x₀ |L₁| c₁
:= funclimit_compAbs

private instance funclimit_compSqrt
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (sqrt ∘ f) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Sqrt h_dom)⟩

private instance funclimit_compSqrt'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ √(f x)) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= funclimit_compSqrt

private instance funclimit_compPower
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Power h_dom)⟩

private instance funclimit_compPower'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= funclimit_compPower

private instance funclimit_compPower''
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= funclimit_compPower

private instance funclimit_compPower_ℤ {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Power_ℤ h_dom)⟩

private instance funclimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= funclimit_compPower_ℤ

private instance funclimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= funclimit_compPower_ℤ

private instance funclimit_compPower_ℕ {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ =>
    CompSV (h_f.eq h₁) (Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id))⟩

private instance funclimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= funclimit_compPower_ℕ

private instance funclimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= funclimit_compPower_ℕ

private instance funclimit_compExp
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (exp ∘ f) x₀ (exp L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Exp⟩

private instance funclimit_compExp'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c₁
:= funclimit_compExp

private instance funclimit_compExpow
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Expow h_dom)⟩

private instance funclimit_compExpow'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= funclimit_compExpow

private instance funclimit_compLn
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (ln ∘ f) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Ln h_dom)⟩

private instance funclimit_compLn'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= funclimit_compLn

private instance funclimit_compLog
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (log a ∘ f) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Log h_dom)⟩

private instance funclimit_compLog'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= funclimit_compLog

private instance funclimit_compSin
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (sin ∘ f) x₀ (sin L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Sin⟩

private instance funclimit_compSin'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c₁
:= funclimit_compSin

private instance funclimit_compCos
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (cos ∘ f) x₀ (cos L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Cos⟩

private instance funclimit_compCos'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c₁
:= funclimit_compCos

private instance funclimit_compTan
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (tan ∘ f) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Tan h_dom)⟩

private instance funclimit_compTan'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= funclimit_compTan

private instance funclimit_compCot
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (cot ∘ f) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Cot h_dom)⟩

private instance funclimit_compCot'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= funclimit_compCot

private instance funclimit_compSec
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (sec ∘ f) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Sec h_dom)⟩

private instance funclimit_compSec'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= funclimit_compSec

private instance funclimit_compCsc
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (csc ∘ f) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Csc h_dom)⟩

private instance funclimit_compCsc'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= funclimit_compCsc

private instance funclimit_compSinh
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (sinh ∘ f) x₀ (sinh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Sinh⟩

private instance funclimit_compSinh'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c₁
:= funclimit_compSinh

private instance funclimit_compCosh
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (cosh ∘ f) x₀ (cosh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Cosh⟩

private instance funclimit_compCosh'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c₁
:= funclimit_compCosh

private instance funclimit_compTanh
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (tanh ∘ f) x₀ (tanh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Tanh⟩

private instance funclimit_compTanh'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c₁
:= funclimit_compTanh

private instance funclimit_compCoth
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (coth ∘ f) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Coth h_dom)⟩

private instance funclimit_compCoth'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= funclimit_compCoth

private instance funclimit_compSech
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (sech ∘ f) x₀ (sech L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Sech⟩

private instance funclimit_compSech'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c₁
:= funclimit_compSech

private instance funclimit_compCsch
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (csch ∘ f) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Csch h_dom)⟩

private instance funclimit_compCsch'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= funclimit_compCsch

private instance funclimit_compArcsin
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arcsin ∘ f) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Arcsin h_dom)⟩

private instance funclimit_compArcsin'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= funclimit_compArcsin

private instance funclimit_compArccos
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arccos ∘ f) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Arccos h_dom)⟩

private instance funclimit_compArccos'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= funclimit_compArccos

private instance funclimit_compArctan
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arctan ∘ f) x₀ (arctan L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Arctan⟩

private instance funclimit_compArctan'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c₁
:= funclimit_compArctan

private instance funclimit_compArccot
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arccot ∘ f) x₀ (arccot L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) Arccot⟩

private instance funclimit_compArccot'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c₁
:= funclimit_compArccot

private instance funclimit_compArcsec
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arcsec ∘ f) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Arcsec h_dom)⟩

private instance funclimit_compArcsec'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= funclimit_compArcsec

private instance funclimit_compArccsc
    [h_f : AutoLimit f x₀ L₁ c₁]
  : AutoLimit (arccsc ∘ f) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (Arccsc h_dom)⟩

private instance funclimit_compArccsc'
    [AutoLimit f x₀ L₁ c₁]
  : AutoLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= funclimit_compArccsc

end

open LeftLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c₁ c₂ : Prop}

private instance leftlimit_patch₁
  : AutoLeftLimit (k + ·) x₀ (k + x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₋ x₀ (const k) + lim₋ x₀ id
          := by lim_add
    _  =  the k + the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k + x₀)
          := rfl

private instance leftlimit_patch₁'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((k + ·) ∘ f) x₀ (k + L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₁.eq trivial)⟩

private instance leftlimit_patch₂
  : AutoLeftLimit (k - ·) x₀ (k - x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₋ x₀ (const k) - lim₋ x₀ id
          := by lim_sub
    _  =  the k - the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k - x₀)
          := rfl

private instance leftlimit_patch₂'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((k - ·) ∘ f) x₀ (k - L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₂.eq trivial)⟩

private instance leftlimit_patch₃
  : AutoLeftLimit (k * ·) x₀ (k * x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₋ x₀ (const k) * lim₋ x₀ id
          := by lim_mul
    _  =  the k * the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k * x₀)
          := rfl

private instance leftlimit_patch₃'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((k * ·) ∘ f) x₀ (k * L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₃.eq trivial)⟩

private instance leftlimit_patch₄
  : AutoLeftLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. lim₋ x₀ (const k) / lim₋ x₀ id
          := by lim_div
    _  =  the k / the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k / x₀)
          := by poly_rw [finite_div h_dom]

private instance leftlimit_patch₄'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((k / ·) ∘ f) x₀ (k / L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₄.eq h_dom)⟩

private instance leftlimit_patch₅
  : AutoLeftLimit (-·) x₀ (-x₀) True
:= by
  constructor
  intro _
  calc
    _  =. - lim₋ x₀ id
          := by lim_neg
    _  =  - the x₀
          := by poly_rw [Identity]
    _  =  the (-x₀)
          := rfl

private instance leftlimit_patch₅'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((-·) ∘ f) x₀ (-L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₅.eq trivial)⟩

private instance leftlimit_patch₆
  : AutoLeftLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. (lim₋ x₀ id)⁻¹
          := by lim_inv
    _  =  (the x₀)⁻¹
          := by poly_rw [Identity]
    _  =  the x₀⁻¹
          := by
            change (if x₀ ≠ 0 then the x₀⁻¹ else infty) = the x₀⁻¹
            rw_pos h_dom

private instance leftlimit_patch₆'
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₆.eq h_dom)⟩

private instance leftlimit_Constant
  : AutoLeftLimit (const C) x₀ C True
:= ⟨directly Constant⟩

private instance leftlimit_Constant'
  : AutoLeftLimit (fun _ ↦ C) x₀ C True
:= leftlimit_Constant

private instance leftlimit_Identity
  : AutoLeftLimit id x₀ x₀ True
:= ⟨directly Identity⟩

private instance leftlimit_Identity'
  : AutoLeftLimit (·) x₀ x₀ True
:= leftlimit_Identity

private instance leftlimit_Neg
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (-f) x₀ (-L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. - lim₋ x₀ f
          := by lim_neg
    _  =  - the L₁
          := by poly_rw [AutoLeftLimit.eq h₁]
    _  =  the (-L₁)
          := rfl

private instance leftlimit_Neg'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ - f x) x₀ (-L₁) c₁
:= leftlimit_Neg

private instance leftlimit_SMul
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (k • f) x₀ (k * L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. the k * lim₋ x₀ f
          := by lim_smul
    _  =  the k * the L₁
          := by poly_rw [AutoLeftLimit.eq h₁]
    _  =  the (k * L₁)
          := rfl

private instance leftlimit_Inv
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit f⁻¹ x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  calc
    _  =. (lim₋ x₀ f)⁻¹
          := by lim_inv
    _  =  (the L₁)⁻¹
          := by poly_rw [AutoLeftLimit.eq h₁]
    _  =  the L₁⁻¹
          := by
            change (if L₁ ≠ 0 then the L₁⁻¹ else infty) = the L₁⁻¹
            rw_pos h_dom

private instance leftlimit_Inv'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= leftlimit_Inv

private instance leftlimit_Add
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₋ x₀ f + lim₋ x₀ g
          := by lim_add
    _  =  the L₁ + the L₂
          := by poly_rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
    _  =  the (L₁ + L₂)
          := rfl

private instance leftlimit_Add'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= leftlimit_Add

private instance leftlimit_Sub
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₋ x₀ f - lim₋ x₀ g
          := by lim_sub
    _  =  the L₁ - the L₂
          := by poly_rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
    _  =  the (L₁ - L₂)
          := rfl

private instance leftlimit_Sub'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= leftlimit_Sub

private instance leftlimit_Mul
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₋ x₀ f * lim₋ x₀ g
          := by lim_mul
    _  =  the L₁ * the L₂
          := by poly_rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
    _  =  the (L₁ * L₂)
          := rfl

private instance leftlimit_Mul'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= leftlimit_Mul

private instance leftlimit_Div
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h₂, h_dom⟩
  calc
    _  =. lim₋ x₀ f / lim₋ x₀ g
          := by lim_div
    _  =  the L₁ / the L₂
          := by poly_rw [AutoLeftLimit.eq h₁, AutoLeftLimit.eq h₂]
    _  = the (L₁ / L₂)
          := by poly_rw [finite_div h_dom]

private instance leftlimit_Div'
    [AutoLeftLimit f x₀ L₁ c₁] [AutoLeftLimit g x₀ L₂ c₂]
  : AutoLeftLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= leftlimit_Div

private instance leftlimit_Abs
  : AutoLeftLimit abs x₀ |x₀| True
:= ⟨directly Abs⟩

private instance leftlimit_Sqrt
  : AutoLeftLimit sqrt x₀ √x₀ (x₀ > 0)
:= ⟨Sqrt⟩

private instance leftlimit_Power
  : AutoLeftLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0)
:= ⟨Power⟩

private instance leftlimit_Power_ℤ {n : ℤ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0)
:= ⟨Power_ℤ⟩

private instance leftlimit_Power_ℕ {n : ℕ}
  : AutoLeftLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0)
:= ⟨fun h_dom => Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id)⟩

private instance leftlimit_Exp
  : AutoLeftLimit exp x₀ (exp x₀) True
:= ⟨directly Exp⟩

private instance leftlimit_Expow
  : AutoLeftLimit (a ^ ·) x₀ (a ^ x₀) (a > 0)
:= ⟨Expow⟩

private instance leftlimit_Ln
  : AutoLeftLimit ln x₀ (ln x₀) (x₀ > 0)
:= ⟨Ln⟩

private instance leftlimit_Log
  : AutoLeftLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨Log⟩

private instance leftlimit_Sin
  : AutoLeftLimit sin x₀ (sin x₀) True
:= ⟨directly Sin⟩

private instance leftlimit_Cos
  : AutoLeftLimit cos x₀ (cos x₀) True
:= ⟨directly Cos⟩

private instance leftlimit_Tan
  : AutoLeftLimit tan x₀ (tan x₀) (cos x₀ ≠ 0)
:= ⟨Tan⟩

private instance leftlimit_Cot
  : AutoLeftLimit cot x₀ (cot x₀) (sin x₀ ≠ 0)
:= ⟨Cot⟩

private instance leftlimit_Sec
  : AutoLeftLimit sec x₀ (sec x₀) (cos x₀ ≠ 0)
:= ⟨Sec⟩

private instance leftlimit_Csc
  : AutoLeftLimit csc x₀ (csc x₀) (sin x₀ ≠ 0)
:= ⟨Csc⟩

private instance leftlimit_Sinh
  : AutoLeftLimit sinh x₀ (sinh x₀) True
:= ⟨directly Sinh⟩

private instance leftlimit_Cosh
  : AutoLeftLimit cosh x₀ (cosh x₀) True
:= ⟨directly Cosh⟩

private instance leftlimit_Tanh
  : AutoLeftLimit tanh x₀ (tanh x₀) True
:= ⟨directly Tanh⟩

private instance leftlimit_Coth
  : AutoLeftLimit coth x₀ (coth x₀) (x₀ ≠ 0)
:= ⟨Coth⟩

private instance leftlimit_Sech
  : AutoLeftLimit sech x₀ (sech x₀) True
:= ⟨directly Sech⟩

private instance leftlimit_Csch
  : AutoLeftLimit csch x₀ (csch x₀) (x₀ ≠ 0)
:= ⟨Csch⟩

private instance leftlimit_Arcsin
  : AutoLeftLimit arcsin x₀ (arcsin x₀) (x₀ > -1 ∧ x₀ ≤ 1)
:= ⟨Arcsin⟩

private instance leftlimit_Arccos
  : AutoLeftLimit arccos x₀ (arccos x₀) (x₀ > -1 ∧ x₀ ≤ 1)
:= ⟨Arccos⟩

private instance leftlimit_Arctan
  : AutoLeftLimit arctan x₀ (arctan x₀) True
:= ⟨directly Arctan⟩

private instance leftlimit_Arccot
  : AutoLeftLimit arccot x₀ (arccot x₀) True
:= ⟨directly Arccot⟩

private instance leftlimit_Arcsec
  : AutoLeftLimit arcsec x₀ (arcsec x₀) (x₀ ≤ -1 ∨ x₀ > 1)
:= ⟨Arcsec⟩

private instance leftlimit_Arccsc
  : AutoLeftLimit arccsc x₀ (arccsc x₀) (x₀ ≤ -1 ∨ x₀ > 1)
:= ⟨Arccsc⟩

private instance leftlimit_compAbs
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (abs ∘ f) x₀ (|L₁|) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Abs⟩

private instance leftlimit_compAbs'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ |f x|) x₀ |L₁| c₁
:= leftlimit_compAbs

private instance leftlimit_compSqrt
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (sqrt ∘ f) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Sqrt h_dom)⟩

private instance leftlimit_compSqrt'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ √(f x)) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= leftlimit_compSqrt

private instance leftlimit_compPower
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Power h_dom)⟩

private instance leftlimit_compPower'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= leftlimit_compPower

private instance leftlimit_compPower''
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= leftlimit_compPower

private instance leftlimit_compPower_ℤ {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Power_ℤ h_dom)⟩

private instance leftlimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= leftlimit_compPower_ℤ

private instance leftlimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= leftlimit_compPower_ℤ

private instance leftlimit_compPower_ℕ {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ =>
    CompSV (h_f.eq h₁)
      (FuncLimitExpr.Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id))⟩

private instance leftlimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= leftlimit_compPower_ℕ

private instance leftlimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= leftlimit_compPower_ℕ

private instance leftlimit_compExp
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (exp ∘ f) x₀ (exp L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Exp⟩

private instance leftlimit_compExp'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c₁
:= leftlimit_compExp

private instance leftlimit_compExpow
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Expow h_dom)⟩

private instance leftlimit_compExpow'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= leftlimit_compExpow

private instance leftlimit_compLn
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (ln ∘ f) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Ln h_dom)⟩

private instance leftlimit_compLn'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= leftlimit_compLn

private instance leftlimit_compLog
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (log a ∘ f) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Log h_dom)⟩

private instance leftlimit_compLog'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= leftlimit_compLog

private instance leftlimit_compSin
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (sin ∘ f) x₀ (sin L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sin⟩

private instance leftlimit_compSin'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c₁
:= leftlimit_compSin

private instance leftlimit_compCos
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (cos ∘ f) x₀ (cos L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Cos⟩

private instance leftlimit_compCos'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c₁
:= leftlimit_compCos

private instance leftlimit_compTan
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (tan ∘ f) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Tan h_dom)⟩

private instance leftlimit_compTan'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= leftlimit_compTan

private instance leftlimit_compCot
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (cot ∘ f) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Cot h_dom)⟩

private instance leftlimit_compCot'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= leftlimit_compCot

private instance leftlimit_compSec
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (sec ∘ f) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Sec h_dom)⟩

private instance leftlimit_compSec'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= leftlimit_compSec

private instance leftlimit_compCsc
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (csc ∘ f) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Csc h_dom)⟩

private instance leftlimit_compCsc'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= leftlimit_compCsc

private instance leftlimit_compSinh
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (sinh ∘ f) x₀ (sinh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sinh⟩

private instance leftlimit_compSinh'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c₁
:= leftlimit_compSinh

private instance leftlimit_compCosh
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (cosh ∘ f) x₀ (cosh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Cosh⟩

private instance leftlimit_compCosh'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c₁
:= leftlimit_compCosh

private instance leftlimit_compTanh
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (tanh ∘ f) x₀ (tanh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Tanh⟩

private instance leftlimit_compTanh'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c₁
:= leftlimit_compTanh

private instance leftlimit_compCoth
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (coth ∘ f) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Coth h_dom)⟩

private instance leftlimit_compCoth'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= leftlimit_compCoth

private instance leftlimit_compSech
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (sech ∘ f) x₀ (sech L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sech⟩

private instance leftlimit_compSech'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c₁
:= leftlimit_compSech

private instance leftlimit_compCsch
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (csch ∘ f) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Csch h_dom)⟩

private instance leftlimit_compCsch'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= leftlimit_compCsch

private instance leftlimit_compArcsin
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arcsin ∘ f) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arcsin h_dom)⟩

private instance leftlimit_compArcsin'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= leftlimit_compArcsin

private instance leftlimit_compArccos
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arccos ∘ f) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arccos h_dom)⟩

private instance leftlimit_compArccos'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= leftlimit_compArccos

private instance leftlimit_compArctan
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arctan ∘ f) x₀ (arctan L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Arctan⟩

private instance leftlimit_compArctan'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c₁
:= leftlimit_compArctan

private instance leftlimit_compArccot
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arccot ∘ f) x₀ (arccot L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Arccot⟩

private instance leftlimit_compArccot'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c₁
:= leftlimit_compArccot

private instance leftlimit_compArcsec
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arcsec ∘ f) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arcsec h_dom)⟩

private instance leftlimit_compArcsec'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= leftlimit_compArcsec

private instance leftlimit_compArccsc
    [h_f : AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (arccsc ∘ f) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arccsc h_dom)⟩

private instance leftlimit_compArccsc'
    [AutoLeftLimit f x₀ L₁ c₁]
  : AutoLeftLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= leftlimit_compArccsc

end

open RightLimitExpr in section
variable {C k a x₀ L₁ L₂ : ℝ} {f g : ℝ → ℝ} {c₁ c₂ : Prop}

private instance rightlimit_patch₁
  : AutoRightLimit (k + ·) x₀ (k + x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₊ x₀ (const k) + lim₊ x₀ id
          := by lim_add
    _  =  the k + the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k + x₀)
          := rfl

private instance rightlimit_patch₁'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((k + ·) ∘ f) x₀ (k + L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₁.eq trivial)⟩

private instance rightlimit_patch₂
  : AutoRightLimit (k - ·) x₀ (k - x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₊ x₀ (const k) - lim₊ x₀ id
          := by lim_sub
    _  =  the k - the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k - x₀)
          := rfl

private instance rightlimit_patch₂'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((k - ·) ∘ f) x₀ (k - L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₂.eq trivial)⟩

private instance rightlimit_patch₃
  : AutoRightLimit (k * ·) x₀ (k * x₀) True
:= by
  constructor
  intro _
  calc
    _  =. lim₊ x₀ (const k) * lim₊ x₀ id
          := by lim_mul
    _  =  the k * the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k * x₀)
          := rfl

private instance rightlimit_patch₃'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((k * ·) ∘ f) x₀ (k * L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₃.eq trivial)⟩

private instance rightlimit_patch₄
  : AutoRightLimit (k / ·) x₀ (k / x₀) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. lim₊ x₀ (const k) / lim₊ x₀ id
          := by lim_div
    _  =  the k / the x₀
          := by poly_rw [Constant, Identity]
    _  =  the (k / x₀)
          := by poly_rw [finite_div h_dom]

private instance rightlimit_patch₄'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((k / ·) ∘ f) x₀ (k / L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₄.eq h_dom)⟩

private instance rightlimit_patch₅
  : AutoRightLimit (-·) x₀ (-x₀) True
:= by
  constructor
  intro _
  calc
    _  =. - lim₊ x₀ id
          := by lim_neg
    _  =  - the x₀
          := by poly_rw [Identity]
    _  =  the (-x₀)
          := rfl

private instance rightlimit_patch₅'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((-·) ∘ f) x₀ (-L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) (funclimit_patch₅.eq trivial)⟩

private instance rightlimit_patch₆
  : AutoRightLimit (·⁻¹) x₀ (x₀⁻¹) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  calc
    _  =. (lim₊ x₀ id)⁻¹
          := by lim_inv
    _  =  (the x₀)⁻¹
          := by poly_rw [Identity]
    _  =  the x₀⁻¹
          := by
            change (if x₀ ≠ 0 then the x₀⁻¹ else infty) = the x₀⁻¹
            rw_pos h_dom

private instance rightlimit_patch₆'
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((·⁻¹) ∘ f) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (funclimit_patch₆.eq h_dom)⟩

private instance rightlimit_Constant
  : AutoRightLimit (const C) x₀ C True
:= ⟨directly Constant⟩

private instance rightlimit_Constant'
  : AutoRightLimit (fun _ ↦ C) x₀ C True
:= rightlimit_Constant

private instance rightlimit_Identity
  : AutoRightLimit id x₀ x₀ True
:= ⟨directly Identity⟩

private instance rightlimit_Identity'
  : AutoRightLimit (·) x₀ x₀ True
:= rightlimit_Identity

private instance rightlimit_SMul
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (k • f) x₀ (k * L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. the k * lim₊ x₀ f
          := by lim_smul
    _  =  the k * the L₁
          := by poly_rw [AutoRightLimit.eq h₁]
    _  =  the (k * L₁)
          := rfl

private instance rightlimit_Neg
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (-f) x₀ (-L₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. - lim₊ x₀ f
          := by lim_neg
    _  =  - the L₁
          := by poly_rw [AutoRightLimit.eq h₁]
    _  =  the (-L₁)
          := rfl

private instance rightlimit_Neg'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ - f x) x₀ (-L₁) c₁
:= rightlimit_Neg

private instance rightlimit_Inv
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit f⁻¹ x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  calc
    _  =. (lim₊ x₀ f)⁻¹
          := by lim_inv
    _  =  (the L₁)⁻¹
          := by poly_rw [AutoRightLimit.eq h₁]
    _  =  the L₁⁻¹
          := by
            change (if L₁ ≠ 0 then the L₁⁻¹ else infty) = the L₁⁻¹
            rw_pos h_dom

private instance rightlimit_Inv'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ (f x)⁻¹) x₀ L₁⁻¹ (c₁ ∧ L₁ ≠ 0)
:= rightlimit_Inv

private instance rightlimit_Add
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f + g) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₊ x₀ f + lim₊ x₀ g
          := by lim_add
    _  =  the L₁ + the L₂
          := by poly_rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
    _  =  the (L₁ + L₂)
          := rfl

private instance rightlimit_Add'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x + g x) x₀ (L₁ + L₂) (c₁ ∧ c₂)
:= rightlimit_Add

private instance rightlimit_Sub
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f - g) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₊ x₀ f - lim₊ x₀ g
          := by lim_sub
    _  =  the L₁ - the L₂
          := by poly_rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
    _  =  the (L₁ - L₂)
          := rfl

private instance rightlimit_Sub'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x - g x) x₀ (L₁ - L₂) (c₁ ∧ c₂)
:= rightlimit_Sub

private instance rightlimit_Mul
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f * g) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. lim₊ x₀ f * lim₊ x₀ g
          := by lim_mul
    _  =  the L₁ * the L₂
          := by poly_rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
    _  =  the (L₁ * L₂)
          := rfl

private instance rightlimit_Mul'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x * g x) x₀ (L₁ * L₂) (c₁ ∧ c₂)
:= rightlimit_Mul

private instance rightlimit_Div
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (f / g) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h₂, h_dom⟩
  calc
    _  =. lim₊ x₀ f / lim₊ x₀ g
          := by lim_div
    _  =  the L₁ / the L₂
          := by poly_rw [AutoRightLimit.eq h₁, AutoRightLimit.eq h₂]
    _  =  the (L₁ / L₂)
          := by poly_rw [finite_div h_dom]

private instance rightlimit_Div'
    [AutoRightLimit f x₀ L₁ c₁] [AutoRightLimit g x₀ L₂ c₂]
  : AutoRightLimit (fun x ↦ f x / g x) x₀ (L₁ / L₂) (c₁ ∧ c₂ ∧ L₂ ≠ 0)
:= rightlimit_Div

private instance rightlimit_Abs
  : AutoRightLimit abs x₀ |x₀| True
:= ⟨directly Abs⟩

private instance rightlimit_Sqrt
  : AutoRightLimit sqrt x₀ √x₀ (x₀ ≥ 0)
:= ⟨Sqrt⟩

private instance rightlimit_Power
  : AutoRightLimit (pow a) x₀ (x₀ ^ a) (x₀ > 0 ∨ a ≥ 0 ∧ x₀ = 0)
:= ⟨Power⟩

private instance rightlimit_Power_ℤ {n : ℤ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n ≥ 0 ∨ x₀ ≠ 0)
:= ⟨Power_ℤ⟩

private instance rightlimit_Power_ℕ {n : ℕ}
  : AutoRightLimit (npow n) x₀ (x₀ ^ n) (n > 0 ∨ x₀ ≠ 0)
:= ⟨fun h_dom => Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id)⟩

private instance rightlimit_Exp
  : AutoRightLimit exp x₀ (exp x₀) True
:= ⟨directly Exp⟩

private instance rightlimit_Expow
  : AutoRightLimit (a ^ ·) x₀ (a ^ x₀) (a > 0)
:= ⟨Expow⟩

private instance rightlimit_Ln
  : AutoRightLimit ln x₀ (ln x₀) (x₀ > 0)
:= ⟨Ln⟩

private instance rightlimit_Log
  : AutoRightLimit (log a) x₀ (log a x₀) (x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨Log⟩

private instance rightlimit_Sin
  : AutoRightLimit sin x₀ (sin x₀) True
:= ⟨directly Sin⟩

private instance rightlimit_Cos
  : AutoRightLimit cos x₀ (cos x₀) True
:= ⟨directly Cos⟩

private instance rightlimit_Tan
  : AutoRightLimit tan x₀ (tan x₀) (cos x₀ ≠ 0)
:= ⟨Tan⟩

private instance rightlimit_Cot
  : AutoRightLimit cot x₀ (cot x₀) (sin x₀ ≠ 0)
:= ⟨Cot⟩

private instance rightlimit_Sec
  : AutoRightLimit sec x₀ (sec x₀) (cos x₀ ≠ 0)
:= ⟨Sec⟩

private instance rightlimit_Csc
  : AutoRightLimit csc x₀ (csc x₀) (sin x₀ ≠ 0)
:= ⟨Csc⟩

private instance rightlimit_Sinh
  : AutoRightLimit sinh x₀ (sinh x₀) True
:= ⟨directly Sinh⟩

private instance rightlimit_Cosh
  : AutoRightLimit cosh x₀ (cosh x₀) True
:= ⟨directly Cosh⟩

private instance rightlimit_Tanh
  : AutoRightLimit tanh x₀ (tanh x₀) True
:= ⟨directly Tanh⟩

private instance rightlimit_Coth
  : AutoRightLimit coth x₀ (coth x₀) (x₀ ≠ 0)
:= ⟨Coth⟩

private instance rightlimit_Sech
  : AutoRightLimit sech x₀ (sech x₀) True
:= ⟨directly Sech⟩

private instance rightlimit_Csch
  : AutoRightLimit csch x₀ (csch x₀) (x₀ ≠ 0)
:= ⟨Csch⟩

private instance rightlimit_Arcsin
  : AutoRightLimit arcsin x₀ (arcsin x₀) (x₀ ≥ -1 ∧ x₀ < 1)
:= ⟨Arcsin⟩

private instance rightlimit_Arccos
  : AutoRightLimit arccos x₀ (arccos x₀) (x₀ ≥ -1 ∧ x₀ < 1)
:= ⟨Arccos⟩

private instance rightlimit_Arctan
  : AutoRightLimit arctan x₀ (arctan x₀) True
:= ⟨directly Arctan⟩

private instance rightlimit_Arccot
  : AutoRightLimit arccot x₀ (arccot x₀) True
:= ⟨directly Arccot⟩

private instance rightlimit_Arcsec
  : AutoRightLimit arcsec x₀ (arcsec x₀) (x₀ < -1 ∨ x₀ ≥ 1)
:= ⟨Arcsec⟩

private instance rightlimit_Arccsc
  : AutoRightLimit arccsc x₀ (arccsc x₀) (x₀ < -1 ∨ x₀ ≥ 1)
:= ⟨Arccsc⟩

private instance rightlimit_compAbs
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (abs ∘ f) x₀ (|L₁|) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Abs⟩

private instance rightlimit_compAbs'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ |f x|) x₀ |L₁| c₁
:= rightlimit_compAbs

private instance rightlimit_compSqrt
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (sqrt ∘ f) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Sqrt h_dom)⟩

private instance rightlimit_compSqrt'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ √(f x)) x₀ √L₁ (c₁ ∧ L₁ > 0)
:= rightlimit_compSqrt

private instance rightlimit_compPower
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((pow a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Power h_dom)⟩

private instance rightlimit_compPower'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((· ^ a) ∘ f) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= rightlimit_compPower

private instance rightlimit_compPower''
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ f x ^ a) x₀ (L₁ ^ a) (c₁ ∧ L₁ > 0)
:= rightlimit_compPower

private instance rightlimit_compPower_ℤ {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Power_ℤ h_dom)⟩

private instance rightlimit_compPower_ℤ' {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= rightlimit_compPower_ℤ

private instance rightlimit_compPower_ℤ'' {n : ℤ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n ≥ 0 ∨ L₁ ≠ 0))
:= rightlimit_compPower_ℤ

private instance rightlimit_compPower_ℕ {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((npow n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ =>
    CompSV (h_f.eq h₁)
      (FuncLimitExpr.Power_ℤ (h_dom.imp (fun _ => Int.natCast_nonneg n) id))⟩

private instance rightlimit_compPower_ℕ' {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((· ^ n) ∘ f) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= rightlimit_compPower_ℕ

private instance rightlimit_compPower_ℕ'' {n : ℕ}
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ f x ^ n) x₀ (L₁ ^ n) (c₁ ∧ (n > 0 ∨ L₁ ≠ 0))
:= rightlimit_compPower_ℕ

private instance rightlimit_compExp
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (exp ∘ f) x₀ (exp L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Exp⟩

private instance rightlimit_compExp'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ exp (f x)) x₀ (exp L₁) c₁
:= rightlimit_compExp

private instance rightlimit_compExpow
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit ((a ^ ·) ∘ f) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Expow h_dom)⟩

private instance rightlimit_compExpow'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ a ^ (f x)) x₀ (a ^ L₁) (c₁ ∧ a > 0)
:= rightlimit_compExpow

private instance rightlimit_compLn
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (ln ∘ f) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Ln h_dom)⟩

private instance rightlimit_compLn'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ ln (f x)) x₀ (ln L₁) (c₁ ∧ L₁ > 0)
:= rightlimit_compLn

private instance rightlimit_compLog
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (log a ∘ f) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Log h_dom)⟩

private instance rightlimit_compLog'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ log a (f x)) x₀ (log a L₁) (c₁ ∧ L₁ > 0 ∧ a > 0 ∧ a ≠ 1)
:= rightlimit_compLog

private instance rightlimit_compSin
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (sin ∘ f) x₀ (sin L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sin⟩

private instance rightlimit_compSin'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ sin (f x)) x₀ (sin L₁) c₁
:= rightlimit_compSin

private instance rightlimit_compCos
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (cos ∘ f) x₀ (cos L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Cos⟩

private instance rightlimit_compCos'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ cos (f x)) x₀ (cos L₁) c₁
:= rightlimit_compCos

private instance rightlimit_compTan
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (tan ∘ f) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Tan h_dom)⟩

private instance rightlimit_compTan'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ tan (f x)) x₀ (tan L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= rightlimit_compTan

private instance rightlimit_compCot
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (cot ∘ f) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Cot h_dom)⟩

private instance rightlimit_compCot'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ cot (f x)) x₀ (cot L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= rightlimit_compCot

private instance rightlimit_compSec
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (sec ∘ f) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Sec h_dom)⟩

private instance rightlimit_compSec'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ sec (f x)) x₀ (sec L₁) (c₁ ∧ (cos L₁ ≠ 0))
:= rightlimit_compSec

private instance rightlimit_compCsc
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (csc ∘ f) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Csc h_dom)⟩

private instance rightlimit_compCsc'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ csc (f x)) x₀ (csc L₁) (c₁ ∧ (sin L₁ ≠ 0))
:= rightlimit_compCsc

private instance rightlimit_compSinh
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (sinh ∘ f) x₀ (sinh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sinh⟩

private instance rightlimit_compSinh'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ sinh (f x)) x₀ (sinh L₁) c₁
:= rightlimit_compSinh

private instance rightlimit_compCosh
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (cosh ∘ f) x₀ (cosh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Cosh⟩

private instance rightlimit_compCosh'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ cosh (f x)) x₀ (cosh L₁) c₁
:= rightlimit_compCosh

private instance rightlimit_compTanh
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (tanh ∘ f) x₀ (tanh L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Tanh⟩

private instance rightlimit_compTanh'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ tanh (f x)) x₀ (tanh L₁) c₁
:= rightlimit_compTanh

private instance rightlimit_compCoth
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (coth ∘ f) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Coth h_dom)⟩

private instance rightlimit_compCoth'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ coth (f x)) x₀ (coth L₁) (c₁ ∧ L₁ ≠ 0)
:= rightlimit_compCoth

private instance rightlimit_compSech
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (sech ∘ f) x₀ (sech L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Sech⟩

private instance rightlimit_compSech'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ sech (f x)) x₀ (sech L₁) c₁
:= rightlimit_compSech

private instance rightlimit_compCsch
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (csch ∘ f) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Csch h_dom)⟩

private instance rightlimit_compCsch'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ csch (f x)) x₀ (csch L₁) (c₁ ∧ L₁ ≠ 0)
:= rightlimit_compCsch

private instance rightlimit_compArcsin
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arcsin ∘ f) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arcsin h_dom)⟩

private instance rightlimit_compArcsin'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arcsin (f x)) x₀ (arcsin L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= rightlimit_compArcsin

private instance rightlimit_compArccos
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arccos ∘ f) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arccos h_dom)⟩

private instance rightlimit_compArccos'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arccos (f x)) x₀ (arccos L₁) (c₁ ∧ (L₁ > -1 ∧ L₁ < 1))
:= rightlimit_compArccos

private instance rightlimit_compArctan
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arctan ∘ f) x₀ (arctan L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Arctan⟩

private instance rightlimit_compArctan'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arctan (f x)) x₀ (arctan L₁) c₁
:= rightlimit_compArctan

private instance rightlimit_compArccot
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arccot ∘ f) x₀ (arccot L₁) c₁
:= ⟨fun h₁ => CompSV (h_f.eq h₁) FuncLimitExpr.Arccot⟩

private instance rightlimit_compArccot'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arccot (f x)) x₀ (arccot L₁) c₁
:= rightlimit_compArccot

private instance rightlimit_compArcsec
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arcsec ∘ f) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arcsec h_dom)⟩

private instance rightlimit_compArcsec'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arcsec (f x)) x₀ (arcsec L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= rightlimit_compArcsec

private instance rightlimit_compArccsc
    [h_f : AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (arccsc ∘ f) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= ⟨fun ⟨h₁, h_dom⟩ => CompSV (h_f.eq h₁) (FuncLimitExpr.Arccsc h_dom)⟩

private instance rightlimit_compArccsc'
    [AutoRightLimit f x₀ L₁ c₁]
  : AutoRightLimit (fun x ↦ arccsc (f x)) x₀ (arccsc L₁) (c₁ ∧ (L₁ < -1 ∨ L₁ > 1))
:= rightlimit_compArccsc

end

section
variable {f : ℝ → ℝ} {x₀ L₁ : ℝ} {cond : Prop}

lemma autoFuncLimit
    [AutoLimit f x₀ L₁ cond] (h : cond)
  : lim x₀ f = the L₁
:= finite_iff.mp <| AutoLimit.eq h

lemma autoLeftLimit
    [AutoLeftLimit f x₀ L₁ cond] (h : cond)
  : lim₋ x₀ f = the L₁
:= finite_iff.mp <| AutoLeftLimit.eq h

lemma autoRightLimit
    [AutoRightLimit f x₀ L₁ cond] (h : cond)
  : lim₊ x₀ f = the L₁
:= finite_iff.mp <| AutoRightLimit.eq h

end


/-- # Limit Calculator (Based on Continuity)

    __Usage__ `lim_cont`

    - Only used for limit expression, including
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`

    - `lim_cont` calculates limit expressions as much as possible, and then uses
      some built-in tactics to solve the remaining goals.

    - `lim_cont` requires some side-conditions to hold true in the context, which
      are the sum of the corresponding conditions for these different functions:

      - `f x ≠ 0` for `lim x` f⁻¹ and other two
      - `g x ≠ 0` for `lim x` (f / g) and other two
      - `x > 0` for `lim x` sqrt and `lim₋ x` sqrt
      - `x ≥ 0` for `lim₊ x` sqrt
      - `x > 0` for `lim x` (pow a) and `lim₋ x` (pow a)
      - `x > 0 ∨ a > 0 ∧ x = 0` for `lim₊ x` (pow a)
      - `n > 0 ∨ x ≠ 0` for `lim x` (npow n) and other two
      - `a > 0` for `lim x` (a ^ ·) and other two
      - `x > 0` for `lim x` ln and other two
      - `x > 0 ∧ a > 0 ∧ a ≠ 1` for `lim x` (log a) and other two
      - `cos x ≠ 0` for `lim x` tan and other two
      - `sin x ≠ 0` for `lim x` cot and other two
      - `cos x ≠ 0` for `lim x` sec and other two
      - `sin x ≠ 0` for `lim x` csc and other two
      - `x ≠ 0` for `lim x` coth and other two
      - `x ≠ 0` for `lim x` csch and other two
      - `x > -1 ∧ x < 1` for `lim x` arcsin
      - `x > -1 ∧ x ≤ 1` for `lim₋ x` arcsin
      - `x ≥ -1 ∧ x < 1` for `lim₊ x` arcsin
      - `x > -1 ∧ x < 1` for `lim x` arccos
      - `x > -1 ∧ x ≤ 1` for `lim₋ x` arccos
      - `x ≥ -1 ∧ x < 1` for `lim₊ x` arccos
      - `x < -1 ∨ x > 1` for `lim x` arcsec
      - `x ≤ -1 ∨ x > 1` for `lim₋ x` arcsec
      - `x < -1 ∨ x ≥ 1` for `lim₊ x` arcsec
      - `x < -1 ∨ x > 1` for `lim x` arccsc
      - `x ≤ -1 ∨ x > 1` for `lim₋ x` arccsc
      - `x < -1 ∨ x ≥ 1` for `lim₊ x` arccsc

      For composite functions, the `x`s above represents the inner functions.

    - The side-conditions should preferably be provided directly. If not, the
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
      : lim 1 fun t ↦ ln t / t) = the 0
    := by lim_cont
    example
      : lim x (fun t ↦ exp (sin t + cos t)) = the (exp (sin x + cos x))
    := by lim_cont
    example (_ : x ≠ 0)
      : lim x (fun t ↦ t⁻¹ + t) = the ((x ^ 2 + 1) / x)
    := by lim_cont
    ```
-/
macro "lim_cont" : tactic => `(tactic| (
  intros
  simp (discharger := auto_side_condition) only [
    autoFuncLimit,
    autoLeftLimit,
    autoRightLimit
  ]
  try · change the _ = the _; congr 1; auto_solver
))


page_end


section
variable {x : ℝ}

example
  : lim 1 (fun t ↦ ln t / t) = the 0
:= by lim_cont
example
  : lim x (fun t ↦ exp (sin t + cos t)) = the (exp (sin x + cos x))
:= by lim_cont
example (_ : x ≠ 0)
  : lim x (fun t ↦ t⁻¹ + t) = the ((x ^ 2 + 1) / x)
:= by lim_cont

end
