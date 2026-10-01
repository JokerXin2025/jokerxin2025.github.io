/-
    «Calculus_21».Integral.Tactics.Table
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Integral.Expr.Indefinite
import «Calculus_21».Differential.Tactics.Calc
import Calculus_21.Function.Tactics.CountableZeros
set_option linter.style.header false


/-! # Preparations -/

class AutoPrimitive (f : ℝ → ℝ)
    (f' : outParam (ℝ → ℝ)) (cond : outParam Prop) where
  eq : cond → ∫ f' =. prim f

private instance primitive_patch₁ {k : ℝ}
  : AutoPrimitive (k + ·) (fun _ ↦ 1) True where
  eq := sorry

private instance primitive_patch₁' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((k + ·) ∘ F) (fun x ↦ f x) c where
  eq := sorry

private instance primitive_patch₂ {k : ℝ}
  : AutoPrimitive (k - ·) (fun _ ↦ -1) True where
  eq := sorry

private instance primitive_patch₂' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((k - ·) ∘ F) (fun x ↦ - f x) c where
  eq := sorry

private instance primitive_patch₃ {k : ℝ}
  : AutoPrimitive (k * ·) (fun _ ↦ k) True where
  eq := sorry

private instance primitive_patch₃' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((k * ·) ∘ F) (fun x ↦ k * f x) c where
  eq := sorry

private instance primitive_patch₄ {k : ℝ}
  : AutoPrimitive (k / ·) (fun x ↦ -k / x ^ 2) True where
  eq := sorry

private instance primitive_patch₄' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((k / ·) ∘ F) (fun x ↦ -k * f x / F x ^ 2)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq h := by
    have hk : ∫ (fun _ ↦ (0 : ℝ)) =. prim (fun _ ↦ k) :=
      IndefiniteExpr.spec.mpr ⟨∅, Set.countable_empty, fun _ _ => DerivExpr.Constant⟩
    have hd := IndefiniteExpr.Div hk (AutoPrimitive.eq h.1) h.2
    simpa only [Function.comp_def, zero_mul, zero_sub, neg_mul] using hd

private instance primitive_patch₅
  : AutoPrimitive (-·) (fun _ ↦ -1) True where
  eq := sorry

private instance primitive_patch₅' {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((-·) ∘ F) (fun x ↦ - f x) c where
  eq := sorry

private instance primitive_patch₆
  : AutoPrimitive (·⁻¹) (fun x ↦ -1 / x ^ 2) True where
  eq := sorry

private instance primitive_patch₆' {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive ((·⁻¹) ∘ F) (fun x ↦ - f x / F x ^ 2)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq h := IndefiniteExpr.Inv (AutoPrimitive.eq h.1) h.2

private instance primitive_Constant {C : ℝ}
  : AutoPrimitive (const C) (fun _ ↦ 0) True := sorry

private instance primitive_Constant' {C : ℝ}
  : AutoPrimitive (fun _ ↦ C) (fun _ ↦ 0) True
:= ⟨primitive_Constant.eq⟩

private instance primitive_Identity
  : AutoPrimitive id (fun _ ↦ 1) True := sorry

private instance primitive_Identity'
  : AutoPrimitive (·) (fun _ ↦ 1) True
:= ⟨primitive_Identity.eq⟩

private instance primitive_SMul {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ k * F x) (fun x ↦ k * f x) c where
  eq := sorry

private instance primitive_SMul' {f F : ℝ → ℝ} {k : ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (k • F) (fun x ↦ k * f x) c := primitive_SMul

private instance primitive_Neg {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ - F x) (fun x ↦ - f x) c where
  eq := sorry

private instance primitive_Neg' {f F : ℝ → ℝ} {c : Prop} [AutoPrimitive F f c]
  : AutoPrimitive (-F) (fun x ↦ -f x) c := primitive_Neg

private instance primitive_Inv {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ (F x)⁻¹) (fun x ↦ - f x / F x ^ 2)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq h := IndefiniteExpr.Inv (AutoPrimitive.eq h.1) h.2

private instance primitive_Inv' {f F : ℝ → ℝ} {c : Prop} [AutoPrimitive F f c]
  : AutoPrimitive F⁻¹ (fun x ↦ -f x / F x ^ 2)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_Inv

private instance primitive_Add {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (fun x ↦ F x + G x) (fun x ↦ f x + g x) (c₁ ∧ c₂) where
  eq := sorry

private instance primitive_Add' {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (F + G) (fun x ↦ f x + g x) (c₁ ∧ c₂) := primitive_Add

private instance primitive_Sub {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (fun x ↦ F x - G x) (fun x ↦ f x - g x) (c₁ ∧ c₂) where
  eq := sorry

private instance primitive_Sub' {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (F - G) (fun x ↦ f x - g x) (c₁ ∧ c₂) := primitive_Sub

private instance primitive_Mul {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (fun x ↦ F x * G x) (fun x ↦ f x * G x + F x * g x) (c₁ ∧ c₂) where
  eq := sorry

private instance primitive_Mul' {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (F * G) (fun x ↦ f x * G x + F x * g x) (c₁ ∧ c₂) := primitive_Mul

private instance primitive_Div {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (fun x ↦ F x / G x)
    (fun x ↦ (f x * G x - F x * g x) / G x ^ 2)
    (c₁ ∧ c₂ ∧ IndefiniteExpr.CountableZeros G) where
  eq h := IndefiniteExpr.Div (AutoPrimitive.eq h.1) (AutoPrimitive.eq h.2.1) h.2.2

private instance primitive_Div' {f g F G : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoPrimitive F f c₁] [AutoPrimitive G g c₂]
  : AutoPrimitive (F / G) (fun x ↦ (f x * G x - F x * g x) / G x ^ 2)
      (c₁ ∧ c₂ ∧ IndefiniteExpr.CountableZeros G) := primitive_Div

private instance primitive_Abs
  : AutoPrimitive (|·|) (fun x ↦ x / |x|) True where
  eq := sorry

private instance primitive_Sqrt
  : AutoPrimitive (√·) (fun x ↦ 1 / (2 * √x)) True where
  eq := sorry

private instance primitive_Power {a : ℝ}
  : AutoPrimitive (pow a) (fun x ↦ a * x ^ (a - 1)) True
:= sorry

private instance primitive_Power_ℤ {n : ℤ}
  : AutoPrimitive (npow n) (fun x ↦ n * x ^ (n - 1)) True
:= sorry

private instance primitive_Power_ℕ {n : ℕ}
  : AutoPrimitive (npow n) (fun x ↦ (n : ℝ) * x ^ ((n : ℤ) - 1)) True
:= sorry

private instance primitive_Exp
  : AutoPrimitive exp (fun x ↦ exp x) True where
  eq := sorry

private instance primitive_Expow {a : ℝ}
  : AutoPrimitive (a ^ ·) (fun x ↦ ln a * a ^ x) (a > 0) where
  eq := sorry

private instance primitive_Ln
  : AutoPrimitive ln (fun x ↦ x⁻¹) True where
  eq := sorry

private instance primitive_LnAbs
  : AutoPrimitive (ln |·|) (fun x ↦ x⁻¹) True where
  eq := sorry

private instance primitive_Log {a : ℝ}
  : AutoPrimitive (log a) (fun x ↦ (ln a * x)⁻¹) (a > 0 ∧ a ≠ 1) where
  eq := sorry

private instance primitive_LogAbs {a : ℝ}
  : AutoPrimitive (log a |·|) (fun x ↦ (ln a * x)⁻¹) (a > 0 ∧ a ≠ 1) where
  eq := sorry

private instance primitive_Sin
  : AutoPrimitive sin (fun x ↦ cos x) True where
  eq := sorry

private instance primitive_Cos
  : AutoPrimitive cos (fun x ↦ - sin x) True where
  eq := sorry

private instance primitive_Tan
  : AutoPrimitive tan (fun x ↦ sec x ^ 2) True where
  eq := sorry

private instance primitive_Cot
  : AutoPrimitive cot (fun x ↦ - csc x ^ 2) True where
  eq := sorry

private instance primitive_Sec
  : AutoPrimitive sec (fun x ↦ tan x * sec x) True where
  eq := sorry

private instance primitive_Csc
  : AutoPrimitive csc (fun x ↦ - cot x * csc x) True where
  eq := sorry

private instance primitive_Sinh
  : AutoPrimitive sinh (fun x ↦ cosh x) True where
  eq := sorry

private instance primitive_Cosh
  : AutoPrimitive cosh (fun x ↦ sinh x) True where
  eq := sorry

private instance primitive_Tanh
  : AutoPrimitive tanh (fun x ↦ sech x ^ 2) True where
  eq := sorry

private instance primitive_Coth
  : AutoPrimitive coth (fun x ↦ - csch x ^ 2) True where
  eq := sorry

private instance primitive_Sech
  : AutoPrimitive sech (fun x ↦ - tanh x * sech x) True where
  eq := sorry

private instance primitive_Csch
  : AutoPrimitive csch (fun x ↦ - coth x * csch x) True where
  eq := sorry

private instance primitive_Arcsin
  : AutoPrimitive arcsin (fun x ↦ 1 / √(1 - x ^ 2)) True where
  eq := sorry

private instance primitive_Arccos
  : AutoPrimitive arccos (fun x ↦ -1 / √(1 - x ^ 2)) True where
  eq := sorry

private instance primitive_Arctan
  : AutoPrimitive arctan (fun x ↦ (1 + x ^ 2)⁻¹) True where
  eq := sorry

private instance primitive_Arccot
  : AutoPrimitive arccot (fun x ↦ -1 / (1 + x ^ 2)) True where
  eq := sorry

private instance primitive_Arcsec
  : AutoPrimitive arcsec (fun x ↦ 1 / (|x| * √(x ^ 2 - 1))) True where
  eq := sorry

private instance primitive_Arccsc
  : AutoPrimitive arccsc (fun x ↦ -1 / (|x| * √(x ^ 2 - 1))) True where
  eq := sorry

/-! Composite instances fix the outer function so that instance search can
recognize both explicit compositions and lambda expressions. Conditions concern
exceptional points in the inner variable, not just the outer function's poles. -/

section
variable {f F : ℝ → ℝ} {c : Prop}

private instance primitive_compAbs [AutoPrimitive F f c]
  : AutoPrimitive (abs ∘ F) (fun x ↦ F x / |F x| * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compAbs' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ |F x|) (fun x ↦ F x / |F x| * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compAbs

private instance primitive_compSqrt [AutoPrimitive F f c]
  : AutoPrimitive (sqrt ∘ F) (fun x ↦ 1 / (2 * √(F x)) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compSqrt' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ √(F x)) (fun x ↦ 1 / (2 * √(F x)) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compSqrt

private instance primitive_compPower {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive ((· ^ a) ∘ F) (fun x ↦ a * F x ^ (a - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compPower' {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ F x ^ a) (fun x ↦ a * F x ^ (a - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compPower

private instance primitive_compPower_ℤ {n : ℤ} [AutoPrimitive F f c]
  : AutoPrimitive ((· ^ n) ∘ F) (fun x ↦ n * F x ^ (n - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compPower_ℤ' {n : ℤ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ F x ^ n) (fun x ↦ n * F x ^ (n - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compPower_ℤ

private instance primitive_compPower_ℕ {n : ℕ} [AutoPrimitive F f c]
  : AutoPrimitive ((· ^ n) ∘ F) (fun x ↦ n * F x ^ (n - 1) * f x) c where
  eq := sorry

private instance primitive_compPower_ℕ' {n : ℕ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ F x ^ n) (fun x ↦ n * F x ^ (n - 1) * f x) c :=
  primitive_compPower_ℕ

private instance primitive_compExp [AutoPrimitive F f c]
  : AutoPrimitive (exp ∘ F) (fun x ↦ exp (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Exp))

private instance primitive_compExp' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ exp (F x)) (fun x ↦ exp (F x) * f x) c := primitive_compExp

private instance primitive_compExpow {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive ((a ^ ·) ∘ F) (fun x ↦ ln a * a ^ F x * f x) (c ∧ a > 0) where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ ln a * a ^ y) (AutoPrimitive.eq h.1)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Expow h.2))

private instance primitive_compExpow' {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ a ^ F x) (fun x ↦ ln a * a ^ F x * f x) (c ∧ a > 0) :=
  primitive_compExpow

private instance primitive_compLn [AutoPrimitive F f c]
  : AutoPrimitive (ln ∘ F) (fun x ↦ (F x)⁻¹ * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compLn' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ ln (F x)) (fun x ↦ (F x)⁻¹ * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compLn

private instance primitive_compLnAbs [AutoPrimitive F f c]
  : AutoPrimitive ((ln |·|) ∘ F) (fun x ↦ (F x)⁻¹ * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compLnAbs' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ ln |F x|) (fun x ↦ (F x)⁻¹ * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compLnAbs

private instance primitive_compLog {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive (log a ∘ F) (fun x ↦ (ln a * F x)⁻¹ * f x)
      (c ∧ a > 0 ∧ a ≠ 1 ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compLog' {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ log a (F x)) (fun x ↦ (ln a * F x)⁻¹ * f x)
      (c ∧ a > 0 ∧ a ≠ 1 ∧ IndefiniteExpr.CountableZeros F) := primitive_compLog

private instance primitive_compLogAbs {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive ((log a |·|) ∘ F) (fun x ↦ (ln a * F x)⁻¹ * f x)
      (c ∧ a > 0 ∧ a ≠ 1 ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compLogAbs' {a : ℝ} [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ log a |F x|) (fun x ↦ (ln a * F x)⁻¹ * f x)
      (c ∧ a > 0 ∧ a ≠ 1 ∧ IndefiniteExpr.CountableZeros F) := primitive_compLogAbs

private instance primitive_compSin [AutoPrimitive F f c]
  : AutoPrimitive (sin ∘ F) (fun x ↦ cos (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Sin))

private instance primitive_compSin' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ sin (F x)) (fun x ↦ cos (F x) * f x) c := primitive_compSin

private instance primitive_compCos [AutoPrimitive F f c]
  : AutoPrimitive (cos ∘ F) (fun x ↦ -sin (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ -sin y) (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Cos))

private instance primitive_compCos' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ cos (F x)) (fun x ↦ -sin (F x) * f x) c := primitive_compCos

private instance primitive_compTan [AutoPrimitive F f c]
  : AutoPrimitive (tan ∘ F) (fun x ↦ sec (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros (cos ∘ F)) where
  eq := sorry

private instance primitive_compTan' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ tan (F x)) (fun x ↦ sec (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros (cos ∘ F)) := primitive_compTan

private instance primitive_compCot [AutoPrimitive F f c]
  : AutoPrimitive (cot ∘ F) (fun x ↦ -csc (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros (sin ∘ F)) where
  eq := sorry

private instance primitive_compCot' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ cot (F x)) (fun x ↦ -csc (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros (sin ∘ F)) := primitive_compCot

private instance primitive_compSec [AutoPrimitive F f c]
  : AutoPrimitive (sec ∘ F) (fun x ↦ tan (F x) * sec (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros (cos ∘ F)) where
  eq := sorry

private instance primitive_compSec' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ sec (F x)) (fun x ↦ tan (F x) * sec (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros (cos ∘ F)) := primitive_compSec

private instance primitive_compCsc [AutoPrimitive F f c]
  : AutoPrimitive (csc ∘ F) (fun x ↦ -cot (F x) * csc (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros (sin ∘ F)) where
  eq := sorry

private instance primitive_compCsc' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ csc (F x)) (fun x ↦ -cot (F x) * csc (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros (sin ∘ F)) := primitive_compCsc

private instance primitive_compSinh [AutoPrimitive F f c]
  : AutoPrimitive (sinh ∘ F) (fun x ↦ cosh (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Sinh))

private instance primitive_compSinh' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ sinh (F x)) (fun x ↦ cosh (F x) * f x) c := primitive_compSinh

private instance primitive_compCosh [AutoPrimitive F f c]
  : AutoPrimitive (cosh ∘ F) (fun x ↦ sinh (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Cosh))

private instance primitive_compCosh' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ cosh (F x)) (fun x ↦ sinh (F x) * f x) c := primitive_compCosh

private instance primitive_compTanh [AutoPrimitive F f c]
  : AutoPrimitive (tanh ∘ F) (fun x ↦ sech (F x) ^ 2 * f x) c where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ sech y ^ 2) (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Tanh))

private instance primitive_compTanh' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ tanh (F x)) (fun x ↦ sech (F x) ^ 2 * f x) c := primitive_compTanh

private instance primitive_compCoth [AutoPrimitive F f c]
  : AutoPrimitive (coth ∘ F) (fun x ↦ -csch (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compCoth' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ coth (F x)) (fun x ↦ -csch (F x) ^ 2 * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compCoth

private instance primitive_compSech [AutoPrimitive F f c]
  : AutoPrimitive (sech ∘ F) (fun x ↦ -tanh (F x) * sech (F x) * f x) c where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ -tanh y * sech y) (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Sech))

private instance primitive_compSech' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ sech (F x)) (fun x ↦ -tanh (F x) * sech (F x) * f x) c :=
  primitive_compSech

private instance primitive_compCsch [AutoPrimitive F f c]
  : AutoPrimitive (csch ∘ F) (fun x ↦ -coth (F x) * csch (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) where
  eq := sorry

private instance primitive_compCsch' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ csch (F x)) (fun x ↦ -coth (F x) * csch (F x) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compCsch

private instance primitive_compArcsin [AutoPrimitive F f c]
  : AutoPrimitive (arcsin ∘ F) (fun x ↦ 1 / √(1 - F x ^ 2) * f x)
      (c ∧ {x | F x = -1 ∨ F x = 1}.Countable) where
  eq := sorry

private instance primitive_compArcsin' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arcsin (F x)) (fun x ↦ 1 / √(1 - F x ^ 2) * f x)
      (c ∧ {x | F x = -1 ∨ F x = 1}.Countable) := primitive_compArcsin

private instance primitive_compArccos [AutoPrimitive F f c]
  : AutoPrimitive (arccos ∘ F) (fun x ↦ -1 / √(1 - F x ^ 2) * f x)
      (c ∧ {x | F x = -1 ∨ F x = 1}.Countable) where
  eq := sorry

private instance primitive_compArccos' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arccos (F x)) (fun x ↦ -1 / √(1 - F x ^ 2) * f x)
      (c ∧ {x | F x = -1 ∨ F x = 1}.Countable) := primitive_compArccos

private instance primitive_compArctan [AutoPrimitive F f c]
  : AutoPrimitive (arctan ∘ F) (fun x ↦ (1 + F x ^ 2)⁻¹ * f x) c where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ (1 + y ^ 2)⁻¹) (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Arctan))

private instance primitive_compArctan' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arctan (F x)) (fun x ↦ (1 + F x ^ 2)⁻¹ * f x) c :=
  primitive_compArctan

private instance primitive_compArccot [AutoPrimitive F f c]
  : AutoPrimitive (arccot ∘ F) (fun x ↦ -1 / (1 + F x ^ 2) * f x) c where
  eq h := IndefiniteExpr.Comp (f := fun y ↦ -1 / (1 + y ^ 2)) (AutoPrimitive.eq h)
    (IndefiniteExpr.countableDerivativePreimage_of_deriv (fun _ => DerivExpr.Arccot))

private instance primitive_compArccot' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arccot (F x)) (fun x ↦ -1 / (1 + F x ^ 2) * f x) c :=
  primitive_compArccot

private instance primitive_compArcsec [AutoPrimitive F f c]
  : AutoPrimitive (arcsec ∘ F) (fun x ↦ 1 / (|F x| * √(F x ^ 2 - 1)) * f x)
      (c ∧ {x | F x = 0 ∨ F x = -1 ∨ F x = 1}.Countable) where
  eq := sorry

private instance primitive_compArcsec' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arcsec (F x)) (fun x ↦ 1 / (|F x| * √(F x ^ 2 - 1)) * f x)
      (c ∧ {x | F x = 0 ∨ F x = -1 ∨ F x = 1}.Countable) := primitive_compArcsec

private instance primitive_compArccsc [AutoPrimitive F f c]
  : AutoPrimitive (arccsc ∘ F) (fun x ↦ -1 / (|F x| * √(F x ^ 2 - 1)) * f x)
      (c ∧ {x | F x = 0 ∨ F x = -1 ∨ F x = 1}.Countable) where
  eq := sorry

private instance primitive_compArccsc' [AutoPrimitive F f c]
  : AutoPrimitive (fun x ↦ arccsc (F x)) (fun x ↦ -1 / (|F x| * √(F x ^ 2 - 1)) * f x)
      (c ∧ {x | F x = 0 ∨ F x = -1 ∨ F x = 1}.Countable) := primitive_compArccsc

end

private instance primitive_compPower_named {a : ℝ} {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (pow a ∘ F) (fun x ↦ a * F x ^ (a - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compPower

private instance primitive_compPower_named_ℤ {n : ℤ} {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (npow n ∘ F) (fun x ↦ n * F x ^ (n - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compPower_ℤ

private instance primitive_compPower_named_ℕ {n : ℕ} {f F : ℝ → ℝ} {c : Prop}
    [AutoPrimitive F f c]
  : AutoPrimitive (npow n ∘ F) (fun x ↦ (n : ℝ) * F x ^ ((n : ℤ) - 1) * f x)
      (c ∧ IndefiniteExpr.CountableZeros F) := primitive_compPower_ℤ

/-- Transport a synthesized primitive across equality outside a countable set.
The exceptional set belongs to the integrand comparison and is independent of
the derivative's own exceptional set. -/
lemma autoPrimitive {f g F : ℝ → ℝ} {cond : Prop}
    [AutoPrimitive F f cond]
    (h_eq : ∃ s : Set ℝ, s.Countable ∧ ∀ x ∉ s, f x = g x) (h_cond : cond)
  : ∫ g =. prim F
:= by
  obtain ⟨s, hs, hfg⟩ := h_eq
  exact IndefiniteExpr.CongrOutside hs (fun x hx => (hfg x hx).symm) (AutoPrimitive.eq h_cond)


/-! # Tactics -/

macro "int_table" : tactic => `(tactic|
  focus
    intros
    apply autoPrimitive
    case' h_eq =>
      refine ⟨∅, Set.countable_empty, ?_⟩
      try
        intro x _
        push_cast
        auto_solver
    case' h_cond =>
      repeat any_goals apply And.intro
      all_goals try trivial
      all_goals try countable_zeros
)

macro "int_table" "except" excepts:term : tactic => `(tactic|
  focus
    intros
    apply autoPrimitive
    case' h_eq =>
      refine ⟨$excepts, ?countability, ?equal⟩
      case' countability =>
        first
        | apply Set.countable_empty
        | apply Set.countable_singleton
        | skip
      case' equal =>
        intro x hx
        try have hx' : x ≠ _ := by simpa only [Set.mem_singleton_iff] using hx
        push_cast
        auto_solver
    case' h_cond =>
      repeat any_goals apply And.intro
      all_goals try trivial
      all_goals try countable_zeros
)


page_end
