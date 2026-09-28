/-
    «Calculus_21».Differential.Tactics.Calc
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Elementary
import «Calculus_21».Differential.Tactics.Rules
set_option linter.style.header false

open LimitValue (finite_iff finite_div)


class AutoDeriv (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → D f x₀ =. the val

open DerivExpr in section
variable {C k a x₀ D₁ D₂ : ℝ} {f g : ℝ → ℝ} {c₁ c₂ : Prop}

private instance deriv_patch₁
  : AutoDeriv (k + ·) x₀ 1 True
:= by
  constructor
  intro _
  calc
    _  =. D (const k) x₀ + D id x₀
          := by deriv_add
    _  =  the 0 + the 1
          := by poly_rw [Constant, Identity]
    _  =  the 1
          := by norm_num

private instance deriv_patch₁'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((k + ·) ∘ f) x₀ D₁ c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D (k + ·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the 1 * the D₁
          := by poly_rw [deriv_patch₁.eq trivial, h_f.eq h₁]
    _  =  the D₁
          := by norm_num

private instance deriv_patch₂
  : AutoDeriv (k - ·) x₀ (-1) True
:= by
  constructor
  intro _
  calc
    _  =. D (const k) x₀ - D id x₀
          := by deriv_sub
    _  =  the 0 - the 1
          := by poly_rw [Constant, Identity]
    _  =  the (-1)
          := by norm_num

private instance deriv_patch₂'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((k - ·) ∘ f) x₀ (-D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D (k - ·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1) * the D₁
          := by poly_rw [deriv_patch₂.eq trivial, h_f.eq h₁]
    _  =  the (-D₁)
          := by norm_num

private instance deriv_patch₃
  : AutoDeriv (k * ·) x₀ k True
:= by
  constructor
  intro _
  script_given_proper
  calc
    _  =? D (const k) x₀ * the x₀ + D id x₀ * the k
          := by deriv_mul
    _  =  the 0 * the x₀ + the 1 * the k
          := by poly_rw [Constant, Identity]
    _  =  the k
          := by norm_num

private instance deriv_patch₃'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((k * ·) ∘ f) x₀ (k * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D (k * ·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the k * the D₁
          := by poly_rw [deriv_patch₃.eq trivial, h_f.eq h₁]
    _  =  the (k * D₁)
          := rfl

private instance deriv_patch₄
  : AutoDeriv (k / ·) x₀ (-k / x₀ ^ 2) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  have h_den : x₀ ^ 2 ≠ 0 := by positivity
  script_given_proper
  calc
    _  =? (D (const k) x₀ * the x₀ - D id x₀ * the k) / the (x₀ ^ 2)
          := by deriv_div
    _  =  (the 0 * the x₀ - the 1 * the k) / the (x₀ ^ 2)
          := by poly_rw [Constant, Identity]
    _  =  the (0 * x₀ - 1 * k) / the (x₀ ^ 2)
          := rfl
    _  =  the ((0 * x₀ - 1 * k) / x₀ ^ 2)
          := by poly_rw [finite_div h_den]
    _  =  the (-k / x₀ ^ 2)
          := by ring_nf

private instance deriv_patch₄'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((k / ·) ∘ f) x₀ (-k * D₁ / f x₀ ^ 2) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (k / ·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-k / f x₀ ^ 2) * the D₁
          := by poly_rw [deriv_patch₄.eq h_dom, h_f.eq h₁]
    _  =  the (-k * D₁ / f x₀ ^ 2)
          := by
            change the ((-k / f x₀ ^ 2) * D₁) = the (-k * D₁ / f x₀ ^ 2)
            ring_nf

private instance deriv_patch₅
  : AutoDeriv (-·) x₀ (-1) True
:= by
  constructor
  intro _
  calc
    _  =. - D id x₀
          := by deriv_neg
    _  =  - the 1
          := by poly_rw [Identity]
    _  =  the (-1)
          := rfl

private instance deriv_patch₅'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((-·) ∘ f) x₀ (-D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D (-·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1) * the D₁
          := by poly_rw [deriv_patch₅.eq trivial, h_f.eq h₁]
    _  =  the (-D₁)
          := by norm_num

private instance deriv_patch₆
  : AutoDeriv (·⁻¹) x₀ (-1 / x₀ ^ 2) (x₀ ≠ 0)
:= by
  constructor
  intro h_dom
  have h_den : x₀ ^ 2 ≠ 0 := by positivity
  script_given_proper
  calc
    _  =? - D id x₀ / the (x₀ ^ 2)
          := by deriv_inv
    _  =  - the 1 / the (x₀ ^ 2)
          := by poly_rw [Identity]
    _  =  the (-1) / the (x₀ ^ 2)
          := rfl
    _  =  the (-1 / x₀ ^ 2)
          := by poly_rw [finite_div h_den]

private instance deriv_patch₆'
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((·⁻¹) ∘ f) x₀ (-D₁ / f x₀ ^ 2) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  have h_den : f x₀ ^ 2 ≠ 0 := by positivity
  script_given_proper
  calc
    _  =? D (·⁻¹) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1 / f x₀ ^ 2) * the D₁
          := by poly_rw [deriv_patch₆.eq h_dom, h_f.eq h₁]
    _  =  the (-D₁ / f x₀ ^ 2)
          := by
            change the ((-1 / f x₀ ^ 2) * D₁) = the (-D₁ / f x₀ ^ 2)
            ring_nf

private instance deriv_Constant
  : AutoDeriv (const C) x₀ 0 True
:= ⟨directly Constant⟩

private instance deriv_Constant'
  : AutoDeriv (fun _ ↦ C) x₀ 0 True
:= deriv_Constant

private instance deriv_Identity
  : AutoDeriv id x₀ 1 True
:= ⟨directly Identity⟩

private instance deriv_Identity'
  : AutoDeriv (·) x₀ 1 True
:= deriv_Identity

private instance deriv_SMul
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (k • f) x₀ (k * D₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. the k * D f x₀
          := by deriv_smul
    _  =  the k * the D₁
          := by poly_rw [AutoDeriv.eq h₁]
    _  =  the (k * D₁)
          := rfl

private instance deriv_Neg
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (-f) x₀ (-D₁) c₁
:= by
  constructor
  intro h₁
  calc
    _  =. - D f x₀
          := by deriv_neg
    _  =  - the D₁
          := by poly_rw [AutoDeriv.eq h₁]
    _  =  the (-D₁)
          := rfl

private instance deriv_Neg'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ - f x) x₀ (-D₁) c₁
:= deriv_Neg

private instance deriv_Inv
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv f⁻¹ x₀ (-D₁ / f x₀ ^ 2) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  have h_den : f x₀ ^ 2 ≠ 0 := by positivity
  script_given_proper
  calc
    _  =? (- D f x₀) / the (f x₀ ^ 2)
          := by deriv_inv
    _  =  - the D₁ / the (f x₀ ^ 2)
          := by poly_rw [AutoDeriv.eq h₁]
    _  =  the (-D₁) / the (f x₀ ^ 2)
          := rfl
    _  =  the (-D₁ / f x₀ ^ 2)
          := by poly_rw [finite_div h_den]

private instance deriv_Inv'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ (f x)⁻¹) x₀ (-D₁ / f x₀ ^ 2) (c₁ ∧ f x₀ ≠ 0)
:= deriv_Inv

private instance deriv_Add
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f + g) x₀ (D₁ + D₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. D f x₀ + D g x₀
          := by deriv_add
    _  =  the D₁ + the D₂
          := by poly_rw [AutoDeriv.eq h₁, AutoDeriv.eq h₂]
    _  =  the (D₁ + D₂)
          := rfl

private instance deriv_Add'
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x + g x) x₀ (D₁ + D₂) (c₁ ∧ c₂)
:= deriv_Add

private instance deriv_Sub
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f - g) x₀ (D₁ - D₂) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  calc
    _  =. D f x₀ - D g x₀
          := by deriv_sub
    _  =  the D₁ - the D₂
          := by poly_rw [AutoDeriv.eq h₁, AutoDeriv.eq h₂]
    _  =  the (D₁ - D₂)
          := rfl

private instance deriv_Sub'
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x - g x) x₀ (D₁ - D₂) (c₁ ∧ c₂)
:= deriv_Sub

private instance deriv_Mul
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f * g) x₀ (D₁ * g x₀ + D₂ * f x₀) (c₁ ∧ c₂)
:= by
  constructor
  intro ⟨h₁, h₂⟩
  script_given_proper
  calc
    _  =? D f x₀ * the (g x₀) + D g x₀ * the (f x₀)
          := by deriv_mul
    _  =  the D₁ * the (g x₀) + the D₂ * the (f x₀)
          := by poly_rw [AutoDeriv.eq h₁, AutoDeriv.eq h₂]
    _  =  the (D₁ * g x₀ + D₂ * f x₀)
          := rfl

private instance deriv_Mul'
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x * g x) x₀ (D₁ * g x₀ + D₂ * f x₀) (c₁ ∧ c₂)
:= deriv_Mul

private instance deriv_Div
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f / g) x₀ ((D₁ * g x₀ - D₂ * f x₀) / g x₀ ^ 2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h₂, h_dom⟩
  have h_den : g x₀ ^ 2 ≠ 0 := by positivity
  script_given_proper
  calc
    _  =? (D f x₀ * the (g x₀) - D g x₀ * the (f x₀)) / the (g x₀ ^ 2)
          := by deriv_div
    _  =  (the D₁ * the (g x₀) - the D₂ * the (f x₀)) / the (g x₀ ^ 2)
          := by poly_rw [AutoDeriv.eq h₁, AutoDeriv.eq h₂]
    _  =  the (D₁ * g x₀ - D₂ * f x₀) / the (g x₀ ^ 2)
          := rfl
    _  =  the ((D₁ * g x₀ - D₂ * f x₀) / g x₀ ^ 2)
          := by poly_rw [finite_div h_den]

private instance deriv_Div'
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x / g x) x₀
      ((D₁ * g x₀ - D₂ * f x₀) / g x₀ ^ 2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0)
:= deriv_Div

private instance deriv_Abs
  : AutoDeriv abs x₀ (x₀ / |x₀|) (x₀ ≠ 0)
:= ⟨Abs⟩

private instance deriv_Sqrt
  : AutoDeriv sqrt x₀ (1 / (2 * √x₀)) (x₀ > 0)
:= ⟨Sqrt⟩

private instance deriv_Power
  : AutoDeriv (pow a) x₀ (a * x₀ ^ (a - 1)) (x₀ > 0)
:= ⟨Power⟩

private instance deriv_Power_ℤ {n : ℤ}
  : AutoDeriv (npow n) x₀ (n * x₀ ^ (n - 1)) (n > 0 ∨ x₀ ≠ 0)
:= ⟨Power_ℤ⟩

private instance deriv_Power_ℕ {n : ℕ}
  : AutoDeriv (npow n) x₀ (n * x₀ ^ ((n - 1) : ℤ)) (n > 0 ∨ x₀ ≠ 0)
:= ⟨fun h_dom => Power_ℤ (h_dom.imp Nat.cast_pos.mpr id)⟩

private instance deriv_Exp
  : AutoDeriv exp x₀ (exp x₀) True
:= ⟨directly Exp⟩

private instance deriv_Expow
  : AutoDeriv (a ^ ·) x₀ (ln a * a ^ x₀) (a > 0)
:= ⟨Expow⟩

private instance deriv_Ln
  : AutoDeriv ln x₀ x₀⁻¹ (x₀ > 0)
:= ⟨Ln⟩

private instance deriv_Log
  : AutoDeriv (log a) x₀ (ln a * x₀)⁻¹ (x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= ⟨Log⟩

private instance deriv_Sin
  : AutoDeriv sin x₀ (cos x₀) True
:= ⟨directly Sin⟩

private instance deriv_Cos
  : AutoDeriv cos x₀ (- sin x₀) True
:= ⟨directly Cos⟩

private instance deriv_Tan
  : AutoDeriv tan x₀ (sec x₀ ^ 2) (cos x₀ ≠ 0)
:= ⟨Tan⟩

private instance deriv_Cot
  : AutoDeriv cot x₀ (- csc x₀ ^ 2) (sin x₀ ≠ 0)
:= ⟨Cot⟩

private instance deriv_Sec
  : AutoDeriv sec x₀ (tan x₀ * sec x₀) (cos x₀ ≠ 0)
:= ⟨Sec⟩

private instance deriv_Csc
  : AutoDeriv csc x₀ (- cot x₀ * csc x₀) (sin x₀ ≠ 0)
:= ⟨Csc⟩

private instance deriv_Sinh
  : AutoDeriv sinh x₀ (cosh x₀) True
:= ⟨directly Sinh⟩

private instance deriv_Cosh
  : AutoDeriv cosh x₀ (sinh x₀) True
:= ⟨directly Cosh⟩

private instance deriv_Tanh
  : AutoDeriv tanh x₀ (sech x₀ ^ 2) True
:= ⟨directly Tanh⟩

private instance deriv_Coth
  : AutoDeriv coth x₀ (- csch x₀ ^ 2) (x₀ ≠ 0)
:= ⟨Coth⟩

private instance deriv_Sech
  : AutoDeriv sech x₀ (- tanh x₀ * sech x₀) True
:= ⟨directly Sech⟩

private instance deriv_Csch
  : AutoDeriv csch x₀ (- coth x₀ * csch x₀) (x₀ ≠ 0)
:= ⟨Csch⟩

private instance deriv_Arcsin
  : AutoDeriv arcsin x₀ (1 / √(1 - x₀ ^ 2)) (x₀ > -1 ∧ x₀ < 1)
:= ⟨Arcsin⟩

private instance deriv_Arccos
  : AutoDeriv arccos x₀ (-1 / √(1 - x₀ ^ 2)) (x₀ > -1 ∧ x₀ < 1)
:= ⟨Arccos⟩

private instance deriv_Arctan
  : AutoDeriv arctan x₀ (1 / (1 + x₀ ^ 2)) True
:= ⟨directly Arctan⟩

private instance deriv_Arccot
  : AutoDeriv arccot x₀ (-1 / (1 + x₀ ^ 2)) True
:= ⟨directly Arccot⟩

private instance deriv_Arcsec
  : AutoDeriv arcsec x₀ (1 / (|x₀| * √(x₀ ^ 2 - 1))) (x₀ < -1 ∨ x₀ > 1)
:= ⟨Arcsec⟩

private instance deriv_Arccsc
  : AutoDeriv arccsc x₀ (-1 / (|x₀| * √(x₀ ^ 2 - 1))) (x₀ < -1 ∨ x₀ > 1)
:= ⟨Arccsc⟩

private instance deriv_compAbs
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (abs ∘ f) x₀ (f x₀ / |f x₀| * D₁) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D abs (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (f x₀ / |f x₀| * D₁)
          := by poly_rw [Abs h_dom, h_f.eq h₁]

private instance deriv_compAbs'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ |f x|) x₀ (f x₀ / |f x₀| * D₁) (c₁ ∧ f x₀ ≠ 0)
:= deriv_compAbs

private instance deriv_compSqrt
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sqrt ∘ f) x₀ (1 / (2 * √(f x₀)) * D₁) (c₁ ∧ f x₀ > 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D sqrt (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (1 / (2 * √(f x₀)) * D₁)
          := by poly_rw [Sqrt h_dom, h_f.eq h₁]

private instance deriv_compSqrt'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ √(f x)) x₀ (1 / (2 * √(f x₀)) * D₁) (c₁ ∧ f x₀ > 0)
:= deriv_compSqrt

private instance deriv_compPower
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((pow a) ∘ f) x₀ (a * f x₀ ^ (a - 1) * D₁) (c₁ ∧ f x₀ > 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (pow a) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (a * f x₀ ^ (a - 1) * D₁)
          := by poly_rw [Power h_dom, h_f.eq h₁]

private instance deriv_compPower'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ f x ^ a) x₀ (a * f x₀ ^ (a - 1) * D₁) (c₁ ∧ f x₀ > 0)
:= deriv_compPower

private instance deriv_compPower_ℤ {n : ℤ}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((npow n) ∘ f) x₀
      (n * f x₀ ^ (n - 1) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (npow n) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (n * f x₀ ^ (n - 1) * D₁)
          := by poly_rw [Power_ℤ h_dom, h_f.eq h₁]

private instance deriv_compPower_ℤ' {n : ℤ}
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((· ^ n) ∘ f) x₀ (n * f x₀ ^ (n - 1) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= deriv_compPower_ℤ

private instance deriv_compPower_ℤ'' {n : ℤ}
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ f x ^ n) x₀
      (n * f x₀ ^ (n - 1) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= deriv_compPower_ℤ

private instance deriv_compPower_ℕ {n : ℕ}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((npow n) ∘ f) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (npow n) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (n * f x₀ ^ ((n - 1) : ℤ) * D₁)
          := by poly_rw [Power_ℤ (h_dom.imp Nat.cast_pos.mpr id), h_f.eq h₁]

private instance deriv_compPower_ℕ' {n : ℕ}
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((· ^ n) ∘ f) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= deriv_compPower_ℕ

private instance deriv_compPower_ℕ'' {n : ℕ}
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ f x ^ n) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c₁ ∧ (n > 0 ∨ f x₀ ≠ 0))
:= deriv_compPower_ℕ

private instance deriv_compExp
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (exp ∘ f) x₀ (exp (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D exp (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (exp (f x₀) * D₁)
          := by poly_rw [Exp, h_f.eq h₁]

private instance deriv_compExp'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ exp (f x)) x₀ (exp (f x₀) * D₁) c₁
:= deriv_compExp

private instance deriv_compExpow
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((a ^ ·) ∘ f) x₀ (ln a * a ^ (f x₀) * D₁) (c₁ ∧ a > 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (a ^ ·) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (ln a * a ^ (f x₀) * D₁)
          := by poly_rw [Expow h_dom, h_f.eq h₁]

private instance deriv_compExpow'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ a ^ (f x)) x₀ (ln a * a ^ (f x₀) * D₁) (c₁ ∧ a > 0)
:= deriv_compExpow

private instance deriv_compLn
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (ln ∘ f) x₀ ((f x₀)⁻¹ * D₁) (c₁ ∧ f x₀ > 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D ln (f x₀) * D f x₀
          := by deriv_comp
    _  =  the ((f x₀)⁻¹ * D₁)
          := by poly_rw [Ln h_dom, h_f.eq h₁]

private instance deriv_compLn'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ ln (f x)) x₀ ((f x₀)⁻¹ * D₁) (c₁ ∧ f x₀ > 0)
:= deriv_compLn

private instance deriv_compLog
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((log a) ∘ f) x₀
      ((ln a * (f x₀))⁻¹ * D₁) (c₁ ∧ f x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D (log a) (f x₀) * D f x₀
          := by deriv_comp
    _  =  the ((ln a * (f x₀))⁻¹ * D₁)
          := by poly_rw [Log h_dom, h_f.eq h₁]

private instance deriv_compLog'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ log a (f x)) x₀
      ((ln a * (f x₀))⁻¹ * D₁) (c₁ ∧ f x₀ > 0 ∧ a > 0 ∧ a ≠ 1)
:= deriv_compLog

private instance deriv_compSin
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sin ∘ f) x₀ (cos (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D sin (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (cos (f x₀) * D₁)
          := by poly_rw [Sin, h_f.eq h₁]

private instance deriv_compSin'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sin (f x)) x₀ (cos (f x₀) * D₁) c₁
:= deriv_compSin

private instance deriv_compCos
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cos ∘ f) x₀ (- sin (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D cos (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- sin (f x₀) * D₁)
          := by poly_rw [Cos, h_f.eq h₁]

private instance deriv_compCos'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cos (f x)) x₀
    (- sin (f x₀) * D₁) c₁
:= deriv_compCos

private instance deriv_compTan
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (tan ∘ f) x₀
    (sec (f x₀) ^ 2 * D₁) (c₁ ∧ (cos (f x₀) ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D tan (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (sec (f x₀) ^ 2 * D₁)
          := by poly_rw [Tan h_dom, h_f.eq h₁]

private instance deriv_compTan'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ tan (f x)) x₀
    (sec (f x₀) ^ 2 * D₁) (c₁ ∧ (cos (f x₀) ≠ 0))
:= deriv_compTan

private instance deriv_compCot
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cot ∘ f) x₀
    (- csc (f x₀) ^ 2 * D₁) (c₁ ∧ (sin (f x₀) ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D cot (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- csc (f x₀) ^ 2 * D₁)
          := by poly_rw [Cot h_dom, h_f.eq h₁]

private instance deriv_compCot'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cot (f x)) x₀
    (- csc (f x₀) ^ 2 * D₁) (c₁ ∧ (sin (f x₀) ≠ 0))
:= deriv_compCot

private instance deriv_compSec
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sec ∘ f) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c₁ ∧ (cos (f x₀) ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D sec (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (tan (f x₀) * sec (f x₀) * D₁)
          := by poly_rw [Sec h_dom, h_f.eq h₁]

private instance deriv_compSec'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sec (f x)) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c₁ ∧ (cos (f x₀) ≠ 0))
:= deriv_compSec

private instance deriv_compCsc
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (csc ∘ f) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c₁ ∧ (sin (f x₀) ≠ 0))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D csc (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- cot (f x₀) * csc (f x₀) * D₁)
          := by poly_rw [Csc h_dom, h_f.eq h₁]

private instance deriv_compCsc'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ csc (f x)) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c₁ ∧ (sin (f x₀) ≠ 0))
:= deriv_compCsc

private instance deriv_compSinh
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sinh ∘ f) x₀
    (cosh (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D sinh (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (cosh (f x₀) * D₁)
          := by poly_rw [Sinh, h_f.eq h₁]

private instance deriv_compSinh'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sinh (f x)) x₀
    (cosh (f x₀) * D₁) c₁
:= deriv_compSinh

private instance deriv_compCosh
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cosh ∘ f) x₀
    (sinh (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D cosh (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (sinh (f x₀) * D₁)
          := by poly_rw [Cosh, h_f.eq h₁]

private instance deriv_compCosh'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cosh (f x)) x₀
    (sinh (f x₀) * D₁) c₁
:= deriv_compCosh

private instance deriv_compTanh
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (tanh ∘ f) x₀
    (sech (f x₀) ^ 2 * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D tanh (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (sech (f x₀) ^ 2 * D₁)
          := by poly_rw [Tanh, h_f.eq h₁]

private instance deriv_compTanh'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ tanh (f x)) x₀
    (sech (f x₀) ^ 2 * D₁) c₁
:= deriv_compTanh

private instance deriv_compCoth
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (coth ∘ f) x₀
    (- csch (f x₀) ^ 2 * D₁) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D coth (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- csch (f x₀) ^ 2 * D₁)
          := by poly_rw [Coth h_dom, h_f.eq h₁]

private instance deriv_compCoth'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ coth (f x)) x₀
    (- csch (f x₀) ^ 2 * D₁) (c₁ ∧ f x₀ ≠ 0)
:= deriv_compCoth

private instance deriv_compSech
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sech ∘ f) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D sech (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- tanh (f x₀) * sech (f x₀) * D₁)
          := by poly_rw [Sech, h_f.eq h₁]

private instance deriv_compSech'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sech (f x)) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c₁
:= deriv_compSech

private instance deriv_compCsch
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (csch ∘ f) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c₁ ∧ f x₀ ≠ 0)
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D csch (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (- coth (f x₀) * csch (f x₀) * D₁)
          := by poly_rw [Csch h_dom, h_f.eq h₁]

private instance deriv_compCsch'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ csch (f x)) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c₁ ∧ f x₀ ≠ 0)
:= deriv_compCsch

private instance deriv_compArcsin
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arcsin ∘ f) x₀
      (1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D arcsin (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (1 / √(1 - f x₀ ^ 2) * D₁)
          := by poly_rw [Arcsin h_dom, h_f.eq h₁]

private instance deriv_compArcsin'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arcsin (f x)) x₀
      (1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1))
:= deriv_compArcsin

private instance deriv_compArccos
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccos ∘ f) x₀
      (-1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D arccos (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1 / √(1 - f x₀ ^ 2) * D₁)
          := by poly_rw [Arccos h_dom, h_f.eq h₁]

private instance deriv_compArccos'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccos (f x)) x₀
      (-1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1))
:= deriv_compArccos

private instance deriv_compArctan
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arctan ∘ f) x₀ (1 / (1 + f x₀ ^ 2) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D arctan (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (1 / (1 + f x₀ ^ 2) * D₁)
          := by poly_rw [Arctan, h_f.eq h₁]

private instance deriv_compArctan'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arctan (f x)) x₀ (1 / (1 + f x₀ ^ 2) * D₁) c₁
:= deriv_compArctan

private instance deriv_compArccot
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccot ∘ f) x₀ (-1 / (1 + f x₀ ^ 2) * D₁) c₁
:= by
  constructor
  intro h₁
  script_given_proper
  calc
    _  =? D arccot (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1 / (1 + f x₀ ^ 2) * D₁)
          := by poly_rw [Arccot, h_f.eq h₁]

private instance deriv_compArccot'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccot (f x)) x₀ (-1 / (1 + f x₀ ^ 2) * D₁) c₁
:= deriv_compArccot

private instance deriv_compArcsec
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arcsec ∘ f) x₀
      (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D arcsec (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁)
          := by poly_rw [Arcsec h_dom, h_f.eq h₁]

private instance deriv_compArcsec'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arcsec (f x)) x₀
      (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1))
:= deriv_compArcsec

private instance deriv_compArccsc
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccsc ∘ f) x₀
      (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1))
:= by
  constructor
  intro ⟨h₁, h_dom⟩
  script_given_proper
  calc
    _  =? D arccsc (f x₀) * D f x₀
          := by deriv_comp
    _  =  the (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁)
          := by poly_rw [Arccsc h_dom, h_f.eq h₁]

private instance deriv_compArccsc'
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccsc (f x)) x₀
      (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1))
:= deriv_compArccsc

end

section
variable {x₀ D₁ : ℝ} {f : ℝ → ℝ} {cond : Prop}

lemma autoDeriv
    [AutoDeriv f x₀ D₁ cond] (h : cond)
  : D f x₀ = the D₁
:= finite_iff.mp <| AutoDeriv.eq h

end


/-! # Tactics -/

/-- ## Derivative Calculator

    __Usage__ `deriv_calc`

    - Only used for derivative expression, including
      - `DerivExpr`
      - `LeftDerivExpr`
      - `RightDerivExpr`

    - `deriv_calc` calculates derivative expressions as much as possible, and
      then uses some built-in tactics to solve the remaining goals.

    - `deriv_calc` requires some side-conditions to hold true in the context,
      which are the sum of the corresponding conditions for these different
      functions:

      - `f x ≠ 0` for `D f⁻¹ x`
      - `g x ≠ 0` for `D (f / g) x`
      - `x ≠ 0` for `D abs x`
      - `x > 0` for `D sqrt x`
      - `x > 0` for `D (pow a) x`
      - `n > 0 ∨ x ≠ 0` for `D (npow n) x`
      - `a > 0` for `D (a ^ ·) x`
      - `x > 0` for `D ln x`
      - `x > 0 ∧ a > 0 ∧ a ≠ 1` for `D (log a) x`
      - `cos x ≠ 0` for `D tan x`
      - `sin x ≠ 0` for `D cot x`
      - `cos x ≠ 0` for `D sec x`
      - `sin x ≠ 0` for `D csc x`
      - `x ≠ 0` for `D coth x`
      - `x ≠ 0` for `D csch x`
      - `x > -1 ∧ x < 1` for `D arcsin x`
      - `x > -1 ∧ x < 1` for `D arccos x`
      - `x < -1 ∨ x > 1` for `D arcsec x`
      - `x < -1 ∨ x > 1` for `D arccsc x`

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
    example (_ : cos x ≠ 0)
      : D tan x + D sec x = the (sec x * (sec x + tan x))
    := by deriv_calc
    example (_ : x > 0) (_ : ln x > 0)
      : D (fun x ↦ ln (ln x)) x = the (1 / (x * ln x))
    := by deriv_calc
    example (_ : x ≠ 0)
      : D (fun x ↦ √(|x| + 1)) x = the (x / (2 * |x| * √(|x| + 1)))
    := by deriv_calc
    ```
-/
macro "deriv_calc" : tactic => `(tactic| (
  intros
  simp
    (discharger := auto_side_condition)
    only [autoDeriv]
  try · change the _  =  the _; congr 1; auto_side_condition
))


page_end


section
variable {x : ℝ}

example (_ : cos x ≠ 0)
  : D tan x + D sec x = the (sec x * (sec x + tan x))
:= by deriv_calc
example (_ : x > 0) (_ : ln x > 0)
  : D (fun x ↦ ln (ln x)) x = the (1 / (x * ln x))
:= by deriv_calc
example (_ : x ≠ 0)
  : D (fun x ↦ √(|x| + 1)) x = the (x / (2 * |x| * √(|x| + 1)))
:= by deriv_calc

end
