import «Calculus_21».Tactics
import «Calculus_21».Expr.Tactics
import «Calculus_21».Differential.Elementary


/-! # Preparations -/

private class AutoDeriv (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → D f x₀ = the val

private instance deriv_patch₁ {k x₀ : ℝ}
  : AutoDeriv (k + ·) x₀ 1 True where
  eq := by
    intro _
    calc
            D (k + ·) x₀
         =? D (const k) x₀ + D id x₀
            := DerivExpr.Add
      _  =  the 0 + the 1
            := by rw [DerivExpr.Constant, DerivExpr.Identity]
      _  =  the (0 + 1)
            := rfl
      _  =  the 1
            := by norm_num

private instance deriv_patch₁' {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((k + ·) ∘ f) x₀ D₁ c where
  eq := sorry

private instance deriv_patch₂ {k x₀ : ℝ}
  : AutoDeriv (k - ·) x₀ (-1) True where
  eq := by
    intro _
    calc
            D (k - ·) x₀
         =? D (const k) x₀ - D id x₀
            := DerivExpr.Sub
      _  =  the 0 - the 1
            := by rw [DerivExpr.Constant, DerivExpr.Identity]
      _  =  the (0 - 1)
            := rfl
      _  =  the (-1)
            := by norm_num

private instance deriv_patch2' {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((k - ·) ∘ f) x₀ (-D₁) c where
  eq := sorry

private instance deriv_patch₃ {k x₀ : ℝ}
  : AutoDeriv (k * ·) x₀ k True where
  eq := by
    intro _
    calc
            D (k * ·) x₀
         =? D (const k) x₀ * the x₀ + the k * D id x₀
            := DerivExpr.Mul
      _  =  the 0 * the x₀ + the k * the 1
            := by rw [DerivExpr.Constant, DerivExpr.Identity]
      _  =  the (0 * x₀ + k * 1)
            := rfl
      _  =  the k
            := by ring_nf

private instance deriv_patch₃' {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((k * ·) ∘ f) x₀ (k * D₁) c where
  eq := sorry

private instance deriv_patch₄ {k x₀ : ℝ}
  : AutoDeriv (k / ·) x₀ (-k / x₀ ^ 2) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    have h_den_ne0 : x₀ ^ 2 ≠ 0 := by simp [h_x₀_ne0]
    calc
            D (k / ·) x₀
         =? (D (const k) x₀ * the x₀ - the k * D id x₀) / the (x₀ ^ 2)
            := DerivExpr.Div
      _  =  (the 0 * the x₀ - the k * the 1) / the (x₀ ^ 2)
            := by rw [DerivExpr.Constant, DerivExpr.Identity]
      _  =  the (0 * x₀ - k * 1) / the (x₀ ^ 2)
            := rfl
      _  =  the ((0 * x₀ - k * 1) / x₀ ^ 2)
            := by rw [UdEqual.calc_div h_den_ne0]
      _  =  the (-k / x₀ ^ 2)
            := by ring_nf

private instance deriv_patch₄' {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((k / ·) ∘ f) x₀ (-k * D₁ / (f x₀ ^ 2)) c where
  eq := sorry

private instance deriv_patch₅ {x₀ : ℝ}
  : AutoDeriv (-·) x₀ (-1) True where
  eq := by
    intro _
    calc
            D (-·) x₀
         =? - D id x₀
            := DerivExpr.Neg
      _  =  - the 1
            := by rw [DerivExpr.Identity]
      _  =  the (-1)
            := rfl

private instance deriv_patch₅' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((-·) ∘ f) x₀ (-D₁) c where
  eq := sorry

private instance deriv_patch₆ {x₀ : ℝ}
  : AutoDeriv (·⁻¹) x₀ (-1 / x₀ ^ 2) (x₀ ≠ 0) where
  eq := by
    intro h_x₀_ne0
    have h_den_ne0 : x₀ ^ 2 ≠ 0 := by simp [h_x₀_ne0]
    calc
            D (·⁻¹) x₀
         =? - D id x₀ / the (x₀ ^ 2)
            := DerivExpr.Inv
      _  =  - the 1 / the (x₀ ^ 2)
            := by rw [DerivExpr.Identity]
      _  =  the (-1) / the (x₀ ^ 2)
            := rfl
      _  =  the (-1 / x₀ ^ 2)
            := by rw [UdEqual.calc_div h_den_ne0]

private instance deriv_patch₆' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((·⁻¹) ∘ f) x₀ (-D₁ / (f x₀ ^ 2)) c where
  eq := sorry

private instance deriv_Constant {C x₀ : ℝ}
  : AutoDeriv (const C) x₀ 0 True where
  eq := directly DerivExpr.Constant

private instance deriv_Constant' {C x₀ : ℝ}
  : AutoDeriv (fun _ ↦ C) x₀ 0 True where
  eq := deriv_Constant.eq

private instance deriv_Identity {x₀ : ℝ}
  : AutoDeriv id x₀ 1 True where
  eq := directly DerivExpr.Identity

private instance deriv_Identity' {x₀ : ℝ}
  : AutoDeriv (·) x₀ 1 True where
  eq := deriv_Identity.eq

private instance deriv_SMul {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c : Prop}
    [AutoDeriv f x₀ D₁ c]
  : AutoDeriv (k • f) x₀ (k * D₁) c where
  eq := by
    intro h_cond
    calc
            D (k • f) x₀
         =? the k * D f x₀
            := DerivExpr.SMul
      _  =  the k * the D₁
            := by rw [AutoDeriv.eq h_cond]
      _  =  the (k * D₁)
            := rfl

private instance deriv_Neg {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [AutoDeriv f x₀ D₁ c]
  : AutoDeriv (-f) x₀ (-D₁) c where
  eq := by
    intro h_cond
    calc
            D (-f) x₀
         =? - D f x₀
            := DerivExpr.Neg
      _  =  - the D₁
            := by rw [AutoDeriv.eq h_cond]
      _  =  the (-D₁)
            := rfl

private instance deriv_Neg' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ - f x) x₀ (-D₁) c where
  eq := deriv_Neg.eq

private instance deriv_Inv {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [AutoDeriv f x₀ D₁ c]
  : AutoDeriv f⁻¹ x₀ (-D₁ / f x₀ ^ 2) (c ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_f_ne0⟩
    have h_den_ne0 : f x₀ ^ 2 ≠ 0 := by simp [h_f_ne0]
    calc
            D f⁻¹ x₀
         =? (- D f x₀) / the (f x₀ ^ 2)
            := DerivExpr.Inv
      _  =  - the D₁ / the (f x₀ ^ 2)
            := by rw [AutoDeriv.eq h_cond]
      _  =  the (-D₁) / the (f x₀ ^ 2)
            := rfl
      _  =  the (-D₁ / f x₀ ^ 2)
            := by rw [UdEqual.calc_div h_den_ne0]

private instance deriv_Inv' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ (f x)⁻¹) x₀ (-D₁ / f x₀ ^ 2) (c ∧ f x₀ ≠ 0) where
  eq := deriv_Inv.eq

private instance deriv_Add {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f + g) x₀ (D₁ + D₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            D (f + g) x₀
         =? D f x₀ + D g x₀
            := DerivExpr.Add
      _  =  the D₁ + the D₂
            := by rw [AutoDeriv.eq h_cond₁, AutoDeriv.eq h_cond₂]
      _  =  the (D₁ + D₂)
            := rfl

private instance deriv_Add' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x + g x) x₀ (D₁ + D₂) (c₁ ∧ c₂) where
  eq := deriv_Add.eq

private instance deriv_Sub {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f - g) x₀ (D₁ - D₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            D (f - g) x₀
         =? D f x₀ - D g x₀
            := DerivExpr.Sub
      _  =  the D₁ - the D₂
            := by rw [AutoDeriv.eq h_cond₁, AutoDeriv.eq h_cond₂]
      _  =  the (D₁ - D₂)
            := rfl

private instance deriv_Sub' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x - g x) x₀ (D₁ - D₂) (c₁ ∧ c₂) where
  eq := deriv_Sub.eq

private instance deriv_Mul {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f * g) x₀ (D₁ * g x₀ + f x₀ * D₂) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_cond₁, h_cond₂⟩
    calc
            D (f * g) x₀
         =? D f x₀ * the (g x₀) + the (f x₀) * D g x₀
            := DerivExpr.Mul
      _  =  the D₁ * the (g x₀) + the (f x₀) * the D₂
            := by rw [AutoDeriv.eq h_cond₁, AutoDeriv.eq h_cond₂]
      _  =  the (D₁ * g x₀ + f x₀ * D₂)
            := rfl

private instance deriv_Mul' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x * g x) x₀ (D₁ * g x₀ + f x₀ * D₂) (c₁ ∧ c₂) where
  eq := deriv_Mul.eq

private instance deriv_Div {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f / g) x₀
    ((D₁ * g x₀ - f x₀ * D₂) / g x₀ ^ 2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond₁, h_cond₂, h_g_ne0⟩
    have h_den_ne0 : g x₀ ^ 2 ≠ 0 := by simp [h_g_ne0]
    calc
            D (f / g) x₀
         =? (D f x₀ * the (g x₀) - the (f x₀) * D g x₀) / the (g x₀ ^ 2)
            := DerivExpr.Div
      _  =  (the D₁ * the (g x₀) - the (f x₀) * the D₂) / the (g x₀ ^ 2)
            := by rw [AutoDeriv.eq h_cond₁, AutoDeriv.eq h_cond₂]
      _  =  the (D₁ * g x₀ - f x₀ * D₂) / the (g x₀ ^ 2)
            := rfl
      _  =  the ((D₁ * g x₀ - f x₀ * D₂) / g x₀ ^ 2)
            := by rw [UdEqual.calc_div h_den_ne0]

private instance deriv_Div' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x / g x) x₀
    ((D₁ * g x₀ - f x₀ * D₂) / g x₀ ^ 2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0) where
  eq := deriv_Div.eq

private instance deriv_Abs {x₀ : ℝ}
  : AutoDeriv abs x₀ (x₀ / |x₀|) (x₀ ≠ 0) where
  eq := DerivExpr.Abs

private instance deriv_Sqrt {x₀ : ℝ}
  : AutoDeriv sqrt x₀ (1 / (2 * √x₀)) (x₀ > 0) where
  eq := DerivExpr.Sqrt

private instance deriv_Power {a x₀ : ℝ}
  : AutoDeriv (pow a) x₀ (a * x₀ ^ (a - 1)) (x₀ > 0) where
  eq := DerivExpr.Power

private instance deriv_Power_ℤ {n : ℤ} {x₀ : ℝ}
  : AutoDeriv (npow n) x₀ (n * x₀ ^ (n - 1)) (n > 0 ∨ x₀ ≠ 0) where
  eq := DerivExpr.Power_ℤ

private instance deriv_Power_ℤ' {n : ℤ} {x₀ : ℝ}
  : AutoDeriv (· ^ n) x₀ (n * x₀ ^ (n - 1)) (n > 0 ∨ x₀ ≠ 0) where
  eq := DerivExpr.Power_ℤ

private instance deriv_Power_ℕ {n : ℕ} {x₀ : ℝ}
  : AutoDeriv (npow n) x₀ (n * x₀ ^ ((n - 1) : ℤ)) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply DerivExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance deriv_Power_ℕ' {n : ℕ} {x₀ : ℝ}
  : AutoDeriv (· ^ (n:ℤ)) x₀ (n * x₀ ^ ((n - 1) : ℤ)) (n > 0 ∨ x₀ ≠ 0) where
  eq := by
    intro h_dom
    apply DerivExpr.Power_ℤ
    exact h_dom.imp Nat.cast_pos.mpr id

private instance deriv_Exp {x₀ : ℝ}
  : AutoDeriv exp x₀ (exp x₀) True where
  eq := directly DerivExpr.Exp

private instance deriv_Expow {a x₀ : ℝ}
  : AutoDeriv (a ^ ·) x₀ (ln a * a ^ x₀) (a > 0) where
  eq := DerivExpr.Expow

private instance deriv_Ln {x₀ : ℝ}
  : AutoDeriv ln x₀ x₀⁻¹ (x₀ > 0) where
  eq := DerivExpr.Ln

private instance deriv_Log {a x₀ : ℝ}
  : AutoDeriv (log a) x₀ (ln a * x₀)⁻¹ (x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := DerivExpr.Log

private instance deriv_Sin {x₀ : ℝ}
  : AutoDeriv sin x₀ (cos x₀) True where
  eq := directly DerivExpr.Sin

private instance deriv_Cos {x₀ : ℝ}
  : AutoDeriv cos x₀ (- sin x₀) True where
  eq := directly DerivExpr.Cos

private instance deriv_Tan {x₀ : ℝ}
  : AutoDeriv tan x₀ (sec x₀ ^ 2) (cos x₀ ≠ 0) where
  eq := DerivExpr.Tan

private instance deriv_Cot {x₀ : ℝ}
  : AutoDeriv cot x₀ (- csc x₀ ^ 2) (sin x₀ ≠ 0) where
  eq := DerivExpr.Cot

private instance deriv_Sec {x₀ : ℝ}
  : AutoDeriv sec x₀ (tan x₀ * sec x₀) (cos x₀ ≠ 0) where
  eq := DerivExpr.Sec

private instance deriv_Csc {x₀ : ℝ}
  : AutoDeriv csc x₀ (- cot x₀ * csc x₀) (sin x₀ ≠ 0) where
  eq := DerivExpr.Csc

private instance deriv_Sinh {x₀ : ℝ}
  : AutoDeriv sinh x₀ (cosh x₀) True where
  eq := directly DerivExpr.Sinh

private instance deriv_Cosh {x₀ : ℝ}
  : AutoDeriv cosh x₀ (sinh x₀) True where
  eq := directly DerivExpr.Cosh

private instance deriv_Tanh {x₀ : ℝ}
  : AutoDeriv tanh x₀ (sech x₀ ^ 2) True where
  eq := directly DerivExpr.Tanh

private instance deriv_Coth {x₀ : ℝ}
  : AutoDeriv coth x₀ (- csch x₀ ^ 2) (x₀ ≠ 0) where
  eq := DerivExpr.Coth

private instance deriv_Sech {x₀ : ℝ}
  : AutoDeriv sech x₀ (- tanh x₀ * sech x₀) True where
  eq := directly DerivExpr.Sech

private instance deriv_Csch {x₀ : ℝ}
  : AutoDeriv csch x₀ (- coth x₀ * csch x₀) (x₀ ≠ 0) where
  eq := DerivExpr.Csch

private instance deriv_Arcsin {x₀ : ℝ}
  : AutoDeriv arcsin x₀ (1 / √(1 - x₀ ^ 2)) (x₀ > -1 ∧ x₀ < 1) where
  eq := DerivExpr.Arcsin

private instance deriv_Arccos {x₀ : ℝ}
  : AutoDeriv arccos x₀ (-1 / √(1 - x₀ ^ 2)) (x₀ > -1 ∧ x₀ < 1) where
  eq := DerivExpr.Arccos

private instance deriv_Arctan {x₀ : ℝ}
  : AutoDeriv arctan x₀ (1 / (1 + x₀ ^ 2)) True where
  eq := directly DerivExpr.Arctan

private instance deriv_Arccot {x₀ : ℝ}
  : AutoDeriv arccot x₀ (-1 / (1 + x₀ ^ 2)) True where
  eq := directly DerivExpr.Arccot

private instance deriv_Arcsec {x₀ : ℝ}
  : AutoDeriv arcsec x₀ (1 / (|x₀| * √(x₀ ^ 2 - 1))) (x₀ < -1 ∨ x₀ > 1) where
  eq := DerivExpr.Arcsec

private instance deriv_Arccsc {x₀ : ℝ}
  : AutoDeriv arccsc x₀ (-1 / (|x₀| * √(x₀ ^ 2 - 1))) (x₀ < -1 ∨ x₀ > 1) where
  eq := DerivExpr.Arccsc

private instance deriv_compAbs {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (abs ∘ f) x₀
    (f x₀ / |f x₀| * D₁) (c ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (abs ∘ f) x₀ =? D abs (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Abs h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compAbs' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ |f x|) x₀
    (f x₀ / |f x₀| * D₁) (c ∧ f x₀ ≠ 0) where
  eq := deriv_compAbs.eq

private instance deriv_compSqrt {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (sqrt ∘ f) x₀
    (1 / (2 * √(f x₀)) * D₁) (c ∧ f x₀ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (sqrt ∘ f) x₀ =? D sqrt (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sqrt h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSqrt' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ √(f x)) x₀
    (1 / (2 * √(f x₀)) * D₁) (c ∧ f x₀ > 0) where
  eq := deriv_compSqrt.eq

private instance deriv_compPower {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((pow a) ∘ f) x₀
    (a * f x₀ ^ (a - 1) * D₁) (c ∧ f x₀ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D ((pow a) ∘ f) x₀ =? D (pow a) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Power h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compPower' {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ f x ^ a) x₀
    (a * f x₀ ^ (a - 1) * D₁) (c ∧ f x₀ > 0) where
  eq := deriv_compPower.eq

private instance deriv_compPower_ℤ {f : ℝ → ℝ} {n : ℤ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((npow n) ∘ f) x₀
    (n * f x₀ ^ (n - 1) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D ((npow n) ∘ f) x₀ =? D (npow n) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Power_ℤ h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compPower_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((· ^ n) ∘ f) x₀
    (n * f x₀ ^ (n - 1) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := deriv_compPower_ℤ.eq

private instance deriv_compPower_ℤ'' {f : ℝ → ℝ} {n : ℤ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ f x ^ n) x₀
    (n * f x₀ ^ (n - 1) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := deriv_compPower_ℤ.eq

private instance deriv_compPower_ℕ {f : ℝ → ℝ} {n : ℕ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((npow n) ∘ f) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D ((npow n) ∘ f) x₀ =? D (npow n) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Power_ℤ] at h_chain
    · rw [h_f.eq h_cond] at h_chain
      exact h_chain
    · exact h_dom.imp Nat.cast_pos.mpr id

private instance deriv_compPower_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((· ^ n) ∘ f) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := deriv_compPower_ℕ.eq

private instance deriv_compPower_ℕ'' {f : ℝ → ℝ} {n : ℕ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ f x ^ n) x₀
    (n * f x₀ ^ ((n - 1) : ℤ) * D₁) (c ∧ (n > 0 ∨ f x₀ ≠ 0)) where
  eq := deriv_compPower_ℕ.eq

private instance deriv_compExp {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (exp ∘ f) x₀
    (exp (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (exp ∘ f) x₀ =? D exp (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Exp] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compExp' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ exp (f x)) x₀
    (exp (f x₀) * D₁) c where
  eq := deriv_compExp.eq

private instance deriv_compExpow {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((a ^ ·) ∘ f) x₀
    (ln a * a ^ (f x₀) * D₁) (c ∧ a > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D ((a ^ ·) ∘ f) x₀ =? D (a ^ ·) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Expow h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compExpow' {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ a ^ (f x)) x₀
    (ln a * a ^ (f x₀) * D₁) (c ∧ a > 0) where
  eq := deriv_compExpow.eq

private instance deriv_compLn {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (ln ∘ f) x₀
    ((f x₀)⁻¹ * D₁) (c ∧ f x₀ > 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (ln ∘ f) x₀ =? D ln (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Ln h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compLn' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ ln (f x)) x₀
    ((f x₀)⁻¹ * D₁) (c ∧ f x₀ > 0) where
  eq := deriv_compLn.eq

private instance deriv_compLog {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv ((log a) ∘ f) x₀
    ((ln a * (f x₀))⁻¹ * D₁) (c ∧ f x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D ((log a) ∘ f) x₀ =? D (log a) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Log h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compLog' {f : ℝ → ℝ} {a x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ log a (f x)) x₀
    ((ln a * (f x₀))⁻¹ * D₁) (c ∧ f x₀ > 0 ∧ a > 0 ∧ a ≠ 1) where
  eq := deriv_compLog.eq

private instance deriv_compSin {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (sin ∘ f) x₀
    (cos (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (sin ∘ f) x₀ =? D sin (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sin] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSin' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ sin (f x)) x₀
    (cos (f x₀) * D₁) c where
  eq := deriv_compSin.eq

private instance deriv_compCos {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (cos ∘ f) x₀
    (- sin (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (cos ∘ f) x₀ =? D cos (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cos] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCos' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ cos (f x)) x₀
    (- sin (f x₀) * D₁) c where
  eq := deriv_compCos.eq

private instance deriv_compTan {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (tan ∘ f) x₀
    (sec (f x₀) ^ 2 * D₁) (c ∧ (cos (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (tan ∘ f) x₀ =? D tan (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Tan h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compTan' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ tan (f x)) x₀
    (sec (f x₀) ^ 2 * D₁) (c ∧ (cos (f x₀) ≠ 0)) where
  eq := deriv_compTan.eq

private instance deriv_compCot {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (cot ∘ f) x₀
    (- csc (f x₀) ^ 2 * D₁) (c ∧ (sin (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (cot ∘ f) x₀ =? D cot (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cot h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCot' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ cot (f x)) x₀
    (- csc (f x₀) ^ 2 * D₁) (c ∧ (sin (f x₀) ≠ 0)) where
  eq := deriv_compCot.eq

private instance deriv_compSec {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (sec ∘ f) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c ∧ (cos (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (sec ∘ f) x₀ =? D sec (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sec h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSec' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ sec (f x)) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c ∧ (cos (f x₀) ≠ 0)) where
  eq := deriv_compSec.eq

private instance deriv_compCsc {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (csc ∘ f) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c ∧ (sin (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (csc ∘ f) x₀ =? D csc (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Csc h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCsc' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ csc (f x)) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c ∧ (sin (f x₀) ≠ 0)) where
  eq := deriv_compCsc.eq

private instance deriv_compSinh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (sinh ∘ f) x₀
    (cosh (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (sinh ∘ f) x₀ =? D sinh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sinh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSinh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ sinh (f x)) x₀
    (cosh (f x₀) * D₁) c where
  eq := deriv_compSinh.eq

private instance deriv_compCosh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (cosh ∘ f) x₀
    (sinh (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (cosh ∘ f) x₀ =? D cosh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cosh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCosh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ cosh (f x)) x₀
    (sinh (f x₀) * D₁) c where
  eq := deriv_compCosh.eq

private instance deriv_compTanh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (tanh ∘ f) x₀
    (sech (f x₀) ^ 2 * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (tanh ∘ f) x₀ =? D tanh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Tanh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compTanh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ tanh (f x)) x₀
    (sech (f x₀) ^ 2 * D₁) c where
  eq := deriv_compTanh.eq

private instance deriv_compCoth {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (coth ∘ f) x₀
    (- csch (f x₀) ^ 2 * D₁) (c ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (coth ∘ f) x₀ =? D coth (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Coth h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCoth' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ coth (f x)) x₀
    (- csch (f x₀) ^ 2 * D₁) (c ∧ f x₀ ≠ 0) where
  eq := deriv_compCoth.eq

private instance deriv_compSech {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (sech ∘ f) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (sech ∘ f) x₀ =? D sech (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sech] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSech' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ sech (f x)) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c where
  eq := deriv_compSech.eq

private instance deriv_compCsch {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (csch ∘ f) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (csch ∘ f) x₀ =? D csch (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Csch h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCsch' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ csch (f x)) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c ∧ f x₀ ≠ 0) where
  eq := deriv_compCsch.eq

private instance deriv_compArcsin {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arcsin ∘ f) x₀
    (1 / √(1 - f x₀ ^ 2) * D₁) (c ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (arcsin ∘ f) x₀ =? D arcsin (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arcsin h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArcsin' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arcsin (f x)) x₀
    (1 / √(1 - f x₀ ^ 2) * D₁) (c ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := deriv_compArcsin.eq

private instance deriv_compArccos {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arccos ∘ f) x₀
    (-1 / √(1 - f x₀ ^ 2) * D₁) (c ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (arccos ∘ f) x₀ =? D arccos (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccos h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccos' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arccos (f x)) x₀
    (-1 / √(1 - f x₀ ^ 2) * D₁) (c ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := deriv_compArccos.eq

private instance deriv_compArctan {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arctan ∘ f) x₀
    (1 / (1 + f x₀ ^ 2) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (arctan ∘ f) x₀ =? D arctan (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arctan] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArctan' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arctan (f x)) x₀
    (1 / (1 + f x₀ ^ 2) * D₁) c where
  eq := deriv_compArctan.eq

private instance deriv_compArccot {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arccot ∘ f) x₀
    (-1 / (1 + f x₀ ^ 2) * D₁) c where
  eq := by
    intro h_cond
    have h_chain : D (arccot ∘ f) x₀ =? D arccot (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccot] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccot' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arccot (f x)) x₀
    (-1 / (1 + f x₀ ^ 2) * D₁) c where
  eq := deriv_compArccot.eq

private instance deriv_compArcsec {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arcsec ∘ f) x₀
    (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (arcsec ∘ f) x₀ =? D arcsec (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arcsec h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArcsec' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arcsec (f x)) x₀
    (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := deriv_compArcsec.eq

private instance deriv_compArccsc {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (arccsc ∘ f) x₀
    (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := by
    intro ⟨h_cond, h_dom⟩
    have h_chain : D (arccsc ∘ f) x₀ =? D arccsc (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccsc h_dom] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccsc' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c : Prop}
    [h_f : AutoDeriv f x₀ D₁ c]
  : AutoDeriv (fun x ↦ arccsc (f x)) x₀
    (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := deriv_compArccsc.eq

lemma autoDeriv {f : ℝ → ℝ} {x₀ : ℝ} {D₁ : ℝ} {cond : Prop}
    [AutoDeriv f x₀ D₁ cond] (h_cond : cond)
  : D f x₀ = the D₁
:= AutoDeriv.eq h_cond


/-! # Tactics -/

/-- ## Derivative Calculator

    __Usage__ `deriv`

    - `deriv` calculates derivative expressions as much as possible in standard
    forms, and then uses built-in tactic `auto_eq` to solve the remaining goal.

    - `deriv` requires differentiability conditions to exist in the context, which
      are the sum of the corresponding conditions for these different functions:

      - `x ≠ 0` for `D (|·|) x`
      - `x > 0` for `D sqrt x`
      - `x > 0` for `D ln x`
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

      For composite functions, the `x` above represents the inner function.

    - The differentiability conditions should preferably be provided as they are.
      If not, `deriv` will try to use `positivity` and `nlinarith` to complete the
      remaining conditions.

    - Only used for derivative expression, including
      - `DerivExpr`
      - `LeftDerivExpr`
      - `RightDerivExpr`

    __Examples__
    ```lean
    variable {x : ℝ}
    example (_ : cos x ≠ 0)
      : D tan x + D sec x = the (sec x * (sec x + tan x))

:= by deriv

    example (_ : x > 0) (_ : ln x > 0)
      : D (fun x ↦ ln (ln x)) x = the (1 / (x * ln x))

:= by deriv

    example (_ : x ≠ 0)
      : D (fun x ↦ √(|x| + 1)) x = the (x / (2 * |x| * √(|x| + 1)))

:= by deriv

    ```
-/
macro "deriv" : tactic => `(tactic| (
  intros
  repeat rw [autoDeriv]
  any_goals
    repeat any_goals apply And.intro
    all_goals first
    | trivial
    | tauto
    | positivity
    | nlinarith
    | norm_num
  try · auto_eq
))

variable {x : ℝ}
example (_ : cos x ≠ 0)
  : D tan x + D sec x = the (sec x * (sec x + tan x))
:= by deriv
example (_ : x > 0) (_ : ln x > 0)
  : D (fun x ↦ ln (ln x)) x = the (1 / (x * ln x))
:= by deriv
example (_ : x ≠ 0)
  : D (fun x ↦ √(|x| + 1)) x = the (x / (2 * |x| * √(|x| + 1)))
:= by deriv
