/-
    «Calculus_21».Differential.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Congr
import «Calculus_21».Limit.Tactics.Calc
import «Calculus_21».Differential.Defs
import «Calculus_21».Expr.PolyRw
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Derivative Expressions -/

noncomputable section
variable (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ)

open Classical in
/-- Derivative Expression -/
def DerivExpr : LimitValue :=
  lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- Left Derivative Expression -/
def LeftDerivExpr : LimitValue :=
  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- Right Derivative Expression -/
def RightDerivExpr : LimitValue :=
  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀

open Classical in
/-- N-th Order Derivative Expression -/
def NthDerivExpr : LimitValue :=
  if h : isNthDerivableAt n ⟨f, Iii⟩ x₀ then the (choose h)
  else unknown

end

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)
macro "Dₙ" : term => `(NthDerivExpr)


/-! # Bridges between Derivatives & Derivative Expressions -/

open Classical in section
variable {n : ℕ} {f : ℝ → ℝ} {x₀ D₁ : ℝ} {dom : Set ℝ}

/-- Derivative → Derivative Expression -/
theorem Deriv.toDerivExpr
  : Deriv ⟨f, dom⟩ x₀ D₁ → D f x₀ =. the D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold DerivExpr
  rw [← h_map]
  exact FuncLimit.toFuncLimitExpr h_deriv

/-- Derivative Expression → Derivative -/
theorem Deriv.fromDerivExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : D f x₀ =. the D₁ → Deriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold DerivExpr at h_deriv
  change FuncLimit Q x₀ D₁
  apply FuncLimit.fromFuncLimitExpr
  · rcases h_dom with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, ?_⟩
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    change x - x₀ ≠ 0
    exact sub_ne_zero.mpr h_x.2.2
  · exact h_deriv

/-- Left Derivative → Left Derivative Expression -/
theorem LeftDeriv.toLeftDerivExpr
  : LeftDeriv ⟨f, dom⟩ x₀ D₁ → D₋ f x₀ =. the D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold LeftDerivExpr
  rw [← h_map]
  exact LeftLimit.toLeftLimitExpr h_deriv

/-- Left Derivative Expression → Left Derivative -/
theorem LeftDeriv.fromLeftDerivExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : D₋ f x₀ =. the D₁ → LeftDeriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold LeftDerivExpr at h_deriv
  change LeftLimit Q x₀ D₁
  apply LeftLimit.fromLeftLimitExpr
  · rcases h_dom with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, ?_⟩
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    change x - x₀ ≠ 0
    exact sub_ne_zero.mpr (ne_of_lt h_x.2)
  · exact h_deriv

/-- Right Derivative → Right Derivative Expression -/
theorem RightDeriv.toRightDerivExpr
  : RightDeriv ⟨f, dom⟩ x₀ D₁ → D₊ f x₀ =. the D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold RightDerivExpr
  rw [← h_map]
  exact RightLimit.toRightLimitExpr h_deriv

/-- Right Derivative Expression → Right Derivative -/
theorem RightDeriv.fromRightDerivExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : D₊ f x₀ =. the D₁ → RightDeriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  let Q := (⟨f, dom⟩ - Constant (f x₀)) / (Identity - Constant x₀)
  have h_map : Q.map = fun x ↦ (f x - f x₀) / (x - x₀) := rfl
  unfold RightDerivExpr at h_deriv
  change RightLimit Q x₀ D₁
  apply RightLimit.fromRightLimitExpr
  · rcases h_dom with ⟨δ, hδ, hsub⟩
    refine ⟨δ, hδ, ?_⟩
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    change x - x₀ ≠ 0
    exact sub_ne_zero.mpr (ne_of_gt h_x.1)
  · exact h_deriv

/-- N-th Order Derivative → N-th Order Derivative Expression -/
theorem NthDeriv.toNthDerivExpr
  : NthDeriv n ⟨f, Iii⟩ x₀ D₁ → Dₙ n f x₀ =. the D₁
:= by
  intro h_deriv
  apply LimitValue.finite_iff.mpr
  unfold NthDerivExpr
  have h_exists : isNthDerivableAt n ⟨f, Iii⟩ x₀ := ⟨D₁, h_deriv⟩
  simp only [dif_pos h_exists]
  apply congrArg the
  exact NthDeriv_Unique (choose_spec h_exists) h_deriv

/-- N-th Order Derivative Expression → N-th Order Derivative -/
theorem NthDeriv.fromNthDerivExpr
  : Dₙ n f x₀ =. the D₁ → NthDeriv n ⟨f, Iii⟩ x₀ D₁
:= by
  intro h_deriv
  have h_eq := LimitValue.finite_iff.mp h_deriv
  unfold NthDerivExpr at h_eq
  split at h_eq
  · rename_i h_exists
    have h_value : choose h_exists = D₁ := LimitValue.finite.inj h_eq
    rw [← h_value]
    exact choose_spec h_exists
  · contradiction

end

/-- Derivative → Left Derivative (Expression) -/
theorem DerivExpr.toLeft {f : ℝ → ℝ} {x₀ : ℝ} {A : LimitValue}
  : D f x₀ =. A → D₋ f x₀ =. A
:= by simpa [DerivExpr, LeftDerivExpr] using FuncLimitExpr.toLeft

/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr.toRight {f : ℝ → ℝ} {x₀ : ℝ} {A : LimitValue}
  : D f x₀ =. A → D₊ f x₀ =. A
:= by simpa [DerivExpr, RightDerivExpr] using FuncLimitExpr.toRight

theorem DerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D f x₀ =. the D₁) → lim f x₀ =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold DerivExpr at hD
  have hD_eq := LimitValue.finite_iff.mp hD
  calc
    _  =  lim (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀) x₀
          := by lim_congr_by field within 1
    _  =. lim (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀)) x₀
            + lim (fun _ ↦ f x₀) x₀
          := by lim_add
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * lim (fun x ↦ x - x₀) x₀
            + lim (fun _ ↦ f x₀) x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by rw [hD_eq]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            congr 1
            ring_nf

theorem LeftDerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D₋ f x₀ =. the D₁) → lim₋ f x₀ =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold LeftDerivExpr at hD
  have hD_eq := LimitValue.finite_iff.mp hD
  calc
    _  =  lim₋ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀) x₀
          := by
            lim_congr_by
              (field_simp [sub_ne_zero.mpr (ne_of_lt (by assumption))]; ring)
              within 1
    _  =. lim₋ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀)) x₀
            + lim₋ (fun _ ↦ f x₀) x₀
          := by lim_add
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * lim₋ (fun x ↦ x - x₀) x₀
            + lim₋ (fun _ ↦ f x₀) x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by rw [hD_eq]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            congr 1
            ring_nf

theorem RightDerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D₊ f x₀ =. the D₁) → lim₊ f x₀ =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold RightDerivExpr at hD
  have hD_eq := LimitValue.finite_iff.mp hD
  calc
    _  =  lim₊ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀) x₀
          := by
            lim_congr_by
              (field_simp [sub_ne_zero.mpr (ne_of_gt (by assumption))]; ring)
              within 1
    _  =. lim₊ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀)) x₀
            + lim₊ (fun _ ↦ f x₀) x₀
          := by lim_add
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * lim₊ (fun x ↦ x - x₀) x₀
            + lim₊ (fun _ ↦ f x₀) x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by rw [hD_eq]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            congr 1
            ring_nf

section
variable {f g : ℝ → ℝ} {x₀ : ℝ}

/-- Addition of Derivative Expression -/
theorem DerivExpr.Add
  : D (f + g) x₀ =. D f x₀ + D g x₀
:= calc
    _  =  lim (fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim (fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          + lim (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_add
    _  =  D f x₀ + D g x₀
          := by rfl

/-- Addition of Left Derivative Expression -/
theorem LeftDerivExpr.Add
  : D₋ (f + g) x₀ =. D₋ f x₀ + D₋ g x₀
:= calc
    _  =  lim₋ (fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          + lim₋ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_add
    _  =  D₋ f x₀ + D₋ g x₀
          := by rfl

/-- Addition of Right Derivative Expression -/
theorem RightDerivExpr.Add
  : D₊ (f + g) x₀ =. D₊ f x₀ + D₊ g x₀
:= calc
    _  =  lim₊ (fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          + lim₊ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_add
    _  =  D₊ f x₀ + D₊ g x₀
          := by rfl

/-- Subtraction of Derivative Expression -/
theorem DerivExpr.Sub
  : D (f - g) x₀ =. D f x₀ - D g x₀
:= calc
    _  =  lim (fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim (fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          - lim (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_sub
    _  =  D f x₀ - D g x₀
          := by rfl

/-- Subtraction of Left Derivative Expression -/
theorem LeftDerivExpr.Sub
  : D₋ (f - g) x₀ =. D₋ f x₀ - D₋ g x₀
:= calc
    _  =  lim₋ (fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          - lim₋ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_sub
    _  =  D₋ f x₀ - D₋ g x₀
          := by rfl

/-- Subtraction of Right Derivative Expression -/
theorem RightDerivExpr.Sub
  : D₊ (f - g) x₀ =. D₊ f x₀ - D₊ g x₀
:= calc
    _  =  lim₊ (fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)) x₀
          := by lim_congr_by ring within 1
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀
          - lim₊ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀
          := by lim_sub
    _  =  D₊ f x₀ - D₊ g x₀
           := by rfl

/-- Multiplication of Derivative Expression -/
theorem DerivExpr.Mul
  : D (f * g) x₀ =? D f x₀ * the (g x₀) + D g x₀ * the (f x₀)
:= by
  intro h_proper
  proper_reflect D f x₀ as h_finite
  calc
    _  =  lim (fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim (fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_congr_by ring within 1
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀) * g x₀) x₀
            + lim (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_add
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_smul
    _  =. lim (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim (fun x ↦ (g x - g x₀) / (x - x₀)) x₀ * lim f x₀
          := by lim_mul
    _  =  D f x₀ * the (g x₀) + D g x₀ * the (f x₀)
          := by poly_rw [DerivExpr.toCont h_finite.getEqual]

/-- Multiplication of Left Derivative Expression -/
theorem LeftDerivExpr.Mul
  : D₋ (f * g) x₀ =? D₋ f x₀ * the (g x₀) + D₋ g x₀ * the (f x₀)
:= by
  intro h_proper
  proper_reflect D₋ f x₀ as h_finite
  calc
    _  =  lim₋ (fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₋ (fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_congr_by ring within 1
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀) * g x₀) x₀
            + lim₋ (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_add
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim₋ (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_smul
    _  =. lim₋ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim₋ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀ * lim₋ f x₀
          := by lim_mul
    _  =  D₋ f x₀ * the (g x₀) + D₋ g x₀ * the (f x₀)
          := by poly_rw [LeftDerivExpr.toCont h_finite.getEqual]

/-- Multiplication of Right Derivative Expression -/
theorem RightDerivExpr.Mul
  : D₊ (f * g) x₀ =? D₊ f x₀ * the (g x₀) + D₊ g x₀ * the (f x₀)
:= by
  intro h_proper
  proper_reflect D₊ f x₀ as h_finite
  calc
    _  =  lim₊ (fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)) x₀
          := by rfl
    _  =  lim₊ (fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_congr_by ring within 1
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀) * g x₀) x₀
            + lim₊ (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_add
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim₊ (fun x ↦ (g x - g x₀) / (x - x₀) * f x) x₀
          := by lim_smul
    _  =. lim₊ (fun x ↦ (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            + lim₊ (fun x ↦ (g x - g x₀) / (x - x₀)) x₀ * lim₊ f x₀
          := by lim_mul
    _  =  D₊ f x₀ * the (g x₀) + D₊ g x₀ * the (f x₀)
          := by poly_rw [RightDerivExpr.toCont h_finite.getEqual]

/-- Division of Derivative Expression -/
theorem DerivExpr.Div
  : D (f / g) x₀ =?
      (D f x₀ * the (g x₀) - D g x₀ * the (f x₀)) / the (g x₀ ^ 2)
:= by
  intro h_proper
  proper_reflect D g x₀ as hg_proper
  have hden : g x₀ ^ 2 ≠ 0 := (ProperClass.isProper_div_finite h_proper).2
  have hg0 : g x₀ ≠ 0 := by grind
  have hg_cont := DerivExpr.toCont hg_proper.getEqual
  obtain ⟨δ, hδ, hg_ne⟩ :
      ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, g x ≠ 0 := by
    have hlim := FuncLimit.fromFuncLimitExpr
      ⟨1, zero_lt_one, subset_univ _⟩ hg_cont
    rcases hlim.2 |g x₀| (abs_pos.mpr hg0) with ⟨δ, hδ, hmap⟩
    exists δ with hδ
    intro x hx hg
    have hnear := hmap x hx
    change g x ∈ Nbho (g x₀) |g x₀| at hnear
    rw [Nbho_abs, hg, zero_sub, abs_neg] at hnear
    exact lt_irrefl |g x₀| hnear
  calc
    _  =  lim (fun x =>
            (((f x - f x₀) / (x - x₀)) * g x₀ - ((g x - g x₀) / (x - x₀)) * f x₀) /
            (g x * g x₀)) x₀
          := by
            apply FuncLimitExpr.Congr
            exists δ with hδ
            intro x hx
            change ((f x / g x - f x₀ / g x₀) / (x - x₀)) = _
            field [hg_ne x hx]
    _  =. lim (fun x =>
            ((f x - f x₀) / (x - x₀)) * g x₀ - ((g x - g x₀) / (x - x₀)) * f x₀) x₀
            / lim (fun x => g x * g x₀) x₀
          := by lim_div
    _  =. (lim (fun x => ((f x - f x₀) / (x - x₀)) * g x₀) x₀ -
            lim (fun x => ((g x - g x₀) / (x - x₀)) * f x₀) x₀) /
            lim (fun x => g x * g x₀) x₀
          := by lim_sub
    _  =. (lim (fun x => (f x - f x₀) / (x - x₀)) x₀ * the (g x₀) -
            lim (fun x => (g x - g x₀) / (x - x₀)) x₀ * the (f x₀)) /
            (lim g x₀ * the (g x₀))
          := by lim_smul
    _  =  (lim (fun x => (f x - f x₀) / (x - x₀)) x₀ * the (g x₀) -
            lim (fun x => (g x - g x₀) / (x - x₀)) x₀ * the (f x₀)) /
            (the (g x₀) * the (g x₀))
          := by poly_rw [hg_cont]
    _  =. (lim (fun x => (f x - f x₀) / (x - x₀)) x₀ * the (g x₀)
            - lim (fun x => (g x - g x₀) / (x - x₀)) x₀ * the (f x₀))
            / the (g x₀ ^ 2)
          := by
            gcongr
            change the (g x₀ * g x₀) =. the (g x₀ ^ 2)
            ring_nf
            rfl

/-- Chain Rule of Derivative Expression -/
theorem DerivExpr.Chain
  : D (f ∘ g) x₀ =? D f (g x₀) * D g x₀
:= by
  intro h_proper
  proper_reflect D f (g x₀) as hf_proper
  proper_reflect D g x₀ from h_proper as hg_proper
  obtain ⟨D₁, hD₁⟩ := hf_proper.getEqual
  have hD₁_eq := LimitValue.finite_iff.mp hD₁
  unfold DerivExpr at hD₁_eq
  let slope : ℝ → ℝ := fun u =>
    if u = g x₀ then D₁ else (f u - f (g x₀)) / (u - g x₀)
  have h_slope_comp : lim (slope ∘ g) x₀ = the D₁ := by
    apply LimitValue.finite_iff.mp
    have h_slope_lim : lim slope (g x₀) =. the (slope (g x₀)) := by
      have hlim : lim slope (g x₀) = the D₁ := by
        apply LimitValue.finite_iff.mp
        calc
          _ = lim (fun u => (f u - f (g x₀)) / (u - g x₀)) (g x₀) := by
            apply FuncLimitExpr.Congr
            exists 1 with zero_lt_one
            intro u hu
            simp [slope, hu.2.2]
          _ = the D₁ := hD₁_eq
          _ =. the D₁ := PolyEqual_refl
      simpa [slope] using LimitValue.finite_iff.mpr hlim
    simpa [slope] using
      FuncLimitExpr.CompSV (by poly_rw [DerivExpr.toCont hg_proper.getEqual]) h_slope_lim
  calc
    _  =  lim (fun x => slope (g x) * ((g x - g x₀) / (x - x₀))) x₀
          := by
            apply FuncLimitExpr.Congr
            exists 1 with zero_lt_one
            intro x hx
            by_cases hg_eq : g x = g x₀
            · simp_all only [mem_setOf_eq, ne_eq, Function.comp_apply, sub_self, zero_div, mul_zero]
            · simp only [Function.comp_apply, slope, hg_eq, ↓reduceIte]
              field
    _  =. lim (slope ∘ g) x₀ * lim (fun x => (g x - g x₀) / (x - x₀)) x₀
          := by lim_mul
    _  =  D f (g x₀) * D g x₀
          := by rw [h_slope_comp, ← hD₁_eq]; rfl

end


page_end
