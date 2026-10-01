/-
    «Calculus_21».Differential.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc.PolyRw
import «Calculus_21».Limit.Expr
import «Calculus_21».Differential.Defs
import «Calculus_21».Limit.Tactics.Congr
import «Calculus_21».Limit.Tactics.Rules
import «Calculus_21».Limit.Tactics.Cont
set_option linter.style.header false


/-! # Derivative Expressions -/

noncomputable section
variable (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ)

/-- Derivative Expression -/
def DerivExpr : LimitValue :=
  lim x₀ fun x ↦ (f x - f x₀) / (x - x₀)

/-- Left Derivative Expression -/
def LeftDerivExpr : LimitValue :=
  lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀)

/-- Right Derivative Expression -/
def RightDerivExpr : LimitValue :=
  lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀)

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


/-! # Bridges between Derivatives and Derivative Expressions -/

open Classical in section
variable {n : ℕ} {f : ℝ → ℝ} {x₀ D₁ : ℝ} {dom : Set ℝ}

/-- Derivative → Derivative Expression -/
theorem Deriv.toDerivExpr
  : Deriv ⟨f, dom⟩ x₀ D₁ → D f x₀ =. the D₁
:= FuncLimit.toFuncLimitExpr

/-- Derivative Expression → Derivative -/
theorem Deriv.fromDerivExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : D f x₀ =. the D₁ → Deriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  apply FuncLimit.fromFuncLimitExpr
  · script_obtain_exist ⟨δ, hδ, hsub⟩ := h_dom
    script_exists δ with hδ
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    exact sub_ne_zero.mpr h_x.2.2
  · exact h_deriv

/-- Left Derivative → Left Derivative Expression -/
theorem LeftDeriv.toLeftDerivExpr
  : LeftDeriv ⟨f, dom⟩ x₀ D₁ → D₋ f x₀ =. the D₁
:= LeftLimit.toLeftLimitExpr

/-- Left Derivative Expression → Left Derivative -/
theorem LeftDeriv.fromLeftDerivExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : D₋ f x₀ =. the D₁ → LeftDeriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  apply LeftLimit.fromLeftLimitExpr
  · script_obtain_exist ⟨δ, hδ, hsub⟩ := h_dom
    script_exists δ with hδ
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    exact sub_ne_zero.mpr (ne_of_lt h_x.2)
  · exact h_deriv

/-- Right Derivative → Right Derivative Expression -/
theorem RightDeriv.toRightDerivExpr
  : RightDeriv ⟨f, dom⟩ x₀ D₁ → D₊ f x₀ =. the D₁
:= RightLimit.toRightLimitExpr

/-- Right Derivative Expression → Right Derivative -/
theorem RightDeriv.fromRightDerivExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : D₊ f x₀ =. the D₁ → RightDeriv ⟨f, dom⟩ x₀ D₁
:= by
  intro h_deriv
  apply RightLimit.fromRightLimitExpr
  · script_obtain_exist ⟨δ, hδ, hsub⟩ := h_dom
    script_exists δ with hδ
    intro x h_x
    refine ⟨⟨⟨hsub h_x, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
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
:= FuncLimitExpr.toLeft

/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr.toRight {f : ℝ → ℝ} {x₀ : ℝ} {A : LimitValue}
  : D f x₀ =. A → D₊ f x₀ =. A
:= FuncLimitExpr.toRight

theorem DerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D f x₀ =. the D₁) → lim x₀ f =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold DerivExpr at hD
  calc
    _  =  lim x₀ fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀
          := by lim_congr 1; field
    _  =. lim x₀ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀))
            + lim x₀ fun _ ↦ f x₀
          := by lim_add
    _  =. lim x₀ (fun x ↦ (f x - f x₀) / (x - x₀)) * lim x₀ (fun x ↦ x - x₀)
            + lim x₀ fun _ ↦ f x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by poly_rw [hD]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            ring_nf

theorem LeftDerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D₋ f x₀ =. the D₁) → lim₋ x₀ f =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold LeftDerivExpr at hD
  calc
    _  =  lim₋ x₀ fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀
          := by
            lim_congr 1
            field [sub_ne_zero.mpr (ne_of_lt _)]
    _  =. lim₋ x₀ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀))
            + lim₋ x₀ fun _ ↦ f x₀
          := by lim_add
    _  =. lim₋ x₀ (fun x ↦ (f x - f x₀) / (x - x₀)) * lim₋ x₀ (fun x ↦ x - x₀)
            + lim₋ x₀ fun _ ↦ f x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by poly_rw [hD]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            ring_nf

theorem RightDerivExpr.toCont {f : ℝ → ℝ} {x₀ : ℝ}
  : (∃ D₁, D₊ f x₀ =. the D₁) → lim₊ x₀ f =. the (f x₀)
:= by
  intro ⟨D₁, hD⟩
  unfold RightDerivExpr at hD
  calc
    _  =  lim₊ x₀ fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀) + f x₀
          := by
            lim_congr 1
            field [sub_ne_zero.mpr (ne_of_gt _)]
    _  =. lim₊ x₀ (fun x ↦ ((f x - f x₀) / (x - x₀)) * (x - x₀))
            + lim₊ x₀ fun _ ↦ f x₀
          := by lim_add
    _  =. lim₊ x₀ (fun x ↦ (f x - f x₀) / (x - x₀)) * lim₊ x₀ (fun x ↦ x - x₀)
            + lim₊ x₀ fun _ ↦ f x₀
          := by lim_mul
    _  =  the D₁ * the 0 + the (f x₀)
          := by poly_rw [hD]; lim_cont
    _  =  the (f x₀)
          := by
            change the (D₁ * 0 + f x₀) = the (f x₀)
            ring_nf


page_end


macro_rules
| `(tactic| use_expr) => `(tactic|
  first
  | refine Deriv.fromDerivExpr ?side ?calculation
  | refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  | refine RightDeriv.fromRightDerivExpr ?side ?calculation
)
