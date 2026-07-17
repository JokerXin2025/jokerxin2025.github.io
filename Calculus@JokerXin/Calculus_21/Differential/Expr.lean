/-
    Calculus_21.Differential.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr
import «Calculus_21».Differential.Defs
set_option linter.style.header false


/-! # Derivative Expression -/

noncomputable section

open Classical in
/-- Derivative Expression -/
def DerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- Left Derivative Expression -/
def LeftDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- Right Derivative Expression -/
def RightDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- N-th Order Derivative Expression -/
def NthDerivExpr (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isNthDerivableAt n ⟨f, Iii⟩ x₀ then the (choose h)
  else none

end

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)
macro "Dₙ" : term => `(NthDerivExpr)


/-! # Bridges between Derivative & Derivative Expression -/

open Classical in
/-- Derivative → Derivative Expression -/
theorem Deriv_to_DerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : Deriv ⟨f, I⟩ x₀ A)
  : D f x₀ = the A
:= FuncLimit_to_FuncLimitExpr h_deriv

open Classical in
/-- Derivative Expression → Derivative -/
theorem DerivExpr_to_Deriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D f x₀ = the A)
  : Deriv ⟨f, I⟩ x₀ A
:= by
  unfold DerivExpr at h_deriv
  have h_dom : ∃ δ > 0,
      Nbhd x₀ δ ⊆ ((⟨f, I⟩ - Constant (f x₀)) / (Identity - Constant x₀)).domain := by
    rcases h_I with ⟨δ, hδ_pos, hδ_dom⟩
    use δ, hδ_pos
    intro x hx
    have hx_I : x ∈ I := hδ_dom hx
    have hx_neq : x - x₀ ≠ 0 := sub_ne_zero.mpr hx.2.2
    exact ⟨⟨⟨hx_I, trivial⟩, ⟨trivial, trivial⟩⟩, hx_neq⟩
  exact FuncLimitExpr_to_FuncLimit h_dom h_deriv

open Classical in
/-- Left Derivative → Left Derivative Expression -/
theorem LeftDeriv_to_LeftDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : LeftDeriv ⟨f, I⟩ x₀ A)
  : D₋ f x₀ = the A
:= LeftLimit_to_LeftLimitExpr h_deriv

open Classical in
/-- Left Derivative Expression → Left Derivative -/
theorem LeftDerivExpr_to_LeftDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₋ f x₀ = the A)
  : LeftDeriv ⟨f, I⟩ x₀ A
:= by
  unfold LeftDerivExpr at h_deriv
  have h_dom : ∃ δ > 0,
      Ioo (x₀ - δ) x₀ ⊆ ((⟨f, I⟩ - Constant (f x₀)) / (Identity - Constant x₀)).domain := by
    rcases h_I with ⟨δ, hδ_pos, hδ_dom⟩
    use δ, hδ_pos
    intro x hx
    rcases hx with ⟨hx_l, hx_r⟩
    have hx_nbhd : x ∈ Nbhd x₀ δ := ⟨hx_l, by linarith, by linarith⟩
    have hx_I : x ∈ I := hδ_dom hx_nbhd
    have hx_neq : x - x₀ ≠ 0 := by linarith
    exact ⟨⟨⟨hx_I, trivial⟩, ⟨trivial, trivial⟩⟩, hx_neq⟩
  exact LeftLimitExpr_to_LeftLimit h_dom h_deriv

open Classical in
/-- Right Derivative → Right Derivative Expression -/
theorem RightDeriv_to_RightDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : RightDeriv ⟨f, I⟩ x₀ A)
  : D₊ f x₀ = the A
:= RightLimit_to_RightLimitExpr h_deriv

open Classical in
/-- Right Derivative Expression → Right Derivative -/
theorem RightDerivExpr_to_RightDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₊ f x₀ = the A)
  : RightDeriv ⟨f, I⟩ x₀ A
:= by
  unfold RightDerivExpr at h_deriv
  have h_dom : ∃ δ > 0,
      Ioo x₀ (x₀ + δ) ⊆ ((⟨f, I⟩ - Constant (f x₀)) / (Identity - Constant x₀)).domain := by
    rcases h_I with ⟨δ, hδ_pos, hδ_dom⟩
    use δ, hδ_pos
    intro x hx
    rcases hx with ⟨hx_l, hx_r⟩
    have hx_nbhd : x ∈ Nbhd x₀ δ := ⟨by linarith, hx_r, by linarith⟩
    have hx_I : x ∈ I := hδ_dom hx_nbhd
    have hx_neq : x - x₀ ≠ 0 := by linarith
    exact ⟨⟨⟨hx_I, trivial⟩, ⟨trivial, trivial⟩⟩, hx_neq⟩
  exact RightLimitExpr_to_RightLimit h_dom h_deriv


open Classical in
/-- N-th Order Derivative → N-th Order Derivative Expression -/
theorem NthDeriv_to_NthDerivExpr {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : NthDeriv n ⟨f, Iii⟩ x₀ A)
  : Dₙ n f x₀ = the A
:= by
  unfold NthDerivExpr
  have h_conv : isNthDerivableAt n ⟨f, Iii⟩ x₀ := ⟨A, h_deriv⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact NthDeriv_Unique (choose_spec h_conv) h_deriv

open Classical in
/-- N-th Order Derivative Expression → N-th Order Derivative -/
theorem NthDerivExpr_to_NthDeriv {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Dₙ n f x₀ = the A)
  : NthDeriv n ⟨f, Iii⟩ x₀ A
:= by
  unfold NthDerivExpr at h_deriv
  split at h_deriv
  · rename_i h_conv
    injection h_deriv with h_eq
    rw [← h_eq]
    exact choose_spec h_conv
  · contradiction

/-- Derivative → Left Derivative (Expression) -/
theorem DerivExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : D₋ f x₀ =? D f x₀
:= FuncLimitExpr_toLeft

/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : D₊ f x₀ =? D f x₀
:= FuncLimitExpr_toRight
