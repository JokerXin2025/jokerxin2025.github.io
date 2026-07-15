import «Calculus@JokerXin».Function.Differential.Defs
import «Calculus@JokerXin».Limit.Expr


/-! ## 导数表达式 Derivative Expression -/

noncomputable section

open Classical in
/-- Derivative Expression -/
def DerivExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    _lim (fun x ↦ (f!! x - f!! x₀) / (x - x₀) : ℝ → ℝ) x₀
  else none

open Classical in
/-- Left Derivative Expression -/
def LeftDerivExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    _lim₋ (fun x ↦ (f!! x - f!! x₀) / (x - x₀) : ℝ → ℝ) x₀
  else none

open Classical in
/-- Right Derivative Expression -/
def RightDerivExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    _lim₊ (fun x ↦ (f!! x - f!! x₀) / (x - x₀) : ℝ → ℝ) x₀
  else none

open Classical in
/-- N-th Order Derivative Expression -/
def NthDerivExpr (n : ℕ) (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : isNthDerivableAt n ⟨f!!, Iii⟩ x₀ then the (choose h)
    else none
  else none

macro "_D" : term => `(DerivExpr)
macro "_D₋" : term => `(LeftDerivExpr)
macro "_D₊" : term => `(RightDerivExpr)
macro "_Dₙ" : term => `(NthDerivExpr)

def DerivExpr' (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ := _D f x₀
def LeftDerivExpr' (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ := _D₋ f x₀
def RightDerivExpr' (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ := _D₊ f x₀
def NthDerivExpr' (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ := _Dₙ n f x₀

macro "D" : term => `(DerivExpr')
macro "D₋" : term => `(LeftDerivExpr')
macro "D₊" : term => `(RightDerivExpr')
macro "Dₙ" : term => `(NthDerivExpr')

end


/-- ### 导数表达式的局部同余性
    ### Derivative Expression's Local Congruence -/
lemma DerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D f x₀ =? D g x₀
:= sorry

/-- ### 左导数表达式的局部同余性
    ### Left Derivative Expression's Local Congruence -/
lemma LeftDerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D₋ f x₀ =? D₋ g x₀
:= sorry

/-- ### 右导数表达式的局部同余性
    ### Right Derivative Expression's Local Congruence -/
lemma RightDerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D₊ f x₀ =? D₊ g x₀
:= sorry

/-- ### n阶导数表达式的局部同余性
    ### N-th Order Derivative Expression's Local Congruence -/
lemma NthDerivExpr.Congr {n : ℕ} {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : Dₙ n f x₀ =? Dₙ n g x₀
:= sorry

open Classical in
theorem NthDerivExpr_to_NthDeriv {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Dₙ n f x₀ = the A)
  : NthDeriv n ⟨f, Iii⟩ x₀ A
:= sorry /-by
  unfold NthDerivExpr at h_deriv
  split at h_deriv
  · rename_i h_derivable
    injection h_deriv with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_derivable
  · contradiction-/

open Classical in
theorem NthDeriv_to_NthDerivExpr {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : NthDeriv n ⟨f, Iii⟩ x₀ A)
  : Dₙ n f x₀ = the A
:= sorry

/-- Derivative → Left Derivative (Expression) -/
theorem DerivExpr.toLeft {f? : ℝ → Option ℝ} {x₀ : ℝ}
  : _D₋ f? x₀ =? _D f? x₀
:= sorry

/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr.toRight {f? : ℝ → Option ℝ} {x₀ : ℝ}
  : _D₊ f? x₀ =? _D f? x₀
:= sorry
