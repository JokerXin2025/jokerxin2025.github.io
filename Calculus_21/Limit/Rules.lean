/-
    «Calculus_21».Limit.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Defs
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Lemmas -/

section
variable {n : ℕ} {k x y L₁ L₂ ε : ℝ}

private lemma smul_near
    (h_ε : ε > 0)
  : ∃ η > 0, ∀ x ∈ Nbho L₁ η, k * x ∈ Nbho (k * L₁) ε
:= by
  by_cases h_k : k = 0
  · subst k
    exists 1 with by norm_num
    intro x h_x
    rw [Nbho_abs]
    simpa using h_ε
  · exists ε / |k| with div_pos h_ε (abs_pos.mpr h_k)
    intro x h_x
    rw [Nbho_abs] at h_x ⊢
    rw [← mul_sub, abs_mul]
    have h_kpos : 0 < |k| := abs_pos.mpr h_k
    calc
      |k| * |x - L₁| < |k| * (ε / |k|) :=
        mul_lt_mul_of_pos_left h_x h_kpos
      _ = ε := by field

private lemma neg_near
  : x ∈ Nbho L₁ ε → -x ∈ Nbho (-L₁) ε
:= by
  intro h_x
  rw [Nbho_abs] at h_x ⊢
  rw [show -x - -L₁ = -(x - L₁) by ring, abs_neg]
  exact h_x

private lemma add_near
  : x ∈ Nbho L₁ (ε / 2) ∧ y ∈ Nbho L₂ (ε / 2) → x + y ∈ Nbho (L₁ + L₂) ε
:= by
  intro ⟨h_x, h_y⟩
  rw [Nbho_abs] at h_x h_y ⊢
  have h_tri : |(x - L₁) + (y - L₂)| ≤ |x - L₁| + |y - L₂| :=
    abs_add_le _ _
  rw [show x + y - (L₁ + L₂) = (x - L₁) + (y - L₂) by ring]
  linarith

private lemma mul_near
    (h_ε : ε > 0)
  : ∃ η > 0, ∀ x ∈ Nbho L₁ η, ∀ y ∈ Nbho L₂ η,
      x * y ∈ Nbho (L₁ * L₂) ε
:= by
  let C := |L₁| + |L₂| + 2
  have h_C : 0 < C := by dsimp [C]; positivity
  exists min 1 (ε / C) with lt_min (by norm_num) (div_pos h_ε h_C)
  intro x h_x y h_y
  rw [Nbho_abs] at h_x h_y ⊢
  have h_η1 : |x - L₁| < 1 := lt_of_lt_of_le h_x (min_le_left _ _)
  have h_ηεx : |x - L₁| < ε / C := lt_of_lt_of_le h_x (min_le_right _ _)
  have h_ηεy : |y - L₂| < ε / C := lt_of_lt_of_le h_y (min_le_right _ _)
  have h_xbound : |x| < |L₁| + 1 := by
    have h_tri : |x| ≤ |x - L₁| + |L₁| := by
      calc
        |x| = |(x - L₁) + L₁| := by ring_nf
        _ ≤ |x - L₁| + |L₁| := abs_add_le _ _
    linarith
  have h_tri : |x * (y - L₂) + L₂ * (x - L₁)| ≤
      |x| * |y - L₂| + |L₂| * |x - L₁| := by
    calc
      |x * (y - L₂) + L₂ * (x - L₁)|
          ≤ |x * (y - L₂)| + |L₂ * (x - L₁)| := abs_add_le _ _
      _ = |x| * |y - L₂| + |L₂| * |x - L₁| := by rw [abs_mul, abs_mul]
  rw [show x * y - L₁ * L₂ = x * (y - L₂) + L₂ * (x - L₁) by ring]
  have h_1 : |x| * |y - L₂| < (|L₁| + 1) * (ε / C) := by
    calc
      |x| * |y - L₂| ≤ (|L₁| + 1) * |y - L₂| :=
        mul_le_mul_of_nonneg_right (le_of_lt h_xbound) (abs_nonneg _)
      _ < (|L₁| + 1) * (ε / C) :=
        mul_lt_mul_of_pos_left h_ηεy (by positivity)
  have h_2 : |L₂| * |x - L₁| ≤ |L₂| * (ε / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt h_ηεx) (abs_nonneg _)
  have h_sum : (|L₁| + 1) * (ε / C) + |L₂| * (ε / C) =
      ε * ((|L₁| + |L₂| + 1) / C) := by ring
  have h_ratio : (|L₁| + |L₂| + 1) / C < 1 := by
    apply (div_lt_one h_C).2
    dsimp [C]
    linarith
  nlinarith

private lemma inv_near
    (h_L₁ : L₁ ≠ 0) (h_ε : ε > 0)
  : ∃ η > 0, ∀ x ∈ Nbho L₁ η, x ≠ 0 ∧ x⁻¹ ∈ Nbho L₁⁻¹ ε
:= by
  have h_Labs : 0 < |L₁| := abs_pos.mpr h_L₁
  let η := min (|L₁| / 2) (ε * |L₁| ^ 2 / 2)
  have h_η : 0 < η := lt_min (by positivity) (by positivity)
  exists η with h_η
  intro x h_x
  rw [Nbho_abs] at h_x
  have h_xclose : |x - L₁| < |L₁| / 2 := lt_of_lt_of_le h_x (min_le_left _ _)
  have h_xabs : |L₁| / 2 < |x| := by
    have h_rev : |L₁| ≤ |L₁ - x| + |x| := by
      calc
        |L₁| = |(L₁ - x) + x| := by ring_nf
        _ ≤ |L₁ - x| + |x| := abs_add_le _ _
    rw [abs_sub_comm] at h_rev
    linarith
  have h_x0 : x ≠ 0 := by
    intro h_xzero
    subst x
    simp only [abs_zero] at h_xabs
    nlinarith
  refine ⟨h_x0, ?_⟩
  rw [Nbho_abs]
  have h_xe : |x - L₁| < ε * |L₁| ^ 2 / 2 :=
    lt_of_lt_of_le h_x (min_le_right _ _)
  have h_inv : x⁻¹ - L₁⁻¹ = (L₁ - x) / (x * L₁) := by field
  rw [h_inv, abs_div, abs_mul]
  have h_den : 0 < |x| * |L₁| := mul_pos (abs_pos.mpr h_x0) h_Labs
  apply (div_lt_iff₀ h_den).2
  have h_prod : |L₁| ^ 2 / 2 < |x| * |L₁| := by
    nlinarith
  rw [abs_sub_comm]
  calc
    |x - L₁| < ε * (|L₁| ^ 2 / 2) := by nlinarith
    _ < ε * (|x| * |L₁|) := mul_lt_mul_of_pos_left h_prod h_ε

private lemma pow_near
    (h_ε : ε > 0)
  : ∃ η > 0, ∀ x ∈ Nbho L₁ η, x ^ n ∈ Nbho (L₁ ^ n) ε
:= by
  induction n generalizing ε with
  | zero =>
      exists 1 with by norm_num
      intro x h_x
      rw [Nbho_abs]
      simpa using h_ε
  | succ n h_ih =>
      obtain ⟨η, h_η, h_mul⟩ := mul_near (L₁ := L₁ ^ n) (L₂ := L₁) h_ε
      obtain ⟨δ, h_δ, h_pow⟩ := h_ih h_η
      exists min δ η with lt_min h_δ h_η
      intro x h_x
      have h_xδ : x ∈ Nbho L₁ δ := by
        rw [Nbho_abs] at h_x ⊢
        exact lt_of_lt_of_le h_x (min_le_left _ _)
      have h_xη : x ∈ Nbho L₁ η := by
        rw [Nbho_abs] at h_x ⊢
        exact lt_of_lt_of_le h_x (min_le_right _ _)
      simpa [pow_succ] using h_mul (x ^ n) (h_pow x h_xδ) x h_xη

end


/-! # Limit Calculation Rules -/

section
variable {A B C : Sequence} {F G H : Function} {n : ℕ} {k x₀ u₀ L₁ L₂ : ℝ}

/-- Scalar Multiplication of Sequence Limit -/
theorem SeqLimit.SMul
  : SeqLimit A L₁ → SeqLimit (k • A) (k * L₁)
:= by
  intro ⟨h_final, h_lim⟩
  constructor
  · exact h_final
  · intro ε h_ε
    obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
    obtain ⟨N, h_N⟩ := h_lim η h_η
    exists N
    intro n h_n
    exact h_smul _ (h_N n h_n)

/-- Scalar Multiplication of Function Limit -/
theorem FuncLimit.SMul
  : FuncLimit F x₀ L₁ → FuncLimit (k • F) x₀ (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  exact h_smul _ (h_map x h_x)

/-- Scalar Multiplication of Left Limit -/
theorem LeftLimit.SMul
  : LeftLimit F x₀ L₁ → LeftLimit (k • F) x₀ (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  exact h_smul _ (h_map x h_x)

/-- Scalar Multiplication of Right Limit -/
theorem RightLimit.SMul
  : RightLimit F x₀ L₁ → RightLimit (k • F) x₀ (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  change k * F.map x ∈ Nbho (k * L₁) ε
  exact h_smul _ (h_map x h_x)

/-- Scalar Multiplication of Limit at Positive Infinity -/
theorem PosInftyLimit.SMul
  : PosInftyLimit F L₁ → PosInftyLimit (k • F) (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
  exists M with h_M
  intro x h_x
  change k * F.map x ∈ Nbho (k * L₁) ε
  exact h_smul _ (h_map x h_x)

/-- Scalar Multiplication of Limit at Negative Infinity -/
theorem NegInftyLimit.SMul
  : NegInftyLimit F L₁ → NegInftyLimit (k • F) (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
  exists M with h_M
  intro x h_x
  change k * F.map x ∈ Nbho (k * L₁) ε
  exact h_smul _ (h_map x h_x)

/-- Scalar Multiplication of Limit at Infinity -/
theorem InftyLimit.SMul
  : InftyLimit F L₁ → InftyLimit (k • F) (k * L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_smul⟩ := smul_near h_ε
  obtain ⟨M, h_M, h_neg, h_pos⟩ := h_lim η h_η
  exists M with h_M
  constructor
  · intro x h_x
    change k * F.map x ∈ Nbho (k * L₁) ε
    exact h_smul _ (h_neg x h_x)
  · intro x h_x
    change k * F.map x ∈ Nbho (k * L₁) ε
    exact h_smul _ (h_pos x h_x)

/-- Additive Inverse of Sequence Limit -/
theorem SeqLimit.Neg
  : SeqLimit A L₁ → SeqLimit (-A) (-L₁)
:= by
  intro ⟨h_final, h_lim⟩
  refine ⟨h_final, ?_⟩
  intro ε h_ε
  obtain ⟨N, h_N⟩ := h_lim ε h_ε
  exists N
  intro n h_n
  change -A.map n ∈ Nbho (-L₁) ε
  exact neg_near (h_N n h_n)

/-- Additive Inverse of Function Limit -/
theorem FuncLimit.Neg
  : FuncLimit F x₀ L₁ → FuncLimit (-F) x₀ (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim ε h_ε
  exists δ with h_δ
  intro x h_x
  change -F.map x ∈ Nbho (-L₁) ε
  exact neg_near (h_map x h_x)

/-- Additive Inverse of Left Limit -/
theorem LeftLimit.Neg
  : LeftLimit F x₀ L₁ → LeftLimit (-F) x₀ (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim ε h_ε
  exists δ with h_δ
  intro x h_x
  change -F.map x ∈ Nbho (-L₁) ε
  exact neg_near (h_map x h_x)

/-- Additive Inverse of Right Limit -/
theorem RightLimit.Neg
  : RightLimit F x₀ L₁ → RightLimit (-F) x₀ (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim ε h_ε
  exists δ with h_δ
  intro x h_x
  change -F.map x ∈ Nbho (-L₁) ε
  exact neg_near (h_map x h_x)

/-- Additive Inverse of Limit at Positive Infinity -/
theorem PosInftyLimit.Neg
  : PosInftyLimit F L₁ → PosInftyLimit (-F) (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim ε h_ε
  exists M with h_M
  intro x h_x
  change -F.map x ∈ Nbho (-L₁) ε
  exact neg_near (h_map x h_x)

/-- Additive Inverse of Limit at Negative Infinity -/
theorem NegInftyLimit.Neg
  : NegInftyLimit F L₁ → NegInftyLimit (-F) (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim ε h_ε
  exists M with h_M
  intro x h_x
  change -F.map x ∈ Nbho (-L₁) ε
  exact neg_near (h_map x h_x)

/-- Additive Inverse of Limit at Infinity -/
theorem InftyLimit.Neg
  : InftyLimit F L₁ → InftyLimit (-F) (-L₁)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨M, h_M, h_neg, h_pos⟩ := h_lim ε h_ε
  exists M with h_M
  constructor
  · intro x h_x
    change -F.map x ∈ Nbho (-L₁) ε
    exact neg_near (h_neg x h_x)
  · intro x h_x
    change -F.map x ∈ Nbho (-L₁) ε
    exact neg_near (h_pos x h_x)

/-- Multiplicative Scalar Power of Sequence Limit -/
theorem SeqLimit.MSPow
  : SeqLimit A L₁ → SeqLimit (A ^ n) (L₁ ^ n)
:= by
  intro ⟨h_final, h_lim⟩
  refine ⟨h_final, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨N, h_N⟩ := h_lim η h_η
  exists N
  intro m h_m
  change A.map m ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_N m h_m)

/-- Multiplicative Scalar Power of Function Limit -/
theorem FuncLimit.MSPow
  : FuncLimit F x₀ L₁ → FuncLimit (F ^ n) x₀ (L₁ ^ n)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_map x h_x)

/-- Multiplicative Scalar Power of Left Limit -/
theorem LeftLimit.MSPow
    (h_A : LeftLimit F x₀ L₁)
  : LeftLimit (F ^ n) x₀ (L₁ ^ n)
:= by
  obtain ⟨h_dom, h_lim⟩ := h_A
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_map x h_x)

/-- Multiplicative Scalar Power of Right Limit -/
theorem RightLimit.MSPow
    (h_A : RightLimit F x₀ L₁)
  : RightLimit (F ^ n) x₀ (L₁ ^ n)
:= by
  obtain ⟨h_dom, h_lim⟩ := h_A
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
  exists δ with h_δ
  intro x h_x
  change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_map x h_x)

/-- Multiplicative Scalar Power of Limit at Positive Infinity -/
theorem PosInftyLimit.MSPow
  : PosInftyLimit F L₁ → PosInftyLimit (F ^ n) (L₁ ^ n)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
  exists M with h_M
  intro x h_x
  change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_map x h_x)

/-- Multiplicative Scalar Power of Limit at Negative Infinity -/
theorem NegInftyLimit.MSPow
  : NegInftyLimit F L₁ → NegInftyLimit (F ^ n) (L₁ ^ n)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
  exists M with h_M
  intro x h_x
  change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
  exact h_pow _ (h_map x h_x)

/-- Multiplicative Scalar Power of Limit at Infinity -/
theorem InftyLimit.MSPow
  : InftyLimit F L₁ → InftyLimit (F ^ n) (L₁ ^ n)
:= by
  intro ⟨h_dom, h_lim⟩
  refine ⟨h_dom, ?_⟩
  intro ε h_ε
  obtain ⟨η, h_η, h_pow⟩ := pow_near h_ε
  obtain ⟨M, h_M, h_neg, h_pos⟩ := h_lim η h_η
  exists M with h_M
  constructor
  · intro x h_x
    change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
    exact h_pow _ (h_neg x h_x)
  · intro x h_x
    change F.map x ^ n ∈ Nbho (L₁ ^ n) ε
    exact h_pow _ (h_pos x h_x)

/-- Multiplicative Inverse of Sequence Limit -/
theorem SeqLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : SeqLimit A L₁ → SeqLimit A⁻¹ L₁⁻¹
-- `A⁻¹.final` is always bounded above by `some (sInf {n | A.map n = 0})`,
-- hence can never be `none`, while `SeqLimit` requires `final = none`.
:= sorry

/-- Multiplicative Inverse of Function Limit -/
theorem FuncLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : FuncLimit F x₀ L₁ → FuncLimit F⁻¹ x₀ L₁⁻¹
:= by
  intro ⟨⟨δd, h_δd, h_dom⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ₀, h_δ₀, h_map₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists min δd δ₀ with lt_min h_δd h_δ₀
    intro x h_x
    have h_xd : x ∈ Nbhd x₀ δd := by
      obtain ⟨h_xl, h_xr, h_xne⟩ := h_x
      exact ⟨by linarith [min_le_left δd δ₀],
        by linarith [min_le_left δd δ₀], h_xne⟩
    have h_x₀ : x ∈ Nbhd x₀ δ₀ := by
      obtain ⟨h_xl, h_xr, h_xne⟩ := h_x
      exact ⟨by linarith [min_le_right δd δ₀],
        by linarith [min_le_right δd δ₀], h_xne⟩
    exact ⟨h_dom h_xd, (h_nonzero _ (h_map₀ x h_x₀)).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
    exists δ with h_δ
    intro x h_x
    change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
    exact (h_inv _ (h_map x h_x)).2

/-- Multiplicative Inverse of Left Limit -/
theorem LeftLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : LeftLimit F x₀ L₁ → LeftLimit F⁻¹ x₀ L₁⁻¹
:= by
  intro ⟨⟨δd, h_δd, h_dom⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ₀, h_δ₀, h_map₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists min δd δ₀ with lt_min h_δd h_δ₀
    intro x h_x
    have h_xd : x ∈ Ioo (x₀ - δd) x₀ := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_left δd δ₀]
    have h_x₀ : x ∈ Ioo (x₀ - δ₀) x₀ := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_right δd δ₀]
    exact ⟨h_dom h_xd, (h_nonzero _ (h_map₀ x h_x₀)).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
    exists δ with h_δ
    intro x h_x
    change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
    exact (h_inv _ (h_map x h_x)).2

/-- Multiplicative Inverse of Right Limit -/
theorem RightLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : RightLimit F x₀ L₁ → RightLimit F⁻¹ x₀ L₁⁻¹
:= by
  intro ⟨⟨δd, h_δd, h_dom⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ₀, h_δ₀, h_map₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists min δd δ₀ with lt_min h_δd h_δ₀
    intro x h_x
    have h_xd : x ∈ Ioo x₀ (x₀ + δd) := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_left δd δ₀]
    have h_x₀ : x ∈ Ioo x₀ (x₀ + δ₀) := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_right δd δ₀]
    exact ⟨h_dom h_xd, (h_nonzero _ (h_map₀ x h_x₀)).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨δ, h_δ, h_map⟩ := h_lim η h_η
    exists δ with h_δ
    intro x h_x
    change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
    exact (h_inv _ (h_map x h_x)).2

/-- Multiplicative Inverse of Limit at Positive Infinity -/
theorem PosInftyLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : PosInftyLimit F L₁ → PosInftyLimit F⁻¹ L₁⁻¹
:= by
  intro ⟨⟨Md, h_Md, h_dom⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M₀, h_M₀, h_map₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists max Md M₀ with by positivity
    intro x h_x
    exact ⟨h_dom (mem_Ioi_max_left h_x),
      (h_nonzero _ (h_map₀ x (mem_Ioi_max_right h_x))).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
    exists M with h_M
    intro x h_x
    change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
    exact (h_inv _ (h_map x h_x)).2

/-- Multiplicative Inverse of Limit at Negative Infinity -/
theorem NegInftyLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : NegInftyLimit F L₁ → NegInftyLimit F⁻¹ L₁⁻¹
:= by
  intro ⟨⟨Md, h_Md, h_dom⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M₀, h_M₀, h_map₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists max Md M₀ with by positivity
    intro x h_x
    exact ⟨h_dom (mem_Iio_neg_max_left h_x),
      (h_nonzero _ (h_map₀ x (mem_Iio_neg_max_right h_x))).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨M, h_M, h_map⟩ := h_lim η h_η
    exists M with h_M
    intro x h_x
    change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
    exact (h_inv _ (h_map x h_x)).2

/-- Multiplicative Inverse of Limit at Infinity -/
theorem InftyLimit.Inv
    (h_L₁_ne0 : L₁ ≠ 0)
  : InftyLimit F L₁ → InftyLimit F⁻¹ L₁⁻¹
:= by
  intro ⟨⟨Md, h_Md, h_domneg, h_dompos⟩, h_lim⟩
  obtain ⟨η₀, h_η₀, h_nonzero⟩ := inv_near h_L₁_ne0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M₀, h_M₀, h_mapneg₀, h_mappos₀⟩ := h_lim η₀ h_η₀
  constructor
  · exists max Md M₀ with by positivity
    constructor
    · intro x h_x
      exact ⟨h_domneg (mem_Iio_neg_max_left h_x),
        (h_nonzero _ (h_mapneg₀ x (mem_Iio_neg_max_right h_x))).1⟩
    · intro x h_x
      exact ⟨h_dompos (mem_Ioi_max_left h_x),
        (h_nonzero _ (h_mappos₀ x (mem_Ioi_max_right h_x))).1⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_inv⟩ := inv_near h_L₁_ne0 h_ε
    obtain ⟨M, h_M, h_mapneg, h_mappos⟩ := h_lim η h_η
    exists M with h_M
    constructor
    · intro x h_x
      change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
      exact (h_inv _ (h_mapneg x h_x)).2
    · intro x h_x
      change (F.map x)⁻¹ ∈ Nbho L₁⁻¹ ε
      exact (h_inv _ (h_mappos x h_x)).2

/-- Addition of Sequence Limit -/
theorem SeqLimit.Add
  : SeqLimit A L₁ → SeqLimit B L₂ → SeqLimit (A + B) (L₁ + L₂)
:= by
  intro ⟨h_Afin, h_Alim⟩ ⟨h_Bfin, h_Blim⟩
  constructor
  · change min A.final B.final = none
    rw [h_Afin, h_Bfin]
    rfl
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨N₁, h_N₁⟩ := h_Alim (ε / 2) h_half
    obtain ⟨N₂, h_N₂⟩ := h_Blim (ε / 2) h_half
    exists max N₁ N₂
    intro n h_n
    change A.map n + B.map n ∈ Nbho (L₁ + L₂) ε
    exact add_near
      ⟨(h_N₁ n (lt_of_le_of_lt (Nat.le_max_left _ _) h_n)),
      (h_N₂ n (lt_of_le_of_lt (Nat.le_max_right _ _) h_n))⟩

/-- Addition of Function Limit -/
theorem FuncLimit.Add
  : FuncLimit F x₀ L₁ → FuncLimit G x₀ L₂ → FuncLimit (F + G) x₀ (L₁ + L₂)
:= by
  intro ⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩ ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨by linarith [h_x.1, min_le_left δF δG],
      by linarith [h_x.2.1, min_le_left δF δG], h_x.2.2⟩,
      h_Gdom ⟨by linarith [h_x.1, min_le_right δF δG],
        by linarith [h_x.2.1, min_le_right δF δG], h_x.2.2⟩⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim (ε / 2) h_half
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim (ε / 2) h_half
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
    exact add_near
      ⟨(h_F x ⟨by linarith [h_x.1, min_le_left δ₁ δ₂],
        by linarith [h_x.2.1, min_le_left δ₁ δ₂], h_x.2.2⟩),
      (h_G x ⟨by linarith [h_x.1, min_le_right δ₁ δ₂],
        by linarith [h_x.2.1, min_le_right δ₁ δ₂], h_x.2.2⟩)⟩

/-- Addition of Left Limit -/
theorem LeftLimit.Add
  : LeftLimit F x₀ L₁ → LeftLimit G x₀ L₂ → LeftLimit (F + G) x₀ (L₁ + L₂)
:= by
  intro ⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩ ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨by linarith [h_x.1, min_le_left δF δG], h_x.2⟩,
      h_Gdom ⟨by linarith [h_x.1, min_le_right δF δG], h_x.2⟩⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim (ε / 2) h_half
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim (ε / 2) h_half
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
    exact add_near
      ⟨(h_F x ⟨by linarith [h_x.1, min_le_left δ₁ δ₂], h_x.2⟩),
      (h_G x ⟨by linarith [h_x.1, min_le_right δ₁ δ₂], h_x.2⟩)⟩

/-- Addition of Right Limit -/
theorem RightLimit.Add
  : RightLimit F x₀ L₁ → RightLimit G x₀ L₂ → RightLimit (F + G) x₀ (L₁ + L₂)
:= by
  intro ⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩ ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨h_x.1, by linarith [h_x.2, min_le_left δF δG]⟩,
      h_Gdom ⟨h_x.1, by linarith [h_x.2, min_le_right δF δG]⟩⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim (ε / 2) h_half
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim (ε / 2) h_half
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
    exact add_near
      ⟨(h_F x ⟨h_x.1, by linarith [h_x.2, min_le_left δ₁ δ₂]⟩),
      (h_G x ⟨h_x.1, by linarith [h_x.2, min_le_right δ₁ δ₂]⟩)⟩

/-- Addition of Limits at Positive Infinity -/
theorem PosInftyLimit.Add
  : PosInftyLimit F L₁ → PosInftyLimit G L₂ → PosInftyLimit (F + G) (L₁ + L₂)
:= by
  intro ⟨⟨MF, h_MF, h_Fdom⟩, h_Flim⟩ ⟨⟨MG, h_MG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists max MF MG with by positivity
    intro x h_x
    exact ⟨h_Fdom (mem_Ioi_max_left h_x), h_Gdom (mem_Ioi_max_right h_x)⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨M₁, h_M₁, h_F⟩ := h_Flim (ε / 2) h_half
    obtain ⟨M₂, h_M₂, h_G⟩ := h_Glim (ε / 2) h_half
    exists max M₁ M₂ with by positivity
    intro x h_x
    change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
    exact add_near ⟨h_F x (mem_Ioi_max_left h_x), h_G x (mem_Ioi_max_right h_x)⟩

/-- Addition of Limits at Negative Infinity -/
theorem NegInftyLimit.Add
  : NegInftyLimit F L₁ → NegInftyLimit G L₂ → NegInftyLimit (F + G) (L₁ + L₂)
:= by
  intro ⟨⟨MF, h_MF, h_Fdom⟩, h_Flim⟩ ⟨⟨MG, h_MG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists max MF MG with by positivity
    intro x h_x
    exact ⟨h_Fdom (mem_Iio_neg_max_left h_x), h_Gdom (mem_Iio_neg_max_right h_x)⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨M₁, h_M₁, h_F⟩ := h_Flim (ε / 2) h_half
    obtain ⟨M₂, h_M₂, h_G⟩ := h_Glim (ε / 2) h_half
    exists max M₁ M₂ with by positivity
    intro x h_x
    change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
    exact add_near
      ⟨h_F x (mem_Iio_neg_max_left h_x), h_G x (mem_Iio_neg_max_right h_x)⟩

/-- Addition of Limits at Infinity -/
theorem InftyLimit.Add
  : InftyLimit F L₁ → InftyLimit G L₂ → InftyLimit (F + G) (L₁ + L₂)
:= by
  intro ⟨⟨MF, h_MF, h_Fdomneg, h_Fdompos⟩, h_Flim⟩ ⟨⟨MG, h_MG, h_Gdomneg, h_Gdompos⟩, h_Glim⟩
  constructor
  · exists max MF MG with by positivity
    constructor
    · intro x h_x
      exact ⟨h_Fdomneg (mem_Iio_neg_max_left h_x),
        h_Gdomneg (mem_Iio_neg_max_right h_x)⟩
    · intro x h_x
      exact ⟨h_Fdompos (mem_Ioi_max_left h_x), h_Gdompos (mem_Ioi_max_right h_x)⟩
  · intro ε h_ε
    have h_half : 0 < ε / 2 := by linarith
    obtain ⟨M₁, h_M₁, h_Fneg, h_Fpos⟩ := h_Flim (ε / 2) h_half
    obtain ⟨M₂, h_M₂, h_Gneg, h_Gpos⟩ := h_Glim (ε / 2) h_half
    exists max M₁ M₂ with by positivity
    constructor
    · intro x h_x
      change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
      exact add_near
        ⟨h_Fneg x (mem_Iio_neg_max_left h_x), h_Gneg x (mem_Iio_neg_max_right h_x)⟩
    · intro x h_x
      change F.map x + G.map x ∈ Nbho (L₁ + L₂) ε
      exact add_near
        ⟨h_Fpos x (mem_Ioi_max_left h_x), h_Gpos x (mem_Ioi_max_right h_x)⟩

/-- Subtraction of Sequence Limit -/
theorem SeqLimit.Sub
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A - B) (L₁ - L₂)
:= by
  have h_result := SeqLimit.Add h_A h_B.Neg
  have h_eq : A - B = A + (-B) := by
    apply Sequence.ext
    · funext n
      change A.map n - B.map n = A.map n + -B.map n
      ring
    · rfl
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction Function Limit -/
theorem FuncLimit.Sub
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F - G) x₀ (L₁ - L₂)
:= by
  have h_result := FuncLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction of Left Limit -/
theorem LeftLimit.Sub
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F - G) x₀ (L₁ - L₂)
:= by
  have h_result := LeftLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction of Right Limit -/
theorem RightLimit.Sub
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F - G) x₀ (L₁ - L₂)
:= by
  have h_result := RightLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction of Limits at Positive Infinity -/
theorem PosInftyLimit.Sub
    (h_F : PosInftyLimit F L₁) (h_G : PosInftyLimit G L₂)
  : PosInftyLimit (F - G) (L₁ - L₂)
:= by
  have h_result := PosInftyLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction of Limits at Negative Infinity -/
theorem NegInftyLimit.Sub
    (h_F : NegInftyLimit F L₁) (h_G : NegInftyLimit G L₂)
  : NegInftyLimit (F - G) (L₁ - L₂)
:= by
  have h_result := NegInftyLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Subtraction of Limits at Infinity -/
theorem InftyLimit.Sub
    (h_F : InftyLimit F L₁) (h_G : InftyLimit G L₂)
  : InftyLimit (F - G) (L₁ - L₂)
:= by
  have h_result := InftyLimit.Add h_F h_G.Neg
  have h_eq : F - G = F + (-G) := by
    apply Function.ext
    · funext x
      change F.map x - G.map x = F.map x + -G.map x
      ring
    · rfl
  rw [h_eq]
  convert h_result using 1
  ring

/-- Multiplication of Sequence Limit -/
theorem SeqLimit.Mul
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A * B) (L₁ * L₂)
:= by
  obtain ⟨h_Afin, h_Alim⟩ := h_A
  obtain ⟨h_Bfin, h_Blim⟩ := h_B
  constructor
  · change min A.final B.final = none
    rw [h_Afin, h_Bfin]
    rfl
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨N₁, h_N₁⟩ := h_Alim η h_η
    obtain ⟨N₂, h_N₂⟩ := h_Blim η h_η
    exists max N₁ N₂
    intro n h_n
    change A.map n * B.map n ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_N₁ n (lt_of_le_of_lt (Nat.le_max_left _ _) h_n))
      _ (h_N₂ n (lt_of_le_of_lt (Nat.le_max_right _ _) h_n))

/-- Multiplication of Function Limit -/
theorem FuncLimit.Mul
  : FuncLimit F x₀ L₁ → FuncLimit G x₀ L₂ → FuncLimit (F * G) x₀ (L₁ * L₂)
:= by
  intro ⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩ ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨by linarith [h_x.1, min_le_left δF δG],
      by linarith [h_x.2.1, min_le_left δF δG], h_x.2.2⟩,
      h_Gdom ⟨by linarith [h_x.1, min_le_right δF δG],
        by linarith [h_x.2.1, min_le_right δF δG], h_x.2.2⟩⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim η h_η
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim η h_η
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_F x ⟨by linarith [h_x.1, min_le_left δ₁ δ₂],
      by linarith [h_x.2.1, min_le_left δ₁ δ₂], h_x.2.2⟩)
      _ (h_G x ⟨by linarith [h_x.1, min_le_right δ₁ δ₂],
        by linarith [h_x.2.1, min_le_right δ₁ δ₂], h_x.2.2⟩)

/-- Multiplication of Left Limit -/
theorem LeftLimit.Mul
  : LeftLimit F x₀ L₁ ∧ LeftLimit G x₀ L₂ → LeftLimit (F * G) x₀ (L₁ * L₂)
:= by
  intro ⟨⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩, ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨by linarith [h_x.1, min_le_left δF δG], h_x.2⟩,
      h_Gdom ⟨by linarith [h_x.1, min_le_right δF δG], h_x.2⟩⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim η h_η
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim η h_η
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_F x ⟨by linarith [h_x.1, min_le_left δ₁ δ₂], h_x.2⟩)
      _ (h_G x ⟨by linarith [h_x.1, min_le_right δ₁ δ₂], h_x.2⟩)

/-- Multiplication of Right Limit -/
theorem RightLimit.Mul
  : RightLimit F x₀ L₁ ∧ RightLimit G x₀ L₂ → RightLimit (F * G) x₀ (L₁ * L₂)
:= by
  intro ⟨⟨⟨δF, h_δF, h_Fdom⟩, h_Flim⟩, ⟨⟨δG, h_δG, h_Gdom⟩, h_Glim⟩⟩
  constructor
  · exists min δF δG with lt_min h_δF h_δG
    intro x h_x
    exact ⟨h_Fdom ⟨h_x.1, by linarith [h_x.2, min_le_left δF δG]⟩,
      h_Gdom ⟨h_x.1, by linarith [h_x.2, min_le_right δF δG]⟩⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨δ₁, h_δ₁, h_F⟩ := h_Flim η h_η
    obtain ⟨δ₂, h_δ₂, h_G⟩ := h_Glim η h_η
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x h_x
    change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_F x ⟨h_x.1, by linarith [h_x.2, min_le_left δ₁ δ₂]⟩)
      _ (h_G x ⟨h_x.1, by linarith [h_x.2, min_le_right δ₁ δ₂]⟩)

/-- Multiplication of Limits at Positive Infinity -/
theorem PosInftyLimit.Mul
  : PosInftyLimit F L₁ ∧ PosInftyLimit G L₂ → PosInftyLimit (F * G) (L₁ * L₂)
:= by
  intro ⟨⟨⟨MF, h_MF, h_Fdom⟩, h_Flim⟩, ⟨⟨MG, h_MG, h_Gdom⟩, h_Glim⟩⟩
  constructor
  · exists max MF MG with by positivity
    intro x h_x
    exact ⟨h_Fdom (mem_Ioi_max_left h_x), h_Gdom (mem_Ioi_max_right h_x)⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨M₁, h_M₁, h_F⟩ := h_Flim η h_η
    obtain ⟨M₂, h_M₂, h_G⟩ := h_Glim η h_η
    exists max M₁ M₂ with by positivity
    intro x h_x
    change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_F x (mem_Ioi_max_left h_x)) _ (h_G x (mem_Ioi_max_right h_x))

/-- Multiplication of Limits at Negative Infinity -/
theorem NegInftyLimit.Mul
  : NegInftyLimit F L₁ ∧ NegInftyLimit G L₂ → NegInftyLimit (F * G) (L₁ * L₂)
:= by
  intro ⟨⟨⟨MF, h_MF, h_Fdom⟩, h_Flim⟩, ⟨⟨MG, h_MG, h_Gdom⟩, h_Glim⟩⟩
  constructor
  · exists max MF MG with by positivity
    intro x h_x
    exact ⟨h_Fdom (mem_Iio_neg_max_left h_x), h_Gdom (mem_Iio_neg_max_right h_x)⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨M₁, h_M₁, h_F⟩ := h_Flim η h_η
    obtain ⟨M₂, h_M₂, h_G⟩ := h_Glim η h_η
    exists max M₁ M₂ with by positivity
    intro x h_x
    change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
    exact h_mul _ (h_F x (mem_Iio_neg_max_left h_x))
      _ (h_G x (mem_Iio_neg_max_right h_x))

/-- Multiplication of Limits at Infinity -/
theorem InftyLimit.Mul
  : InftyLimit F L₁ ∧ InftyLimit G L₂ → InftyLimit (F * G) (L₁ * L₂)
:= by
  intro ⟨⟨⟨MF, h_MF, h_Fdomneg, h_Fdompos⟩, h_Flim⟩, ⟨⟨MG, h_MG, h_Gdomneg, h_Gdompos⟩, h_Glim⟩⟩
  constructor
  · exists max MF MG with by positivity
    constructor
    · intro x h_x
      exact ⟨h_Fdomneg (mem_Iio_neg_max_left h_x),
        h_Gdomneg (mem_Iio_neg_max_right h_x)⟩
    · intro x h_x
      exact ⟨h_Fdompos (mem_Ioi_max_left h_x), h_Gdompos (mem_Ioi_max_right h_x)⟩
  · intro ε h_ε
    obtain ⟨η, h_η, h_mul⟩ := mul_near h_ε
    obtain ⟨M₁, h_M₁, h_Fneg, h_Fpos⟩ := h_Flim η h_η
    obtain ⟨M₂, h_M₂, h_Gneg, h_Gpos⟩ := h_Glim η h_η
    exists max M₁ M₂ with by positivity
    constructor
    · intro x h_x
      change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
      exact h_mul _ (h_Fneg x (mem_Iio_neg_max_left h_x))
        _ (h_Gneg x (mem_Iio_neg_max_right h_x))
    · intro x h_x
      change F.map x * G.map x ∈ Nbho (L₁ * L₂) ε
      exact h_mul _ (h_Fpos x (mem_Ioi_max_left h_x))
        _ (h_Gpos x (mem_Ioi_max_right h_x))

/-- Division of Sequence Limit -/
theorem SeqLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A / B) (L₁ / L₂)
-- `(A / B).final` is always bounded above by
-- `some (sInf {n | B.map n = 0})`, so it cannot satisfy `final = none`.
:= sorry

/-- Division of Function Limit -/
theorem FuncLimit.Div
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : FuncLimit (F / G) x₀ (L₁ / L₂)
:= by
  have h_result := FuncLimit.Mul h_F (h_G.Inv h_L₂_ne0)
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Division of Left Limit -/
theorem LeftLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F / G) x₀ (L₁ / L₂)
:= by
  have h_result := LeftLimit.Mul ⟨h_F, (h_G.Inv h_L₂_ne0)⟩
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Division of Right Limit -/
theorem RightLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F / G) x₀ (L₁ / L₂)
:= by
  have h_result := RightLimit.Mul ⟨h_F, (h_G.Inv h_L₂_ne0)⟩
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Division of Limits at Positive Infinity -/
theorem PosInftyLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_F : PosInftyLimit F L₁) (h_G : PosInftyLimit G L₂)
  : PosInftyLimit (F / G) (L₁ / L₂)
:= by
  have h_result := PosInftyLimit.Mul ⟨h_F, (h_G.Inv h_L₂_ne0)⟩
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Division of Limits at Negative Infinity -/
theorem NegInftyLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_F : NegInftyLimit F L₁) (h_G : NegInftyLimit G L₂)
  : NegInftyLimit (F / G) (L₁ / L₂)
:= by
  have h_result := NegInftyLimit.Mul ⟨h_F, (h_G.Inv h_L₂_ne0)⟩
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Division of Limits at Infinity -/
theorem InftyLimit.Div
    (h_L₂_ne0 : L₂ ≠ 0)
    (h_F : InftyLimit F L₁) (h_G : InftyLimit G L₂)
  : InftyLimit (F / G) (L₁ / L₂)
:= by
  have h_result := InftyLimit.Mul ⟨h_F, (h_G.Inv h_L₂_ne0)⟩
  have h_eq : F / G = F * G⁻¹ := by
    apply Function.ext
    · funext x
      change F.map x / G.map x = F.map x * (G.map x)⁻¹
      rw [div_eq_mul_inv]
    · ext x
      change ((x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0) ↔
        (x ∈ F.domain ∧ x ∈ G.domain ∧ G.map x ≠ 0)
      tauto
  rw [h_eq]
  convert h_result using 1
  rw [div_eq_mul_inv]

/-- Composition of Function Limit -/
theorem FuncLimit.Comp
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_G_ne_u₀ : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, G.map x ≠ u₀)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_L : FuncLimit F u₀ L₁)
  : FuncLimit (F ⊙ G) x₀ L₁
:= sorry

/-- Squeeze Theorem for Sequence Limit -/
theorem SeqLimit_Squeeze
    (h_A : SeqLimit A L₁) (h_C : SeqLimit C L₁)
    (h_B_inf : B.final = none)
    (h_sqz : ∃ N : ℕ, ∀ n > N, A.map n ≤ B.map n ∧ B.map n ≤ C.map n)
  : SeqLimit B L₁
:= sorry

/-- Squeeze Theorem for Function Limit -/
theorem FuncLimit_Squeeze
    (h_F : FuncLimit F x₀ L₁) (h_H : FuncLimit H x₀ L₁)
    (h_G_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain)
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, F.map x ≤ G.map x ∧ G.map x ≤ H.map x)
  : FuncLimit G x₀ L₁
:= sorry

end


/-! # Calculation rules involving infinite limit values -/

section InfiniteLimitRules

private def EventuallyAt {α ρ : Type} (S : ρ → Set α) (good : ρ → Prop)
    (P : α → Prop) : Prop :=
  ∃ r, good r ∧ ∀ x ∈ S r, P x

private theorem EventuallyAt.and {α ρ : Type} {S : ρ → Set α} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {P Q : α → Prop} (h_P : EventuallyAt S good P) (h_Q : EventuallyAt S good Q) :
    EventuallyAt S good fun x => P x ∧ Q x := by
  obtain ⟨r, h_r, h_Pr⟩ := h_P
  obtain ⟨s, h_s, h_Qs⟩ := h_Q
  obtain ⟨t, h_t, h_sub⟩ := h_sh_rink h_r h_s
  exists t with h_t
  intro x h_x
  exact ⟨h_Pr x (h_sub h_x).1, h_Qs x (h_sub h_x).2⟩

private theorem finiteEventuallyBounded {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} {f : α → ℝ} {L : ℝ}
    (h_result : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε) :
    EventuallyAt S good fun x => |f x| < |L| + 1 := by
  obtain ⟨r, h_r, h_near⟩ := h_result 1 (by norm_num)
  exists r with h_r
  intro x h_x
  have h_xnear := h_near x h_x
  change f x ∈ Nbho L 1 at h_xnear
  rw [Nbho_abs] at h_xnear
  have h_tri : |f x| ≤ |f x - L| + |L| := by
    calc
      |f x| = |(f x - L) + L| := by ring_nf
      _ ≤ |f x - L| + |L| := abs_add_le _ _
  linarith

private theorem eventuallyFiniteAddPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x > M) :
    ∀ M > 0, EventuallyAt S good fun x => f x + g x > M := by
  intro M h_M
  have h_fBound := finiteEventuallyBounded h_f
  have h_T : 0 < M + |L| + 1 := by positivity
  have h_gLarge := h_g (M + |L| + 1) h_T
  obtain ⟨r, h_r, h_both⟩ := h_fBound.and h_sh_rink h_gLarge
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_fLower : -(|L| + 1) < f x := by
    linarith [neg_abs_le (f x), h_result.1]
  linarith [h_result.2]

private theorem eventuallyFiniteAddNeg {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x < -M) :
    ∀ M > 0, EventuallyAt S good fun x => f x + g x < -M := by
  intro M h_M
  have h_fBound := finiteEventuallyBounded h_f
  have h_T : 0 < M + |L| + 1 := by positivity
  have h_gLarge := h_g (M + |L| + 1) h_T
  obtain ⟨r, h_r, h_both⟩ := h_fBound.and h_sh_rink h_gLarge
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_fUpper : f x < |L| + 1 :=
    lt_of_le_of_lt (le_abs_self (f x)) h_result.1
  linarith [h_result.2]

private theorem eventuallyFiniteAddInfty {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => |g x| > M) :
    ∀ M > 0, EventuallyAt S good fun x => |f x + g x| > M := by
  intro M h_M
  have h_fBound := finiteEventuallyBounded h_f
  have h_T : 0 < M + |L| + 1 := by positivity
  have h_gLarge := h_g (M + |L| + 1) h_T
  obtain ⟨r, h_r, h_both⟩ := h_fBound.and h_sh_rink h_gLarge
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_tri : |g x| ≤ |f x + g x| + |f x| := by
    calc
      |g x| = |(f x + g x) + (-f x)| := by ring_nf
      _ ≤ |f x + g x| + |-f x| := abs_add_le _ _
      _ = |f x + g x| + |f x| := by rw [abs_neg]
  linarith [h_result.1, h_result.2]

private theorem eventuallyPosAddPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ}
    (h_f : ∀ M > 0, EventuallyAt S good fun x => f x > M)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x > M) :
    ∀ M > 0, EventuallyAt S good fun x => f x + g x > M := by
  intro M h_M
  obtain ⟨r, h_r, h_both⟩ := (h_f M h_M).and h_sh_rink (h_g M h_M)
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  linarith [h_result.1, h_result.2]

private theorem eventuallyNegAddNeg {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ}
    (h_f : ∀ M > 0, EventuallyAt S good fun x => f x < -M)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x < -M) :
    ∀ M > 0, EventuallyAt S good fun x => f x + g x < -M := by
  intro M h_M
  obtain ⟨r, h_r, h_both⟩ := (h_f M h_M).and h_sh_rink (h_g M h_M)
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  linarith [h_result.1, h_result.2]

private theorem eventuallyInvZero {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} {f : α → ℝ}
    (h_f : ∀ M > 0, EventuallyAt S good fun x => |f x| > M) :
    ∀ ε > 0, EventuallyAt S good fun x => f x ≠ 0 ∧ (f x)⁻¹ ∈ Nbho 0 ε := by
  intro ε h_ε
  obtain ⟨r, h_r, h_large⟩ := h_f ε⁻¹ (inv_pos.mpr h_ε)
  exists r with h_r
  intro x h_x
  have h_fx : ε⁻¹ < |f x| := h_large x h_x
  have h_fx0 : f x ≠ 0 := by
    intro h_result
    rw [h_result, abs_zero] at h_fx
    exact (not_lt_of_ge (le_of_lt (inv_pos.mpr h_ε))) h_fx
  refine ⟨h_fx0, ?_⟩
  rw [Nbho_abs, sub_zero, abs_inv]
  have h_abs : 0 < |f x| := abs_pos.mpr h_fx0
  have h_inv : 0 < |f x|⁻¹ := inv_pos.mpr h_abs
  have h_prod : |f x|⁻¹ * |f x| = 1 := inv_mul_cancel₀ h_abs.ne'
  have h_eps : 1 < ε * |f x| := by
    calc
      1 = ε * ε⁻¹ := (mul_inv_cancel₀ h_ε.ne').symm
      _ < ε * |f x| := mul_lt_mul_of_pos_left h_fx h_ε
  nlinarith

private theorem natTailSh_rink {r s : ℕ} :
    ∃ t, True ∧ {n : ℕ | n > t} ⊆ {n : ℕ | n > r} ∩ {n : ℕ | n > s} := by
  exists max r s with trivial
  intro n h_n
  exact ⟨lt_of_le_of_lt (Nat.le_max_left _ _) h_n,
    lt_of_le_of_lt (Nat.le_max_right _ _) h_n⟩

private theorem nbhdTailSh_rink {x₀ r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Nbhd x₀ t ⊆ Nbhd x₀ r ∩ Nbhd x₀ s := by
  exists min r s with lt_min h_r h_s
  intro x h_x
  exact ⟨⟨by linarith [h_x.1, min_le_left r s],
      by linarith [h_x.2.1, min_le_left r s], h_x.2.2⟩,
    ⟨by linarith [h_x.1, min_le_right r s],
      by linarith [h_x.2.1, min_le_right r s], h_x.2.2⟩⟩

private theorem leftTailSh_rink {x₀ r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Ioo (x₀ - t) x₀ ⊆
      Ioo (x₀ - r) x₀ ∩ Ioo (x₀ - s) x₀ := by
  exists min r s with lt_min h_r h_s
  intro x h_x
  exact ⟨⟨by linarith [h_x.1, min_le_left r s], h_x.2⟩,
    ⟨by linarith [h_x.1, min_le_right r s], h_x.2⟩⟩

private theorem rightTailSh_rink {x₀ r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Ioo x₀ (x₀ + t) ⊆
      Ioo x₀ (x₀ + r) ∩ Ioo x₀ (x₀ + s) := by
  exists min r s with lt_min h_r h_s
  intro x h_x
  exact ⟨⟨h_x.1, by linarith [h_x.2, min_le_left r s]⟩,
    ⟨h_x.1, by linarith [h_x.2, min_le_right r s]⟩⟩

private theorem posInftyTailSh_rink {r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Ioi t ⊆ Ioi r ∩ Ioi s := by
  exists max r s with lt_of_lt_of_le (lt_min h_r h_s)
    (le_trans (min_le_left r s) (le_max_left r s))
  intro x h_x
  change max r s < x at h_x
  exact ⟨lt_of_le_of_lt (le_max_left r s) h_x,
    lt_of_le_of_lt (le_max_right r s) h_x⟩

private theorem negInftyTailSh_rink {r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Iio (-t) ⊆ Iio (-r) ∩ Iio (-s) := by
  exists max r s with lt_of_lt_of_le (lt_min h_r h_s)
    (le_trans (min_le_left r s) (le_max_left r s))
  intro x h_x
  change x < -max r s at h_x
  exact ⟨lt_of_lt_of_le h_x (neg_le_neg (le_max_left r s)),
    lt_of_lt_of_le h_x (neg_le_neg (le_max_right r s))⟩

private theorem inftyTailSh_rink {r s : ℝ} (h_r : r > 0) (h_s : s > 0) :
    ∃ t, t > 0 ∧ Ioi t ∪ Iio (-t) ⊆
      (Ioi r ∪ Iio (-r)) ∩ (Ioi s ∪ Iio (-s)) := by
  exists max r s with lt_of_lt_of_le (lt_min h_r h_s)
    (le_trans (min_le_left r s) (le_max_left r s))
  intro x h_x
  obtain h_x | h_x := h_x
  · change max r s < x at h_x
    exact ⟨Or.inl (lt_of_le_of_lt (le_max_left r s) h_x),
      Or.inl (lt_of_le_of_lt (le_max_right r s) h_x)⟩
  · change x < -max r s at h_x
    exact ⟨Or.inr (lt_of_lt_of_le h_x (neg_le_neg (le_max_left r s))),
      Or.inr (lt_of_lt_of_le h_x (neg_le_neg (le_max_right r s)))⟩

private theorem function_add_comm (F G : Function) : F + G = G + F := by
  apply Function.ext
  · funext _
    exact add_comm _ _
  · ext _
    exact and_comm

private theorem sequence_add_comm (A B : Sequence) : A + B = B + A := by
  apply Sequence.ext
  · funext _
    exact add_comm _ _
  · exact max_comm _ _
  · exact min_comm _ _

variable {A B : Sequence} {F G : Function} {x₀ L : ℝ}

/-- Negation preserves an unsigned infinite sequence limit. -/
theorem SeqLimitInfty.Neg (h_result : SeqLimitInfty A) : SeqLimitInfty (-A) := by
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨N, h_N⟩ := h_result.2 M h_M
  exists N
  intro n h_n
  change |-A.map n| > M
  simpa only [abs_neg] using h_N n h_n

/-- Negation preserves an unsigned infinite function limit. -/
theorem FuncLimitInfty.Neg (h_result : FuncLimitInfty F x₀) : FuncLimitInfty (-F) x₀ := by
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨δ, h_δ, h_map⟩ := h_result.2 M h_M
  exists δ with h_δ
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/-- Negation preserves an unsigned infinite left limit. -/
theorem LeftLimitInfty.Neg (h_result : LeftLimitInfty F x₀) : LeftLimitInfty (-F) x₀ := by
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨δ, h_δ, h_map⟩ := h_result.2 M h_M
  exists δ with h_δ
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/-- Negation preserves an unsigned infinite right limit. -/
theorem RightLimitInfty.Neg (h_result : RightLimitInfty F x₀) : RightLimitInfty (-F) x₀ := by
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨δ, h_δ, h_map⟩ := h_result.2 M h_M
  exists δ with h_δ
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/-- Negation preserves an unsigned infinite limit at positive infinity. -/
theorem PosInftyLimitInfty.Neg
  : PosInftyLimitInfty F → PosInftyLimitInfty (-F)
:= by
  intro h_result
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨X, h_X, h_map⟩ := h_result.2 M h_M
  exists X with h_X
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/-- Negation preserves an unsigned infinite limit at negative infinity. -/
theorem NegInftyLimitInfty.Neg
  : NegInftyLimitInfty F → NegInftyLimitInfty (-F)
:= by
  intro h_result
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨X, h_X, h_map⟩ := h_result.2 M h_M
  exists X with h_X
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/-- Negation preserves an unsigned infinite two-sided limit at infinity. -/
theorem InftyLimitInfty.Neg
  : InftyLimitInfty F → InftyLimitInfty (-F)
:= by
  intro h_result
  refine ⟨h_result.1, ?_⟩
  intro M h_M
  obtain ⟨X, h_X, h_map⟩ := h_result.2 M h_M
  exists X with h_X
  intro x h_x
  change |-F.map x| > M
  simpa only [abs_neg] using h_map x h_x

/- Sequence addition rules. -/

theorem SeqLimit.AddPosInfty
  : SeqLimit A L → SeqLimitPosInfty B → SeqLimitPosInfty (A + B)
:= by
  intro h_A h_B
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  have h_f : ∀ ε > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => A.map n ∈ Nbho L ε := by
    simpa [EventuallyAt] using h_A.2
  have h_g : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => B.map n > M := by
    simpa [EventuallyAt] using h_B.2
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyFiniteAddPos (by
    intro r s h_r h_s
    exact natTailSh_rink) h_f h_g M h_M
  exists N

theorem SeqLimit.AddNegInfty
  : SeqLimit A L → SeqLimitNegInfty B → SeqLimitNegInfty (A + B)
:= by
  intro h_A h_B
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  have h_f : ∀ ε > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => A.map n ∈ Nbho L ε := by
    simpa [EventuallyAt] using h_A.2
  have h_g : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => B.map n < -M := by
    simpa [EventuallyAt] using h_B.2
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyFiniteAddNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) h_f h_g M h_M
  exists N

theorem SeqLimit.AddInfty
  : SeqLimit A L → SeqLimitInfty B → SeqLimitInfty (A + B)
:= by
  intro h_A h_B
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  have h_f : ∀ ε > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => A.map n ∈ Nbho L ε := by
    simpa [EventuallyAt] using h_A.2
  have h_g : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => |B.map n| > M := by
    simpa [EventuallyAt] using h_B.2
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyFiniteAddInfty (by
    intro r s h_r h_s
    exact natTailSh_rink) h_f h_g M h_M
  exists N

theorem SeqLimitPosInfty.AddFinite
  : SeqLimitPosInfty A → SeqLimit B L → SeqLimitPosInfty (A + B)
:= by
  intro h_A h_B
  rw [sequence_add_comm]
  exact h_B.AddPosInfty h_A

theorem SeqLimitNegInfty.AddFinite
  : SeqLimitNegInfty A → SeqLimit B L → SeqLimitNegInfty (A + B)
:= by
  intro h_A h_B
  rw [sequence_add_comm]
  exact h_B.AddNegInfty h_A

theorem SeqLimitInfty.AddFinite
  : SeqLimitInfty A → SeqLimit B L → SeqLimitInfty (A + B)
:= by
  intro h_A h_B
  rw [sequence_add_comm]
  exact h_B.AddInfty h_A

theorem SeqLimitPosInfty.Add
  : SeqLimitPosInfty A → SeqLimitPosInfty B → SeqLimitPosInfty (A + B)
:= by
  intro h_A h_B
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  have h_f : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => A.map n > M := by
    simpa [EventuallyAt] using h_A.2
  have h_g : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => B.map n > M := by
    simpa [EventuallyAt] using h_B.2
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyPosAddPos (by
    intro r s h_r h_s
    exact natTailSh_rink) h_f h_g M h_M
  exists N

theorem SeqLimitNegInfty.Add
  : SeqLimitNegInfty A → SeqLimitNegInfty B → SeqLimitNegInfty (A + B)
:= by
  intro h_A h_B
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  have h_f : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => A.map n < -M := by
    simpa [EventuallyAt] using h_A.2
  have h_g : ∀ M > 0, EventuallyAt (fun N => {n : ℕ | n > N})
      (fun _ => True) fun n => B.map n < -M := by
    simpa [EventuallyAt] using h_B.2
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyNegAddNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) h_f h_g M h_M
  exists N

/- Function addition rules at a finite point. -/

theorem FuncLimit.AddPosInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitPosInfty (F + G) x₀ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, h_r, h_Fr⟩ := h_F.1
    obtain ⟨s, h_s, h_Gs⟩ := h_G.1
    obtain ⟨t, h_t, h_sub⟩ := nbhdTailSh_rink h_r h_s
    exists t with h_t
    intro x h_x
    exact ⟨h_Fr (h_sub h_x).1, h_Gs (h_sub h_x).2⟩
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddPos nbhdTailSh_rink h_F.2 h_G.2 M h_M
    exists r with h_r
    intro x h_x
    change F.map x + G.map x > M
    exact h_map x h_x

theorem FuncLimit.AddNegInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitNegInfty (F + G) x₀ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, h_r, h_Fr⟩ := h_F.1
    obtain ⟨s, h_s, h_Gs⟩ := h_G.1
    obtain ⟨t, h_t, h_sub⟩ := nbhdTailSh_rink h_r h_s
    exists t with h_t
    intro x h_x
    exact ⟨h_Fr (h_sub h_x).1, h_Gs (h_sub h_x).2⟩
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddNeg nbhdTailSh_rink h_F.2 h_G.2 M h_M
    exists r with h_r
    intro x h_x
    change F.map x + G.map x < -M
    exact h_map x h_x

theorem FuncLimit.AddInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitInfty G x₀) : FuncLimitInfty (F + G) x₀ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, h_r, h_Fr⟩ := h_F.1
    obtain ⟨s, h_s, h_Gs⟩ := h_G.1
    obtain ⟨t, h_t, h_sub⟩ := nbhdTailSh_rink h_r h_s
    exists t with h_t
    intro x h_x
    exact ⟨h_Fr (h_sub h_x).1, h_Gs (h_sub h_x).2⟩
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddInfty nbhdTailSh_rink h_F.2 h_G.2 M h_M
    exists r with h_r
    intro x h_x
    change |F.map x + G.map x| > M
    exact h_map x h_x

theorem FuncLimitPosInfty.AddFinite (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitPosInfty (F + G) x₀ := by
  rw [function_add_comm]
  exact h_G.AddPosInfty h_F

theorem FuncLimitNegInfty.AddFinite (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitNegInfty (F + G) x₀ := by
  rw [function_add_comm]
  exact h_G.AddNegInfty h_F

theorem FuncLimitInfty.AddFinite (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitInfty (F + G) x₀ := by
  rw [function_add_comm]
  exact h_G.AddInfty h_F

theorem FuncLimitPosInfty.Add (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitPosInfty (F + G) x₀ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, h_r, h_Fr⟩ := h_F.1
    obtain ⟨s, h_s, h_Gs⟩ := h_G.1
    obtain ⟨t, h_t, h_sub⟩ := nbhdTailSh_rink h_r h_s
    exists t with h_t
    intro x h_x
    exact ⟨h_Fr (h_sub h_x).1, h_Gs (h_sub h_x).2⟩
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyPosAddPos nbhdTailSh_rink h_F.2 h_G.2 M h_M
    exists r with h_r
    intro x h_x
    change F.map x + G.map x > M
    exact h_map x h_x

theorem FuncLimitNegInfty.Add (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitNegInfty (F + G) x₀ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, h_r, h_Fr⟩ := h_F.1
    obtain ⟨s, h_s, h_Gs⟩ := h_G.1
    obtain ⟨t, h_t, h_sub⟩ := nbhdTailSh_rink h_r h_s
    exists t with h_t
    intro x h_x
    exact ⟨h_Fr (h_sub h_x).1, h_Gs (h_sub h_x).2⟩
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyNegAddNeg nbhdTailSh_rink h_F.2 h_G.2 M h_M
    exists r with h_r
    intro x h_x
    change F.map x + G.map x < -M
    exact h_map x h_x

private theorem genericAddPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M) :
    EventuallyAt S good (fun x => x ∈ (F + G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F + G).map x > M := by
  constructor
  · obtain ⟨r, h_r, h_dom⟩ := h_Fdom.and h_sh_rink h_Gdom
    exists r with h_r
    intro x h_x
    exact h_dom x h_x
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddPos h_sh_rink h_F h_G M h_M
    exists r with h_r
    intro x h_x
    exact h_map x h_x

private theorem genericAddNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M) :
    EventuallyAt S good (fun x => x ∈ (F + G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F + G).map x < -M := by
  constructor
  · obtain ⟨r, h_r, h_dom⟩ := h_Fdom.and h_sh_rink h_Gdom
    exists r with h_r
    intro x h_x
    exact h_dom x h_x
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddNeg h_sh_rink h_F h_G M h_M
    exists r with h_r
    intro x h_x
    exact h_map x h_x

private theorem genericAddInfty {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => |G.map x| > M) :
    EventuallyAt S good (fun x => x ∈ (F + G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => |(F + G).map x| > M := by
  constructor
  · obtain ⟨r, h_r, h_dom⟩ := h_Fdom.and h_sh_rink h_Gdom
    exists r with h_r
    intro x h_x
    exact h_dom x h_x
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyFiniteAddInfty h_sh_rink h_F h_G M h_M
    exists r with h_r
    intro x h_x
    exact h_map x h_x

private theorem genericPosAddPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x > M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M) :
    EventuallyAt S good (fun x => x ∈ (F + G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F + G).map x > M := by
  constructor
  · obtain ⟨r, h_r, h_dom⟩ := h_Fdom.and h_sh_rink h_Gdom
    exists r with h_r
    intro x h_x
    exact h_dom x h_x
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyPosAddPos h_sh_rink h_F h_G M h_M
    exists r with h_r
    intro x h_x
    exact h_map x h_x

private theorem genericNegAddNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x < -M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M) :
    EventuallyAt S good (fun x => x ∈ (F + G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F + G).map x < -M := by
  constructor
  · obtain ⟨r, h_r, h_dom⟩ := h_Fdom.and h_sh_rink h_Gdom
    exists r with h_r
    intro x h_x
    exact h_dom x h_x
  · intro M h_M
    obtain ⟨r, h_r, h_map⟩ := eventuallyNegAddNeg h_sh_rink h_F h_G M h_M
    exists r with h_r
    intro x h_x
    exact h_map x h_x

/- The same five addition rules for each remaining one-tail mode. -/

theorem LeftLimit.AddPosInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitPosInfty G x₀) : LeftLimitPosInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddPos leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem LeftLimit.AddNegInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitNegInfty G x₀) : LeftLimitNegInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem LeftLimit.AddInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddInfty leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem LeftLimitPosInfty.Add (h_F : LeftLimitPosInfty F x₀)
    (h_G : LeftLimitPosInfty G x₀) : LeftLimitPosInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericPosAddPos leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem LeftLimitNegInfty.Add (h_F : LeftLimitNegInfty F x₀)
    (h_G : LeftLimitNegInfty G x₀) : LeftLimitNegInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericNegAddNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem RightLimit.AddPosInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitPosInfty G x₀) : RightLimitPosInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddPos rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem RightLimit.AddNegInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitNegInfty G x₀) : RightLimitNegInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem RightLimit.AddInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitInfty G x₀) : RightLimitInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddInfty rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem RightLimitPosInfty.Add (h_F : RightLimitPosInfty F x₀)
    (h_G : RightLimitPosInfty G x₀) : RightLimitPosInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericPosAddPos rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem RightLimitNegInfty.Add (h_F : RightLimitNegInfty F x₀)
    (h_G : RightLimitNegInfty G x₀) : RightLimitNegInfty (F + G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericNegAddNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem PosInftyLimit.AddPosInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitPosInfty G) : PosInftyLimitPosInfty (F + G) := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddPos posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem PosInftyLimit.AddNegInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitNegInfty G) : PosInftyLimitNegInfty (F + G) := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem PosInftyLimit.AddInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F + G) := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddInfty posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem PosInftyLimitPosInfty.Add (h_F : PosInftyLimitPosInfty F)
    (h_G : PosInftyLimitPosInfty G) : PosInftyLimitPosInfty (F + G) := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ (F + G).domain) ∧ _
  exact genericPosAddPos posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem PosInftyLimitNegInfty.Add (h_F : PosInftyLimitNegInfty F)
    (h_G : PosInftyLimitNegInfty G) : PosInftyLimitNegInfty (F + G) := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ (F + G).domain) ∧ _
  exact genericNegAddNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem NegInftyLimit.AddPosInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitPosInfty G) : NegInftyLimitPosInfty (F + G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddPos negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem NegInftyLimit.AddNegInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitNegInfty G) : NegInftyLimitNegInfty (F + G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem NegInftyLimit.AddInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F + G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericAddInfty negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem NegInftyLimitPosInfty.Add (h_F : NegInftyLimitPosInfty F)
    (h_G : NegInftyLimitPosInfty G) : NegInftyLimitPosInfty (F + G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericPosAddPos negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

theorem NegInftyLimitNegInfty.Add (h_F : NegInftyLimitNegInfty F)
    (h_G : NegInftyLimitNegInfty G) : NegInftyLimitNegInfty (F + G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ (F + G).domain) ∧ _
  exact genericNegAddNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2

private theorem inftyFiniteAsUnion (h_result : InftyLimit F L) :
    EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
        (fun x => x ∈ F.domain) ∧
      ∀ ε > 0, EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
        fun x => F.map x ∈ Nbho L ε := by
  constructor
  · obtain ⟨r, h_r, h_neg, h_pos⟩ := h_result.1
    exists r with h_r
    intro x h_x
    obtain h_x | h_x := h_x
    · exact h_pos h_x
    · exact h_neg h_x
  · intro ε h_ε
    obtain ⟨r, h_r, h_neg, h_pos⟩ := h_result.2 ε h_ε
    exists r with h_r
    intro x h_x
    obtain h_x | h_x := h_x
    · exact h_pos x h_x
    · exact h_neg x h_x

private theorem inftyDomainAsUnion
    (h_result : (∃ X > 0, Ioi X ⊆ F.domain ∧ Iio (-X) ⊆ F.domain)) :
    EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => x ∈ F.domain := by
  obtain ⟨r, h_r, h_pos, h_neg⟩ := h_result
  exists r with h_r
  intro x h_x
  obtain h_x | h_x := h_x
  · exact h_pos h_x
  · exact h_neg h_x

private theorem unionDomainToInfty {K : Function}
    (h_result : EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => x ∈ K.domain) :
    ∃ X > 0, Ioi X ⊆ K.domain ∧ Iio (-X) ⊆ K.domain := by
  obtain ⟨r, h_r, h_dom⟩ := h_result
  exists r with h_r
  constructor
  · intro x h_x
    exact h_dom x (Or.inl h_x)
  · intro x h_x
    exact h_dom x (Or.inr h_x)

theorem InftyLimit.AddPosInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitPosInfty G) : InftyLimitPosInfty (F + G) := by
  have h_result := genericAddPos inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2
  exact ⟨unionDomainToInfty h_result.1, h_result.2⟩

theorem InftyLimit.AddNegInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitNegInfty G) : InftyLimitNegInfty (F + G) := by
  have h_result := genericAddNeg inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2
  exact ⟨unionDomainToInfty h_result.1, h_result.2⟩

theorem InftyLimit.AddInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitInfty G) : InftyLimitInfty (F + G) := by
  have h_result := genericAddInfty inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2
  exact ⟨unionDomainToInfty h_result.1, h_result.2⟩

theorem InftyLimitPosInfty.Add (h_F : InftyLimitPosInfty F)
    (h_G : InftyLimitPosInfty G) : InftyLimitPosInfty (F + G) := by
  have h_result := genericPosAddPos inftyTailSh_rink (inftyDomainAsUnion h_F.1)
    (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact ⟨unionDomainToInfty h_result.1, h_result.2⟩

theorem InftyLimitNegInfty.Add (h_F : InftyLimitNegInfty F)
    (h_G : InftyLimitNegInfty G) : InftyLimitNegInfty (F + G) := by
  have h_result := genericNegAddNeg inftyTailSh_rink (inftyDomainAsUnion h_F.1)
    (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact ⟨unionDomainToInfty h_result.1, h_result.2⟩

/- Commuted finite-plus-infinite rules for the remaining function modes. -/

theorem LeftLimitPosInfty.AddFinite (h_F : LeftLimitPosInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitPosInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddPosInfty h_F

theorem LeftLimitNegInfty.AddFinite (h_F : LeftLimitNegInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitNegInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddNegInfty h_F

theorem LeftLimitInfty.AddFinite (h_F : LeftLimitInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddInfty h_F

theorem RightLimitPosInfty.AddFinite (h_F : RightLimitPosInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitPosInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddPosInfty h_F

theorem RightLimitNegInfty.AddFinite (h_F : RightLimitNegInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitNegInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddNegInfty h_F

theorem RightLimitInfty.AddFinite (h_F : RightLimitInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitInfty (F + G) x₀ := by
  rw [function_add_comm]; exact h_G.AddInfty h_F

theorem PosInftyLimitPosInfty.AddFinite (h_F : PosInftyLimitPosInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitPosInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddPosInfty h_F

theorem PosInftyLimitNegInfty.AddFinite (h_F : PosInftyLimitNegInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitNegInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddNegInfty h_F

theorem PosInftyLimitInfty.AddFinite (h_F : PosInftyLimitInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddInfty h_F

theorem NegInftyLimitPosInfty.AddFinite (h_F : NegInftyLimitPosInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitPosInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddPosInfty h_F

theorem NegInftyLimitNegInfty.AddFinite (h_F : NegInftyLimitNegInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitNegInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddNegInfty h_F

theorem NegInftyLimitInfty.AddFinite (h_F : NegInftyLimitInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddInfty h_F

theorem InftyLimitPosInfty.AddFinite (h_F : InftyLimitPosInfty F)
    (h_G : InftyLimit G L) : InftyLimitPosInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddPosInfty h_F

theorem InftyLimitNegInfty.AddFinite (h_F : InftyLimitNegInfty F)
    (h_G : InftyLimit G L) : InftyLimitNegInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddNegInfty h_F

theorem InftyLimitInfty.AddFinite (h_F : InftyLimitInfty F)
    (h_G : InftyLimit G L) : InftyLimitInfty (F + G) := by
  rw [function_add_comm]; exact h_G.AddInfty h_F

private theorem function_sub_eq_add_neg (F G : Function) : F - G = F + (-G) := by
  apply Function.ext
  · funext x; change F.map x - G.map x = F.map x + -G.map x; ring
  · rfl

private theorem sequence_sub_eq_add_neg (A B : Sequence) : A - B = A + (-B) := by
  apply Sequence.ext
  · funext n; change A.map n - B.map n = A.map n + -B.map n; ring
  · rfl
  · rfl

/- Subtraction rules: finite-infinite, infinite-finite, and opposite signs. -/

theorem SeqLimit.SubPosInfty (h_A : SeqLimit A L) (h_B : SeqLimitPosInfty B) :
    SeqLimitNegInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddNegInfty h_B.neg

theorem SeqLimit.SubNegInfty (h_A : SeqLimit A L) (h_B : SeqLimitNegInfty B) :
    SeqLimitPosInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddPosInfty h_B.neg

theorem SeqLimit.SubInfty (h_A : SeqLimit A L) (h_B : SeqLimitInfty B) :
    SeqLimitInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddInfty h_B.Neg

theorem SeqLimitPosInfty.SubFinite (h_A : SeqLimitPosInfty A) (h_B : SeqLimit B L) :
    SeqLimitPosInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddFinite h_B.Neg

theorem SeqLimitNegInfty.SubFinite (h_A : SeqLimitNegInfty A) (h_B : SeqLimit B L) :
    SeqLimitNegInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddFinite h_B.Neg

theorem SeqLimitInfty.SubFinite (h_A : SeqLimitInfty A) (h_B : SeqLimit B L) :
    SeqLimitInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.AddFinite h_B.Neg

theorem SeqLimitPosInfty.SubNegInfty (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimitNegInfty B) : SeqLimitPosInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.Add h_B.neg

theorem SeqLimitNegInfty.SubPosInfty (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimitPosInfty B) : SeqLimitNegInfty (A - B) := by
  rw [sequence_sub_eq_add_neg]; exact h_A.Add h_B.neg

theorem FuncLimit.SubPosInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem FuncLimit.SubNegInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem FuncLimit.SubInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitInfty G x₀) : FuncLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem FuncLimitPosInfty.SubFinite (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem FuncLimitNegInfty.SubFinite (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem FuncLimitInfty.SubFinite (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimit G x₀ L) : FuncLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem FuncLimitPosInfty.SubNegInfty (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem FuncLimitNegInfty.SubPosInfty (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

theorem LeftLimit.SubPosInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitPosInfty G x₀) : LeftLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem LeftLimit.SubNegInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitNegInfty G x₀) : LeftLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem LeftLimit.SubInfty (h_F : LeftLimit F x₀ L)
    (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem LeftLimitPosInfty.SubFinite (h_F : LeftLimitPosInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem LeftLimitNegInfty.SubFinite (h_F : LeftLimitNegInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem LeftLimitInfty.SubFinite (h_F : LeftLimitInfty F x₀)
    (h_G : LeftLimit G x₀ L) : LeftLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem LeftLimitPosInfty.SubNegInfty (h_F : LeftLimitPosInfty F x₀)
    (h_G : LeftLimitNegInfty G x₀) : LeftLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem LeftLimitNegInfty.SubPosInfty (h_F : LeftLimitNegInfty F x₀)
    (h_G : LeftLimitPosInfty G x₀) : LeftLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

theorem RightLimit.SubPosInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitPosInfty G x₀) : RightLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem RightLimit.SubNegInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitNegInfty G x₀) : RightLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem RightLimit.SubInfty (h_F : RightLimit F x₀ L)
    (h_G : RightLimitInfty G x₀) : RightLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem RightLimitPosInfty.SubFinite (h_F : RightLimitPosInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem RightLimitNegInfty.SubFinite (h_F : RightLimitNegInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem RightLimitInfty.SubFinite (h_F : RightLimitInfty F x₀)
    (h_G : RightLimit G x₀ L) : RightLimitInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem RightLimitPosInfty.SubNegInfty (h_F : RightLimitPosInfty F x₀)
    (h_G : RightLimitNegInfty G x₀) : RightLimitPosInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem RightLimitNegInfty.SubPosInfty (h_F : RightLimitNegInfty F x₀)
    (h_G : RightLimitPosInfty G x₀) : RightLimitNegInfty (F - G) x₀ := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

theorem PosInftyLimit.SubPosInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitPosInfty G) : PosInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem PosInftyLimit.SubNegInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitNegInfty G) : PosInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem PosInftyLimit.SubInfty (h_F : PosInftyLimit F L)
    (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem PosInftyLimitPosInfty.SubFinite (h_F : PosInftyLimitPosInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem PosInftyLimitNegInfty.SubFinite (h_F : PosInftyLimitNegInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem PosInftyLimitInfty.SubFinite (h_F : PosInftyLimitInfty F)
    (h_G : PosInftyLimit G L) : PosInftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem PosInftyLimitPosInfty.SubNegInfty (h_F : PosInftyLimitPosInfty F)
    (h_G : PosInftyLimitNegInfty G) : PosInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem PosInftyLimitNegInfty.SubPosInfty (h_F : PosInftyLimitNegInfty F)
    (h_G : PosInftyLimitPosInfty G) : PosInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

theorem NegInftyLimit.SubPosInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitPosInfty G) : NegInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem NegInftyLimit.SubNegInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitNegInfty G) : NegInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem NegInftyLimit.SubInfty (h_F : NegInftyLimit F L)
    (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem NegInftyLimitPosInfty.SubFinite (h_F : NegInftyLimitPosInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem NegInftyLimitNegInfty.SubFinite (h_F : NegInftyLimitNegInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem NegInftyLimitInfty.SubFinite (h_F : NegInftyLimitInfty F)
    (h_G : NegInftyLimit G L) : NegInftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem NegInftyLimitPosInfty.SubNegInfty (h_F : NegInftyLimitPosInfty F)
    (h_G : NegInftyLimitNegInfty G) : NegInftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem NegInftyLimitNegInfty.SubPosInfty (h_F : NegInftyLimitNegInfty F)
    (h_G : NegInftyLimitPosInfty G) : NegInftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

theorem InftyLimit.SubPosInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitPosInfty G) : InftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddNegInfty h_G.neg
theorem InftyLimit.SubNegInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitNegInfty G) : InftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddPosInfty h_G.neg
theorem InftyLimit.SubInfty (h_F : InftyLimit F L)
    (h_G : InftyLimitInfty G) : InftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddInfty h_G.Neg
theorem InftyLimitPosInfty.SubFinite (h_F : InftyLimitPosInfty F)
    (h_G : InftyLimit G L) : InftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem InftyLimitNegInfty.SubFinite (h_F : InftyLimitNegInfty F)
    (h_G : InftyLimit G L) : InftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem InftyLimitInfty.SubFinite (h_F : InftyLimitInfty F)
    (h_G : InftyLimit G L) : InftyLimitInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.AddFinite h_G.Neg
theorem InftyLimitPosInfty.SubNegInfty (h_F : InftyLimitPosInfty F)
    (h_G : InftyLimitNegInfty G) : InftyLimitPosInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg
theorem InftyLimitNegInfty.SubPosInfty (h_F : InftyLimitNegInfty F)
    (h_G : InftyLimitPosInfty G) : InftyLimitNegInfty (F - G) := by
  rw [function_sub_eq_add_neg]; exact h_F.Add h_G.neg

/- Inversion of any infinite function limit gives the corresponding finite limit zero. -/

private theorem genericInvZero {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_dom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_inf : ∀ M > 0, EventuallyAt S good fun x => |F.map x| > M) :
    EventuallyAt S good (fun x => x ∈ F⁻¹.domain) ∧
      ∀ ε > 0, EventuallyAt S good fun x => F⁻¹.map x ∈ Nbho 0 ε := by
  have h_one := eventuallyInvZero h_inf 1 (by norm_num)
  constructor
  · obtain ⟨r, h_r, h_both⟩ := h_dom.and h_sh_rink h_one
    exists r with h_r
    intro x h_x
    exact ⟨(h_both x h_x).1, (h_both x h_x).2.1⟩
  · intro ε h_ε
    obtain ⟨r, h_r, h_map⟩ := eventuallyInvZero h_inf ε h_ε
    exists r with h_r
    intro x h_x
    exact h_map x h_x |>.2

theorem FuncLimitInfty.Inv (h_result : FuncLimitInfty F x₀) : FuncLimit F⁻¹ x₀ 0 := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0)
      (fun x => x ∈ F⁻¹.domain) ∧ _
  exact genericInvZero nbhdTailSh_rink h_result.1 h_result.2

theorem LeftLimitInfty.Inv (h_result : LeftLimitInfty F x₀) : LeftLimit F⁻¹ x₀ 0 := by
  change EventuallyAt (fun r => Ioo (x₀ - r) x₀) (fun r => r > 0)
      (fun x => x ∈ F⁻¹.domain) ∧ _
  exact genericInvZero leftTailSh_rink h_result.1 h_result.2

theorem RightLimitInfty.Inv (h_result : RightLimitInfty F x₀) : RightLimit F⁻¹ x₀ 0 := by
  change EventuallyAt (fun r => Ioo x₀ (x₀ + r)) (fun r => r > 0)
      (fun x => x ∈ F⁻¹.domain) ∧ _
  exact genericInvZero rightTailSh_rink h_result.1 h_result.2

theorem PosInftyLimitInfty.Inv (h_result : PosInftyLimitInfty F) : PosInftyLimit F⁻¹ 0 := by
  change EventuallyAt Ioi (fun r => r > 0) (fun x => x ∈ F⁻¹.domain) ∧ _
  exact genericInvZero posInftyTailSh_rink h_result.1 h_result.2

theorem NegInftyLimitInfty.Inv (h_result : NegInftyLimitInfty F) : NegInftyLimit F⁻¹ 0 := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r > 0)
      (fun x => x ∈ F⁻¹.domain) ∧ _
  exact genericInvZero negInftyTailSh_rink h_result.1 h_result.2

theorem InftyLimitInfty.Inv (h_result : InftyLimitInfty F) : InftyLimit F⁻¹ 0 := by
  have h_u := genericInvZero inftyTailSh_rink (inftyDomainAsUnion h_result.1) h_result.2
  obtain ⟨r, h_r, h_pos, h_neg⟩ := unionDomainToInfty h_u.1
  refine ⟨⟨r, h_r, h_neg, h_pos⟩, ?_⟩
  intro ε h_ε
  obtain ⟨r, h_r, h_map⟩ := h_u.2 ε h_ε
  exists r with h_r
  constructor
  · intro x h_x
    exact h_map x (Or.inr h_x)
  · intro x h_x
    exact h_map x (Or.inl h_x)

theorem FuncLimitPosInfty.Inv (h_result : FuncLimitPosInfty F x₀) : FuncLimit F⁻¹ x₀ 0 :=
  h_result.toFuncLimitInfty.Inv
theorem FuncLimitNegInfty.Inv (h_result : FuncLimitNegInfty F x₀) : FuncLimit F⁻¹ x₀ 0 :=
  h_result.toFuncLimitInfty.Inv
theorem LeftLimitPosInfty.Inv (h_result : LeftLimitPosInfty F x₀) : LeftLimit F⁻¹ x₀ 0 :=
  h_result.toLeftLimitInfty.Inv
theorem LeftLimitNegInfty.Inv (h_result : LeftLimitNegInfty F x₀) : LeftLimit F⁻¹ x₀ 0 :=
  h_result.toLeftLimitInfty.Inv
theorem RightLimitPosInfty.Inv (h_result : RightLimitPosInfty F x₀) : RightLimit F⁻¹ x₀ 0 :=
  h_result.toRightLimitInfty.Inv
theorem RightLimitNegInfty.Inv (h_result : RightLimitNegInfty F x₀) : RightLimit F⁻¹ x₀ 0 :=
  h_result.toRightLimitInfty.Inv
theorem PosInftyLimitPosInfty.Inv (h_result : PosInftyLimitPosInfty F) : PosInftyLimit F⁻¹ 0 :=
  h_result.toPosInftyLimitInfty.Inv
theorem PosInftyLimitNegInfty.Inv (h_result : PosInftyLimitNegInfty F) : PosInftyLimit F⁻¹ 0 :=
  h_result.toPosInftyLimitInfty.Inv
theorem NegInftyLimitPosInfty.Inv (h_result : NegInftyLimitPosInfty F) : NegInftyLimit F⁻¹ 0 :=
  h_result.toNegInftyLimitInfty.Inv
theorem NegInftyLimitNegInfty.Inv (h_result : NegInftyLimitNegInfty F) : NegInftyLimit F⁻¹ 0 :=
  h_result.toNegInftyLimitInfty.Inv
theorem InftyLimitPosInfty.Inv (h_result : InftyLimitPosInfty F) : InftyLimit F⁻¹ 0 :=
  h_result.toInftyLimitInfty.Inv
theorem InftyLimitNegInfty.Inv (h_result : InftyLimitNegInfty F) : InftyLimit F⁻¹ 0 :=
  h_result.toInftyLimitInfty.Inv

/- Multiplication rules involving infinite limit values. -/

private theorem finiteEventuallyPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} {f : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_L : 0 < L) : EventuallyAt S good fun x => L / 2 < f x := by
  obtain ⟨r, h_r, h_map⟩ := h_f (L / 2) (by positivity)
  exists r with h_r
  intro x h_x
  have h_result := h_map x h_x
  change f x ∈ Nbho L (L / 2) at h_result
  rw [Nbho_abs] at h_result
  linarith [neg_abs_le (f x - L)]

private theorem finiteEventuallyNeg {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} {f : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_L : L < 0) : EventuallyAt S good fun x => f x < L / 2 := by
  obtain ⟨r, h_r, h_map⟩ := h_f (-L / 2) (by linarith)
  exists r with h_r
  intro x h_x
  have h_result := h_map x h_x
  change f x ∈ Nbho L (-L / 2) at h_result
  rw [Nbho_abs] at h_result
  linarith [le_abs_self (f x - L)]

private theorem finiteEventuallyAbsPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} {f : α → ℝ} {L : ℝ}
    (h_f : ∀ ε > 0, EventuallyAt S good fun x => f x ∈ Nbho L ε)
    (h_L : L ≠ 0) : EventuallyAt S good fun x => |L| / 2 < |f x| := by
  obtain ⟨r, h_r, h_map⟩ := h_f (|L| / 2) (by positivity)
  exists r with h_r
  intro x h_x
  have h_result := h_map x h_x
  change f x ∈ Nbho L (|L| / 2) at h_result
  rw [Nbho_abs] at h_result
  have h_rev : |L| ≤ |f x - L| + |f x| := by
    calc
      |L| = |-(f x - L) + f x| := by ring_nf
      _ ≤ |-(f x - L)| + |f x| := abs_add_le _ _
      _ = |f x - L| + |f x| := by rw [abs_neg]
  linarith

private theorem eventuallyPosMulPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {c : ℝ} (h_c : 0 < c)
    (h_f : EventuallyAt S good fun x => c < f x)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x > M) :
    ∀ M > 0, EventuallyAt S good fun x => f x * g x > M := by
  intro M h_M
  obtain ⟨r, h_r, h_both⟩ := h_f.and h_sh_rink (h_g (M / c) (div_pos h_M h_c))
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_fx : 0 < f x := lt_trans h_c h_result.1
  have h_q : 0 < M / c := div_pos h_M h_c
  calc
    M = c * (M / c) := by field
    _ < f x * (M / c) := mul_lt_mul_of_pos_right h_result.1 h_q
    _ < f x * g x := mul_lt_mul_of_pos_left h_result.2 h_fx

private theorem eventuallyPosMulNeg {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {c : ℝ} (h_c : 0 < c)
    (h_f : EventuallyAt S good fun x => c < f x)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x < -M) :
    ∀ M > 0, EventuallyAt S good fun x => f x * g x < -M := by
  intro M h_M
  obtain ⟨r, h_r, h_both⟩ := h_f.and h_sh_rink (h_g (M / c) (div_pos h_M h_c))
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_fx : 0 < f x := lt_trans h_c h_result.1
  have h_gneg : g x < 0 := lt_trans h_result.2 (neg_lt_zero.mpr (div_pos h_M h_c))
  have h_prod := mul_lt_mul_of_neg_right h_result.1 h_gneg
  have h_prod' := mul_lt_mul_of_pos_left h_result.2 h_c
  have h_eq : c * (-(M / c)) = -M := by field
  nlinarith

private theorem eventuallyNegMulPos {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {c : ℝ} (h_c : c < 0)
    (h_f : EventuallyAt S good fun x => f x < c)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x > M) :
    ∀ M > 0, EventuallyAt S good fun x => f x * g x < -M := by
  intro M h_M
  have h_cpos : 0 < -c := neg_pos.mpr h_c
  obtain ⟨r, h_r, h_both⟩ := h_f.and h_sh_rink (h_g (M / (-c)) (div_pos h_M h_cpos))
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_neg : f x < 0 := lt_trans h_result.1 h_c
  have h_1 := mul_lt_mul_of_pos_right h_result.1 (lt_trans (div_pos h_M h_cpos) h_result.2)
  have h_2 := mul_lt_mul_of_neg_left h_result.2 h_c
  have h_eq : c * (M / (-c)) = -M := by field [ne_of_lt h_c]
  nlinarith

private theorem eventuallyNegMulNeg {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {c : ℝ} (h_c : c < 0)
    (h_f : EventuallyAt S good fun x => f x < c)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => g x < -M) :
    ∀ M > 0, EventuallyAt S good fun x => f x * g x > M := by
  intro M h_M
  have h_cpos : 0 < -c := neg_pos.mpr h_c
  obtain ⟨r, h_r, h_both⟩ := h_f.and h_sh_rink (h_g (M / (-c)) (div_pos h_M h_cpos))
  exists r with h_r
  intro x h_x
  have h_result := h_both x h_x
  have h_fneg : f x < 0 := lt_trans h_result.1 h_c
  have h_gneg : g x < 0 := lt_trans h_result.2 (neg_lt_zero.mpr (div_pos h_M h_cpos))
  have h_1 := mul_lt_mul_of_neg_right h_result.1 h_gneg
  have h_2 := mul_lt_mul_of_neg_left h_result.2 h_c
  have h_eq : c * (-(M / (-c))) = M := by field [ne_of_lt h_c]
  nlinarith

private theorem eventuallyAbsMulInfty {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ} {c : ℝ} (h_c : 0 < c)
    (h_f : EventuallyAt S good fun x => c < |f x|)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => |g x| > M) :
    ∀ M > 0, EventuallyAt S good fun x => |f x * g x| > M := by
  intro M h_M
  obtain ⟨r, h_r, h_both⟩ := h_f.and h_sh_rink (h_g (M / c) (div_pos h_M h_c))
  exists r with h_r
  intro x h_x
  rw [abs_mul]
  have h_result := h_both x h_x
  calc
    M = c * (M / c) := by field
    _ < |f x| * |g x| := by nlinarith [h_result.1, h_result.2, abs_nonneg (f x), abs_nonneg (g x)]

private theorem eventuallyInftyMulInfty {α ρ : Type} {S : ρ → Set α}
    {good : ρ → Prop} (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    {f g : α → ℝ}
    (h_f : ∀ M > 0, EventuallyAt S good fun x => |f x| > M)
    (h_g : ∀ M > 0, EventuallyAt S good fun x => |g x| > M) :
    ∀ M > 0, EventuallyAt S good fun x => |f x * g x| > M := by
  intro M h_M
  exact eventuallyAbsMulInfty h_sh_rink (c := 1) (by norm_num)
    (h_f 1 (by norm_num)) h_g M h_M

private theorem genericMulDomain {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_F : EventuallyAt S good fun x => x ∈ F.domain)
    (h_G : EventuallyAt S good fun x => x ∈ G.domain) :
    EventuallyAt S good fun x => x ∈ (F * G).domain := by
  obtain ⟨r, h_r, h_dom⟩ := h_F.and h_sh_rink h_G
  exists r with h_r
  intro x h_x
  exact h_dom x h_x

private theorem function_mul_comm (F G : Function) : F * G = G * F := by
  apply Function.ext
  · funext x; exact mul_comm _ _
  · ext x; exact and_comm

private theorem sequence_mul_comm (A B : Sequence) : A * B = B * A := by
  apply Sequence.ext
  · funext n; exact mul_comm _ _
  · exact max_comm _ _
  · exact min_comm _ _

private theorem genericFiniteMulPosPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M)
    (h_L : 0 < L) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyPosMulPos h_sh_rink (c := L / 2) (by positivity)
      (finiteEventuallyPos h_F h_L) h_G⟩

private theorem genericFiniteMulPosNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M)
    (h_L : 0 < L) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x < -M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyPosMulNeg h_sh_rink (c := L / 2) (by positivity)
      (finiteEventuallyPos h_F h_L) h_G⟩

private theorem genericFiniteMulNegPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M)
    (h_L : L < 0) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x < -M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyNegMulPos h_sh_rink (c := L / 2) (by linarith)
      (finiteEventuallyNeg h_F h_L) h_G⟩

private theorem genericFiniteMulNegNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M)
    (h_L : L < 0) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyNegMulNeg h_sh_rink (c := L / 2) (by linarith)
      (finiteEventuallyNeg h_F h_L) h_G⟩

private theorem genericFiniteMulInfty {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ ε > 0, EventuallyAt S good fun x => F.map x ∈ Nbho L ε)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => |G.map x| > M)
    (h_L : L ≠ 0) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => |(F * G).map x| > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyAbsMulInfty h_sh_rink (c := |L| / 2) (by positivity)
      (finiteEventuallyAbsPos h_F h_L) h_G⟩

private theorem genericPosMulPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x > M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyPosMulPos h_sh_rink (c := 1) (by norm_num) (h_F 1 (by norm_num)) h_G⟩

private theorem genericPosMulNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x > M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x < -M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyPosMulNeg h_sh_rink (c := 1) (by norm_num) (h_F 1 (by norm_num)) h_G⟩

private theorem genericNegMulPos {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x < -M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x > M) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x < -M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyNegMulPos h_sh_rink (c := -1) (by norm_num) (h_F 1 (by norm_num)) h_G⟩

private theorem genericNegMulNeg {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => F.map x < -M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => G.map x < -M) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => (F * G).map x > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyNegMulNeg h_sh_rink (c := -1) (by norm_num) (h_F 1 (by norm_num)) h_G⟩

private theorem genericInftyMulInfty {ρ : Type} {S : ρ → Set ℝ} {good : ρ → Prop}
    (h_sh_rink : ∀ {r s}, good r → good s →
      ∃ t, good t ∧ S t ⊆ S r ∩ S s)
    (h_Fdom : EventuallyAt S good fun x => x ∈ F.domain)
    (h_Gdom : EventuallyAt S good fun x => x ∈ G.domain)
    (h_F : ∀ M > 0, EventuallyAt S good fun x => |F.map x| > M)
    (h_G : ∀ M > 0, EventuallyAt S good fun x => |G.map x| > M) :
    EventuallyAt S good (fun x => x ∈ (F * G).domain) ∧
      ∀ M > 0, EventuallyAt S good fun x => |(F * G).map x| > M := by
  exact ⟨genericMulDomain h_sh_rink h_Fdom h_Gdom,
    eventuallyInftyMulInfty h_sh_rink h_F h_G⟩

/- Sequence multiplication rules. -/

private abbrev SeqTail := fun N => {n : ℕ | n > N}
private abbrev SeqGood := fun (_ : ℕ) => True

private theorem seqFiniteMulPosPos (h_A : SeqLimit A L) (h_B : SeqLimitPosInfty B)
    (h_L : 0 < L) : ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n > M :=
  eventuallyPosMulPos (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := L / 2) (by positivity)
    (finiteEventuallyPos (by simpa [EventuallyAt] using h_A.2) h_L)
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqFiniteMulPosNeg (h_A : SeqLimit A L) (h_B : SeqLimitNegInfty B)
    (h_L : 0 < L) : ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n < -M :=
  eventuallyPosMulNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := L / 2) (by positivity)
    (finiteEventuallyPos (by simpa [EventuallyAt] using h_A.2) h_L)
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqFiniteMulNegPos (h_A : SeqLimit A L) (h_B : SeqLimitPosInfty B)
    (h_L : L < 0) : ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n < -M :=
  eventuallyNegMulPos (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := L / 2) (by linarith)
    (finiteEventuallyNeg (by simpa [EventuallyAt] using h_A.2) h_L)
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqFiniteMulNegNeg (h_A : SeqLimit A L) (h_B : SeqLimitNegInfty B)
    (h_L : L < 0) : ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n > M :=
  eventuallyNegMulNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := L / 2) (by linarith)
    (finiteEventuallyNeg (by simpa [EventuallyAt] using h_A.2) h_L)
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqFiniteMulAbs (h_A : SeqLimit A L) (h_B : SeqLimitInfty B)
    (h_L : L ≠ 0) : ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => |A.map n * B.map n| > M :=
  eventuallyAbsMulInfty (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := |L| / 2) (by positivity)
    (finiteEventuallyAbsPos (by simpa [EventuallyAt] using h_A.2) h_L)
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqPosMulPos (h_A : SeqLimitPosInfty A) (h_B : SeqLimitPosInfty B) :
    ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n > M :=
  eventuallyPosMulPos (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := 1) (by norm_num)
    (by simpa [EventuallyAt] using h_A.2 1 (by norm_num))
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqPosMulNeg (h_A : SeqLimitPosInfty A) (h_B : SeqLimitNegInfty B) :
    ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n < -M :=
  eventuallyPosMulNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := 1) (by norm_num)
    (by simpa [EventuallyAt] using h_A.2 1 (by norm_num))
    (by simpa [EventuallyAt] using h_B.2)

private theorem seqNegMulNeg (h_A : SeqLimitNegInfty A) (h_B : SeqLimitNegInfty B) :
    ∀ M > 0, EventuallyAt SeqTail SeqGood fun n => A.map n * B.map n > M :=
  eventuallyNegMulNeg (by
    intro r s h_r h_s
    exact natTailSh_rink) (c := -1) (by norm_num)
    (by simpa [EventuallyAt] using h_A.2 1 (by norm_num))
    (by simpa [EventuallyAt] using h_B.2)

theorem SeqLimit.MulPosInfty_of_pos (h_A : SeqLimit A L) (h_B : SeqLimitPosInfty B)
    (h_L : 0 < L) : SeqLimitPosInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqFiniteMulPosPos h_A h_B h_L M h_M
  exists N

theorem SeqLimit.MulNegInfty_of_pos (h_A : SeqLimit A L) (h_B : SeqLimitNegInfty B)
    (h_L : 0 < L) : SeqLimitNegInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqFiniteMulPosNeg h_A h_B h_L M h_M
  exists N

theorem SeqLimit.MulPosInfty_of_neg (h_A : SeqLimit A L) (h_B : SeqLimitPosInfty B)
    (h_L : L < 0) : SeqLimitNegInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqFiniteMulNegPos h_A h_B h_L M h_M
  exists N

theorem SeqLimit.MulNegInfty_of_neg (h_A : SeqLimit A L) (h_B : SeqLimitNegInfty B)
    (h_L : L < 0) : SeqLimitPosInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqFiniteMulNegNeg h_A h_B h_L M h_M
  exists N

theorem SeqLimit.MulInfty (h_A : SeqLimit A L) (h_B : SeqLimitInfty B)
    (h_L : L ≠ 0) : SeqLimitInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqFiniteMulAbs h_A h_B h_L M h_M
  exists N

theorem SeqLimitPosInfty.MulFinite_of_pos (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimit B L) (h_L : 0 < L) : SeqLimitPosInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulPosInfty_of_pos h_A h_L
theorem SeqLimitNegInfty.MulFinite_of_pos (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimit B L) (h_L : 0 < L) : SeqLimitNegInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulNegInfty_of_pos h_A h_L
theorem SeqLimitPosInfty.MulFinite_of_neg (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimit B L) (h_L : L < 0) : SeqLimitNegInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulPosInfty_of_neg h_A h_L
theorem SeqLimitNegInfty.MulFinite_of_neg (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimit B L) (h_L : L < 0) : SeqLimitPosInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulNegInfty_of_neg h_A h_L
theorem SeqLimitInfty.MulFinite (h_A : SeqLimitInfty A)
    (h_B : SeqLimit B L) (h_L : L ≠ 0) : SeqLimitInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulInfty h_A h_L

private theorem seqInftyMulInfty (h_A : SeqLimitInfty A) (h_B : SeqLimitInfty B) :
    SeqLimitInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := eventuallyInftyMulInfty (by
    intro r s h_r h_s
    exact natTailSh_rink)
    (by simpa [EventuallyAt] using h_A.2) (by simpa [EventuallyAt] using h_B.2) M h_M
  exists N

theorem SeqLimitPosInfty.MulPosInfty (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimitPosInfty B) : SeqLimitPosInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqPosMulPos h_A h_B M h_M
  exists N
theorem SeqLimitPosInfty.MulNegInfty (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimitNegInfty B) : SeqLimitNegInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqPosMulNeg h_A h_B M h_M
  exists N
theorem SeqLimitNegInfty.MulPosInfty (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimitPosInfty B) : SeqLimitNegInfty (A * B) := by
  rw [sequence_mul_comm]; exact h_B.MulNegInfty h_A
theorem SeqLimitNegInfty.MulNegInfty (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimitNegInfty B) : SeqLimitPosInfty (A * B) := by
  refine ⟨by change min A.final B.final = none; simp [h_A.1, h_B.1], ?_⟩
  intro M h_M
  obtain ⟨N, _, h_map⟩ := seqNegMulNeg h_A h_B M h_M
  exists N
theorem SeqLimitPosInfty.MulInfty (h_A : SeqLimitPosInfty A)
    (h_B : SeqLimitInfty B) : SeqLimitInfty (A * B) := seqInftyMulInfty h_A.toSeqLimitInfty h_B
theorem SeqLimitNegInfty.MulInfty (h_A : SeqLimitNegInfty A)
    (h_B : SeqLimitInfty B) : SeqLimitInfty (A * B) := seqInftyMulInfty h_A.toSeqLimitInfty h_B
theorem SeqLimitInfty.MulPosInfty (h_A : SeqLimitInfty A)
    (h_B : SeqLimitPosInfty B) : SeqLimitInfty (A * B) := seqInftyMulInfty h_A h_B.toSeqLimitInfty
theorem SeqLimitInfty.MulNegInfty (h_A : SeqLimitInfty A)
    (h_B : SeqLimitNegInfty B) : SeqLimitInfty (A * B) := seqInftyMulInfty h_A h_B.toSeqLimitInfty
theorem SeqLimitInfty.MulInfty (h_A : SeqLimitInfty A)
    (h_B : SeqLimitInfty B) : SeqLimitInfty (A * B) := seqInftyMulInfty h_A h_B

/- Multiplication rules for limits at a finite point. -/

theorem FuncLimit.MulPosInfty_of_pos (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitPosInfty G x₀) (h_L : 0 < L) : FuncLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericFiniteMulPosPos nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem FuncLimit.MulNegInfty_of_pos (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitNegInfty G x₀) (h_L : 0 < L) : FuncLimitNegInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericFiniteMulPosNeg nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem FuncLimit.MulPosInfty_of_neg (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitPosInfty G x₀) (h_L : L < 0) : FuncLimitNegInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericFiniteMulNegPos nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem FuncLimit.MulNegInfty_of_neg (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitNegInfty G x₀) (h_L : L < 0) : FuncLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericFiniteMulNegNeg nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem FuncLimit.MulInfty (h_F : FuncLimit F x₀ L)
    (h_G : FuncLimitInfty G x₀) (h_L : L ≠ 0) : FuncLimitInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericFiniteMulInfty nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem FuncLimitPosInfty.MulFinite_of_pos (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimit G x₀ L) (h_L : 0 < L) : FuncLimitPosInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem FuncLimitNegInfty.MulFinite_of_pos (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimit G x₀ L) (h_L : 0 < L) : FuncLimitNegInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem FuncLimitPosInfty.MulFinite_of_neg (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimit G x₀ L) (h_L : L < 0) : FuncLimitNegInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem FuncLimitNegInfty.MulFinite_of_neg (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimit G x₀ L) (h_L : L < 0) : FuncLimitPosInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem FuncLimitInfty.MulFinite (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimit G x₀ L) (h_L : L ≠ 0) : FuncLimitInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem FuncLimitPosInfty.MulPosInfty (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericPosMulPos nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem FuncLimitPosInfty.MulNegInfty (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitNegInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericPosMulNeg nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem FuncLimitNegInfty.MulPosInfty (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitNegInfty (F * G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem FuncLimitNegInfty.MulNegInfty (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericNegMulNeg nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
private theorem funcInftyMulInfty (h_F : FuncLimitInfty F x₀) (h_G : FuncLimitInfty G x₀) :
    FuncLimitInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Nbhd x₀ r) (fun r => r > 0) (fun x => x ∈ (F * G).domain) ∧ _
  exact genericInftyMulInfty nbhdTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem FuncLimitPosInfty.MulInfty (h_F : FuncLimitPosInfty F x₀)
    (h_G : FuncLimitInfty G x₀) : FuncLimitInfty (F * G) x₀ := funcInftyMulInfty h_F.toFuncLimitInfty h_G
theorem FuncLimitNegInfty.MulInfty (h_F : FuncLimitNegInfty F x₀)
    (h_G : FuncLimitInfty G x₀) : FuncLimitInfty (F * G) x₀ := funcInftyMulInfty h_F.toFuncLimitInfty h_G
theorem FuncLimitInfty.MulPosInfty (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimitPosInfty G x₀) : FuncLimitInfty (F * G) x₀ := funcInftyMulInfty h_F h_G.toFuncLimitInfty
theorem FuncLimitInfty.MulNegInfty (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimitNegInfty G x₀) : FuncLimitInfty (F * G) x₀ := funcInftyMulInfty h_F h_G.toFuncLimitInfty
theorem FuncLimitInfty.MulInfty (h_F : FuncLimitInfty F x₀)
    (h_G : FuncLimitInfty G x₀) : FuncLimitInfty (F * G) x₀ := funcInftyMulInfty h_F h_G

/- Left-limit multiplication rules. -/

theorem LeftLimit.MulPosInfty_of_pos (h_F : LeftLimit F x₀ L) (h_G : LeftLimitPosInfty G x₀)
    (h_L : 0 < L) : LeftLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericFiniteMulPosPos leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem LeftLimit.MulNegInfty_of_pos (h_F : LeftLimit F x₀ L) (h_G : LeftLimitNegInfty G x₀)
    (h_L : 0 < L) : LeftLimitNegInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericFiniteMulPosNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem LeftLimit.MulPosInfty_of_neg (h_F : LeftLimit F x₀ L) (h_G : LeftLimitPosInfty G x₀)
    (h_L : L < 0) : LeftLimitNegInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericFiniteMulNegPos leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem LeftLimit.MulNegInfty_of_neg (h_F : LeftLimit F x₀ L) (h_G : LeftLimitNegInfty G x₀)
    (h_L : L < 0) : LeftLimitPosInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericFiniteMulNegNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem LeftLimit.MulInfty (h_F : LeftLimit F x₀ L) (h_G : LeftLimitInfty G x₀)
    (h_L : L ≠ 0) : LeftLimitInfty (F * G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericFiniteMulInfty leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem LeftLimitPosInfty.MulFinite_of_pos (h_F : LeftLimitPosInfty F x₀) (h_G : LeftLimit G x₀ L)
    (h_L : 0<L) : LeftLimitPosInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem LeftLimitNegInfty.MulFinite_of_pos (h_F : LeftLimitNegInfty F x₀) (h_G : LeftLimit G x₀ L)
    (h_L : 0<L) : LeftLimitNegInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem LeftLimitPosInfty.MulFinite_of_neg (h_F : LeftLimitPosInfty F x₀) (h_G : LeftLimit G x₀ L)
    (h_L : L<0) : LeftLimitNegInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem LeftLimitNegInfty.MulFinite_of_neg (h_F : LeftLimitNegInfty F x₀) (h_G : LeftLimit G x₀ L)
    (h_L : L<0) : LeftLimitPosInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem LeftLimitInfty.MulFinite (h_F : LeftLimitInfty F x₀) (h_G : LeftLimit G x₀ L)
    (h_L : L≠0) : LeftLimitInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem LeftLimitPosInfty.MulPosInfty (h_F : LeftLimitPosInfty F x₀) (h_G : LeftLimitPosInfty G x₀) : LeftLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericPosMulPos leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem LeftLimitPosInfty.MulNegInfty (h_F : LeftLimitPosInfty F x₀) (h_G : LeftLimitNegInfty G x₀) : LeftLimitNegInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericPosMulNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem LeftLimitNegInfty.MulPosInfty (h_F : LeftLimitNegInfty F x₀) (h_G : LeftLimitPosInfty G x₀) : LeftLimitNegInfty (F*G) x₀ := by
  rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem LeftLimitNegInfty.MulNegInfty (h_F : LeftLimitNegInfty F x₀) (h_G : LeftLimitNegInfty G x₀) : LeftLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericNegMulNeg leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
private theorem leftInftyMulInfty (h_F : LeftLimitInfty F x₀) (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo (x₀-r) x₀) (fun r => r>0) (fun x => x ∈ (F*G).domain) ∧ _
  exact genericInftyMulInfty leftTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem LeftLimitPosInfty.MulInfty (h_F : LeftLimitPosInfty F x₀) (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F*G) x₀ := leftInftyMulInfty h_F.toLeftLimitInfty h_G
theorem LeftLimitNegInfty.MulInfty (h_F : LeftLimitNegInfty F x₀) (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F*G) x₀ := leftInftyMulInfty h_F.toLeftLimitInfty h_G
theorem LeftLimitInfty.MulPosInfty (h_F : LeftLimitInfty F x₀) (h_G : LeftLimitPosInfty G x₀) : LeftLimitInfty (F*G) x₀ := leftInftyMulInfty h_F h_G.toLeftLimitInfty
theorem LeftLimitInfty.MulNegInfty (h_F : LeftLimitInfty F x₀) (h_G : LeftLimitNegInfty G x₀) : LeftLimitInfty (F*G) x₀ := leftInftyMulInfty h_F h_G.toLeftLimitInfty
theorem LeftLimitInfty.MulInfty (h_F : LeftLimitInfty F x₀) (h_G : LeftLimitInfty G x₀) : LeftLimitInfty (F*G) x₀ := leftInftyMulInfty h_F h_G

/- Right-limit multiplication rules. -/

theorem RightLimit.MulPosInfty_of_pos (h_F : RightLimit F x₀ L) (h_G : RightLimitPosInfty G x₀) (h_L : 0<L) : RightLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosPos rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem RightLimit.MulNegInfty_of_pos (h_F : RightLimit F x₀ L) (h_G : RightLimitNegInfty G x₀) (h_L : 0<L) : RightLimitNegInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem RightLimit.MulPosInfty_of_neg (h_F : RightLimit F x₀ L) (h_G : RightLimitPosInfty G x₀) (h_L : L<0) : RightLimitNegInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegPos rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem RightLimit.MulNegInfty_of_neg (h_F : RightLimit F x₀ L) (h_G : RightLimitNegInfty G x₀) (h_L : L<0) : RightLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem RightLimit.MulInfty (h_F : RightLimit F x₀ L) (h_G : RightLimitInfty G x₀) (h_L : L≠0) : RightLimitInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulInfty rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem RightLimitPosInfty.MulFinite_of_pos (h_F : RightLimitPosInfty F x₀) (h_G : RightLimit G x₀ L) (h_L : 0<L) : RightLimitPosInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem RightLimitNegInfty.MulFinite_of_pos (h_F : RightLimitNegInfty F x₀) (h_G : RightLimit G x₀ L) (h_L : 0<L) : RightLimitNegInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem RightLimitPosInfty.MulFinite_of_neg (h_F : RightLimitPosInfty F x₀) (h_G : RightLimit G x₀ L) (h_L : L<0) : RightLimitNegInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem RightLimitNegInfty.MulFinite_of_neg (h_F : RightLimitNegInfty F x₀) (h_G : RightLimit G x₀ L) (h_L : L<0) : RightLimitPosInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem RightLimitInfty.MulFinite (h_F : RightLimitInfty F x₀) (h_G : RightLimit G x₀ L) (h_L : L≠0) : RightLimitInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem RightLimitPosInfty.MulPosInfty (h_F : RightLimitPosInfty F x₀) (h_G : RightLimitPosInfty G x₀) : RightLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulPos rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem RightLimitPosInfty.MulNegInfty (h_F : RightLimitPosInfty F x₀) (h_G : RightLimitNegInfty G x₀) : RightLimitNegInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem RightLimitNegInfty.MulPosInfty (h_F : RightLimitNegInfty F x₀) (h_G : RightLimitPosInfty G x₀) : RightLimitNegInfty (F*G) x₀ := by rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem RightLimitNegInfty.MulNegInfty (h_F : RightLimitNegInfty F x₀) (h_G : RightLimitNegInfty G x₀) : RightLimitPosInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericNegMulNeg rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
private theorem rightInftyMulInfty (h_F : RightLimitInfty F x₀) (h_G : RightLimitInfty G x₀) : RightLimitInfty (F*G) x₀ := by
  change EventuallyAt (fun r => Ioo x₀ (x₀+r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericInftyMulInfty rightTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem RightLimitPosInfty.MulInfty (h_F : RightLimitPosInfty F x₀) (h_G : RightLimitInfty G x₀) : RightLimitInfty (F*G) x₀ := rightInftyMulInfty h_F.toRightLimitInfty h_G
theorem RightLimitNegInfty.MulInfty (h_F : RightLimitNegInfty F x₀) (h_G : RightLimitInfty G x₀) : RightLimitInfty (F*G) x₀ := rightInftyMulInfty h_F.toRightLimitInfty h_G
theorem RightLimitInfty.MulPosInfty (h_F : RightLimitInfty F x₀) (h_G : RightLimitPosInfty G x₀) : RightLimitInfty (F*G) x₀ := rightInftyMulInfty h_F h_G.toRightLimitInfty
theorem RightLimitInfty.MulNegInfty (h_F : RightLimitInfty F x₀) (h_G : RightLimitNegInfty G x₀) : RightLimitInfty (F*G) x₀ := rightInftyMulInfty h_F h_G.toRightLimitInfty
theorem RightLimitInfty.MulInfty (h_F : RightLimitInfty F x₀) (h_G : RightLimitInfty G x₀) : RightLimitInfty (F*G) x₀ := rightInftyMulInfty h_F h_G

/- Multiplication rules at positive infinity. -/

theorem PosInftyLimit.MulPosInfty_of_pos (h_F : PosInftyLimit F L) (h_G : PosInftyLimitPosInfty G) (h_L : 0<L) : PosInftyLimitPosInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosPos posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem PosInftyLimit.MulNegInfty_of_pos (h_F : PosInftyLimit F L) (h_G : PosInftyLimitNegInfty G) (h_L : 0<L) : PosInftyLimitNegInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem PosInftyLimit.MulPosInfty_of_neg (h_F : PosInftyLimit F L) (h_G : PosInftyLimitPosInfty G) (h_L : L<0) : PosInftyLimitNegInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegPos posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem PosInftyLimit.MulNegInfty_of_neg (h_F : PosInftyLimit F L) (h_G : PosInftyLimitNegInfty G) (h_L : L<0) : PosInftyLimitPosInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem PosInftyLimit.MulInfty (h_F : PosInftyLimit F L) (h_G : PosInftyLimitInfty G) (h_L : L≠0) : PosInftyLimitInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulInfty posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem PosInftyLimitPosInfty.MulFinite_of_pos (h_F : PosInftyLimitPosInfty F) (h_G : PosInftyLimit G L) (h_L : 0<L) : PosInftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem PosInftyLimitNegInfty.MulFinite_of_pos (h_F : PosInftyLimitNegInfty F) (h_G : PosInftyLimit G L) (h_L : 0<L) : PosInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem PosInftyLimitPosInfty.MulFinite_of_neg (h_F : PosInftyLimitPosInfty F) (h_G : PosInftyLimit G L) (h_L : L<0) : PosInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem PosInftyLimitNegInfty.MulFinite_of_neg (h_F : PosInftyLimitNegInfty F) (h_G : PosInftyLimit G L) (h_L : L<0) : PosInftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem PosInftyLimitInfty.MulFinite (h_F : PosInftyLimitInfty F) (h_G : PosInftyLimit G L) (h_L : L≠0) : PosInftyLimitInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem PosInftyLimitPosInfty.MulPosInfty (h_F : PosInftyLimitPosInfty F) (h_G : PosInftyLimitPosInfty G) : PosInftyLimitPosInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulPos posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem PosInftyLimitPosInfty.MulNegInfty (h_F : PosInftyLimitPosInfty F) (h_G : PosInftyLimitNegInfty G) : PosInftyLimitNegInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem PosInftyLimitNegInfty.MulPosInfty (h_F : PosInftyLimitNegInfty F) (h_G : PosInftyLimitPosInfty G) : PosInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem PosInftyLimitNegInfty.MulNegInfty (h_F : PosInftyLimitNegInfty F) (h_G : PosInftyLimitNegInfty G) : PosInftyLimitPosInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericNegMulNeg posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
private theorem posAtInftyMulInfty (h_F : PosInftyLimitInfty F) (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F*G) := by
  change EventuallyAt Ioi (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericInftyMulInfty posInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem PosInftyLimitPosInfty.MulInfty (h_F : PosInftyLimitPosInfty F) (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F*G) := posAtInftyMulInfty h_F.toPosInftyLimitInfty h_G
theorem PosInftyLimitNegInfty.MulInfty (h_F : PosInftyLimitNegInfty F) (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F*G) := posAtInftyMulInfty h_F.toPosInftyLimitInfty h_G
theorem PosInftyLimitInfty.MulPosInfty (h_F : PosInftyLimitInfty F) (h_G : PosInftyLimitPosInfty G) : PosInftyLimitInfty (F*G) := posAtInftyMulInfty h_F h_G.toPosInftyLimitInfty
theorem PosInftyLimitInfty.MulNegInfty (h_F : PosInftyLimitInfty F) (h_G : PosInftyLimitNegInfty G) : PosInftyLimitInfty (F*G) := posAtInftyMulInfty h_F h_G.toPosInftyLimitInfty
theorem PosInftyLimitInfty.MulInfty (h_F : PosInftyLimitInfty F) (h_G : PosInftyLimitInfty G) : PosInftyLimitInfty (F*G) := posAtInftyMulInfty h_F h_G

/- Multiplication rules at negative infinity. -/

theorem NegInftyLimit.MulPosInfty_of_pos (h_F : NegInftyLimit F L) (h_G : NegInftyLimitPosInfty G) (h_L : 0<L) : NegInftyLimitPosInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosPos negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem NegInftyLimit.MulNegInfty_of_pos (h_F : NegInftyLimit F L) (h_G : NegInftyLimitNegInfty G) (h_L : 0<L) : NegInftyLimitNegInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulPosNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem NegInftyLimit.MulPosInfty_of_neg (h_F : NegInftyLimit F L) (h_G : NegInftyLimitPosInfty G) (h_L : L<0) : NegInftyLimitNegInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegPos negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem NegInftyLimit.MulNegInfty_of_neg (h_F : NegInftyLimit F L) (h_G : NegInftyLimitNegInfty G) (h_L : L<0) : NegInftyLimitPosInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulNegNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem NegInftyLimit.MulInfty (h_F : NegInftyLimit F L) (h_G : NegInftyLimitInfty G) (h_L : L≠0) : NegInftyLimitInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericFiniteMulInfty negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2 h_L
theorem NegInftyLimitPosInfty.MulFinite_of_pos (h_F : NegInftyLimitPosInfty F) (h_G : NegInftyLimit G L) (h_L : 0<L) : NegInftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem NegInftyLimitNegInfty.MulFinite_of_pos (h_F : NegInftyLimitNegInfty F) (h_G : NegInftyLimit G L) (h_L : 0<L) : NegInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem NegInftyLimitPosInfty.MulFinite_of_neg (h_F : NegInftyLimitPosInfty F) (h_G : NegInftyLimit G L) (h_L : L<0) : NegInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem NegInftyLimitNegInfty.MulFinite_of_neg (h_F : NegInftyLimitNegInfty F) (h_G : NegInftyLimit G L) (h_L : L<0) : NegInftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem NegInftyLimitInfty.MulFinite (h_F : NegInftyLimitInfty F) (h_G : NegInftyLimit G L) (h_L : L≠0) : NegInftyLimitInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem NegInftyLimitPosInfty.MulPosInfty (h_F : NegInftyLimitPosInfty F) (h_G : NegInftyLimitPosInfty G) : NegInftyLimitPosInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulPos negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem NegInftyLimitPosInfty.MulNegInfty (h_F : NegInftyLimitPosInfty F) (h_G : NegInftyLimitNegInfty G) : NegInftyLimitNegInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericPosMulNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem NegInftyLimitNegInfty.MulPosInfty (h_F : NegInftyLimitNegInfty F) (h_G : NegInftyLimitPosInfty G) : NegInftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem NegInftyLimitNegInfty.MulNegInfty (h_F : NegInftyLimitNegInfty F) (h_G : NegInftyLimitNegInfty G) : NegInftyLimitPosInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericNegMulNeg negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
private theorem negAtInftyMulInfty (h_F : NegInftyLimitInfty F) (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F*G) := by
  change EventuallyAt (fun r => Iio (-r)) (fun r => r>0) (fun x => x∈(F*G).domain) ∧ _; exact genericInftyMulInfty negInftyTailSh_rink h_F.1 h_G.1 h_F.2 h_G.2
theorem NegInftyLimitPosInfty.MulInfty (h_F : NegInftyLimitPosInfty F) (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F*G) := negAtInftyMulInfty h_F.toNegInftyLimitInfty h_G
theorem NegInftyLimitNegInfty.MulInfty (h_F : NegInftyLimitNegInfty F) (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F*G) := negAtInftyMulInfty h_F.toNegInftyLimitInfty h_G
theorem NegInftyLimitInfty.MulPosInfty (h_F : NegInftyLimitInfty F) (h_G : NegInftyLimitPosInfty G) : NegInftyLimitInfty (F*G) := negAtInftyMulInfty h_F h_G.toNegInftyLimitInfty
theorem NegInftyLimitInfty.MulNegInfty (h_F : NegInftyLimitInfty F) (h_G : NegInftyLimitNegInfty G) : NegInftyLimitInfty (F*G) := negAtInftyMulInfty h_F h_G.toNegInftyLimitInfty
theorem NegInftyLimitInfty.MulInfty (h_F : NegInftyLimitInfty F) (h_G : NegInftyLimitInfty G) : NegInftyLimitInfty (F*G) := negAtInftyMulInfty h_F h_G

/- Multiplication rules for two-sided limits at infinity. -/

private theorem inftyPosResult
    (h_dom : EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => x ∈ (F * G).domain)
    (h_map : ∀ M > 0, EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => (F * G).map x > M) : InftyLimitPosInfty (F * G) :=
  ⟨unionDomainToInfty h_dom, h_map⟩

private theorem inftyNegResult
    (h_dom : EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => x ∈ (F * G).domain)
    (h_map : ∀ M > 0, EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => (F * G).map x < -M) : InftyLimitNegInfty (F * G) :=
  ⟨unionDomainToInfty h_dom, h_map⟩

private theorem inftyAbsResult
    (h_dom : EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => x ∈ (F * G).domain)
    (h_map : ∀ M > 0, EventuallyAt (fun r => Ioi r ∪ Iio (-r)) (fun r => r > 0)
      fun x => |(F * G).map x| > M) : InftyLimitInfty (F * G) :=
  ⟨unionDomainToInfty h_dom, h_map⟩

theorem InftyLimit.MulPosInfty_of_pos (h_F : InftyLimit F L) (h_G : InftyLimitPosInfty G)
    (h_L : 0<L) : InftyLimitPosInfty (F*G) := by
  have h_result := genericFiniteMulPosPos inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2 h_L
  exact inftyPosResult h_result.1 h_result.2
theorem InftyLimit.MulNegInfty_of_pos (h_F : InftyLimit F L) (h_G : InftyLimitNegInfty G)
    (h_L : 0<L) : InftyLimitNegInfty (F*G) := by
  have h_result := genericFiniteMulPosNeg inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2 h_L
  exact inftyNegResult h_result.1 h_result.2
theorem InftyLimit.MulPosInfty_of_neg (h_F : InftyLimit F L) (h_G : InftyLimitPosInfty G)
    (h_L : L<0) : InftyLimitNegInfty (F*G) := by
  have h_result := genericFiniteMulNegPos inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2 h_L
  exact inftyNegResult h_result.1 h_result.2
theorem InftyLimit.MulNegInfty_of_neg (h_F : InftyLimit F L) (h_G : InftyLimitNegInfty G)
    (h_L : L<0) : InftyLimitPosInfty (F*G) := by
  have h_result := genericFiniteMulNegNeg inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2 h_L
  exact inftyPosResult h_result.1 h_result.2
theorem InftyLimit.MulInfty (h_F : InftyLimit F L) (h_G : InftyLimitInfty G)
    (h_L : L≠0) : InftyLimitInfty (F*G) := by
  have h_result := genericFiniteMulInfty inftyTailSh_rink (inftyFiniteAsUnion h_F).1
    (inftyDomainAsUnion h_G.1) (inftyFiniteAsUnion h_F).2 h_G.2 h_L
  exact inftyAbsResult h_result.1 h_result.2
theorem InftyLimitPosInfty.MulFinite_of_pos (h_F : InftyLimitPosInfty F) (h_G : InftyLimit G L)
    (h_L : 0<L) : InftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_pos h_F h_L
theorem InftyLimitNegInfty.MulFinite_of_pos (h_F : InftyLimitNegInfty F) (h_G : InftyLimit G L)
    (h_L : 0<L) : InftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_pos h_F h_L
theorem InftyLimitPosInfty.MulFinite_of_neg (h_F : InftyLimitPosInfty F) (h_G : InftyLimit G L)
    (h_L : L<0) : InftyLimitNegInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulPosInfty_of_neg h_F h_L
theorem InftyLimitNegInfty.MulFinite_of_neg (h_F : InftyLimitNegInfty F) (h_G : InftyLimit G L)
    (h_L : L<0) : InftyLimitPosInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulNegInfty_of_neg h_F h_L
theorem InftyLimitInfty.MulFinite (h_F : InftyLimitInfty F) (h_G : InftyLimit G L)
    (h_L : L≠0) : InftyLimitInfty (F*G) := by rw [function_mul_comm]; exact h_G.MulInfty h_F h_L
theorem InftyLimitPosInfty.MulPosInfty (h_F : InftyLimitPosInfty F) (h_G : InftyLimitPosInfty G) : InftyLimitPosInfty (F*G) := by
  have h_result := genericPosMulPos inftyTailSh_rink (inftyDomainAsUnion h_F.1) (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact inftyPosResult h_result.1 h_result.2
theorem InftyLimitPosInfty.MulNegInfty (h_F : InftyLimitPosInfty F) (h_G : InftyLimitNegInfty G) : InftyLimitNegInfty (F*G) := by
  have h_result := genericPosMulNeg inftyTailSh_rink (inftyDomainAsUnion h_F.1) (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact inftyNegResult h_result.1 h_result.2
theorem InftyLimitNegInfty.MulPosInfty (h_F : InftyLimitNegInfty F) (h_G : InftyLimitPosInfty G) : InftyLimitNegInfty (F*G) := by
  rw [function_mul_comm]; exact h_G.MulNegInfty h_F
theorem InftyLimitNegInfty.MulNegInfty (h_F : InftyLimitNegInfty F) (h_G : InftyLimitNegInfty G) : InftyLimitPosInfty (F*G) := by
  have h_result := genericNegMulNeg inftyTailSh_rink (inftyDomainAsUnion h_F.1) (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact inftyPosResult h_result.1 h_result.2
private theorem twoSidedInftyMulInfty (h_F : InftyLimitInfty F) (h_G : InftyLimitInfty G) : InftyLimitInfty (F*G) := by
  have h_result := genericInftyMulInfty inftyTailSh_rink (inftyDomainAsUnion h_F.1) (inftyDomainAsUnion h_G.1) h_F.2 h_G.2
  exact inftyAbsResult h_result.1 h_result.2
theorem InftyLimitPosInfty.MulInfty (h_F : InftyLimitPosInfty F) (h_G : InftyLimitInfty G) : InftyLimitInfty (F*G) := twoSidedInftyMulInfty h_F.toInftyLimitInfty h_G
theorem InftyLimitNegInfty.MulInfty (h_F : InftyLimitNegInfty F) (h_G : InftyLimitInfty G) : InftyLimitInfty (F*G) := twoSidedInftyMulInfty h_F.toInftyLimitInfty h_G
theorem InftyLimitInfty.MulPosInfty (h_F : InftyLimitInfty F) (h_G : InftyLimitPosInfty G) : InftyLimitInfty (F*G) := twoSidedInftyMulInfty h_F h_G.toInftyLimitInfty
theorem InftyLimitInfty.MulNegInfty (h_F : InftyLimitInfty F) (h_G : InftyLimitNegInfty G) : InftyLimitInfty (F*G) := twoSidedInftyMulInfty h_F h_G.toInftyLimitInfty
theorem InftyLimitInfty.MulInfty (h_F : InftyLimitInfty F) (h_G : InftyLimitInfty G) : InftyLimitInfty (F*G) := twoSidedInftyMulInfty h_F h_G

end InfiniteLimitRules


page_end
