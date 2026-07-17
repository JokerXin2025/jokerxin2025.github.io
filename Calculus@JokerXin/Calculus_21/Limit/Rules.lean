/-
    Calculus_21.Limit.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr
set_option linter.style.header false


/-! # Basic Limits -/

/-! For more limits, please refer to `Continuity.Elementary`. -/


/-! # Limit Calculation Rules -/

/-!
The rules for __Function's Multiplicative Scalar Power__ are not provided here,
which can be regarded as a composite function by the following conclusion:
```lean
example {f : ℝ → ℝ} {n : ℕ} : f ^ n = npow n ∘ f := rfl
```
-/

lemma nbho_abs {x L ε : ℝ}
  : x ∈ Nbho L ε ↔ |x - L| < ε
:= by
  dsimp [Nbho]
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> linarith

lemma smul_helper {x L k ε : ℝ}
    (h : |x - L| < ε / (|k| + 1))
  : |k * x - k * L| < ε
:= by
  have hk : 0 < |k| + 1 := by positivity
  have h1 : |k| * |x - L| ≤ (|k| + 1) * |x - L| := by
    apply mul_le_mul_of_nonneg_right
    · linarith
    · exact abs_nonneg _
  have h2 : (|k| + 1) * |x - L| < (|k| + 1) * (ε / (|k| + 1)) := mul_lt_mul_of_pos_left h hk
  have h3 : (|k| + 1) * (ε / (|k| + 1)) = ε := by
    calc (|k| + 1) * (ε / (|k| + 1))
      _ = (|k| + 1) * (ε * (|k| + 1)⁻¹) := by rw [div_eq_mul_inv]
      _ = (|k| + 1) * (|k| + 1)⁻¹ * ε := by ring
      _ = 1 * ε := by rw [mul_inv_cancel₀ (ne_of_gt hk)]
      _ = ε := by ring
  calc |k * x - k * L| = |k| * |x - L| := by rw [← mul_sub, abs_mul]
    _ ≤ (|k| + 1) * |x - L| := h1
    _ < (|k| + 1) * (ε / (|k| + 1)) := h2
    _ = ε := h3


lemma neg_helper {x L ε : ℝ}
    (h : |x - L| < ε)
  : |-x - -L| < ε
:= by
  calc |-x - -L| = |x - L| := by rw [← abs_neg, neg_sub, sub_neg_eq_add, neg_add_eq_sub]
    _ < ε := h

lemma add_helper {x y L M ε : ℝ}
    (hx : |x - L| < ε / 2) (hy : |y - M| < ε / 2)
  : |x + y - (L + M)| < ε
:= by
  calc |x + y - (L + M)| = |(x - L) + (y - M)| := by congr 1; ring
    _ ≤ |x - L| + |y - M| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hx hy
    _ = ε := add_halves ε

lemma sub_helper {x y L M ε : ℝ}
    (hx : |x - L| < ε / 2) (hy : |y - M| < ε / 2)
  : |x - y - (L - M)| < ε
:= by
  calc |x - y - (L - M)| = |(x - L) - (y - M)| := by congr 1; ring
    _ ≤ |x - L| + |y - M| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hx hy
    _ = ε := add_halves ε

lemma mul_helper {x y L M ε : ℝ} (hx1 : |x - L| < 1)
    (hx2 : |x - L| < ε / (2 * (|M| + 1)))
    (hy : |y - M| < ε / (2 * (|L| + 2))) (hε : 0 < ε)
  : |x * y - L * M| < ε
:= by
  have b1 : 0 < |L| + 2 := by positivity
  have b2 : 0 < |M| + 1 := by positivity
  have b1_pos : 0 < 2 * (|L| + 2) := by positivity
  have b2_pos : 0 < 2 * (|M| + 1) := by positivity
  have Hx : |x| ≤ |L| + 1 := by
    have h1 : x - L ≤ |x - L| := le_abs_self (x - L)
    have h2 : -(x - L) ≤ |x - L| := neg_le_abs (x - L)
    have h3 : L ≤ |L| := le_abs_self L
    have h4 : -L ≤ |L| := neg_le_abs L
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have T1 : |x| * |y - M| ≤ (|L| + 1) * |y - M| := mul_le_mul_of_nonneg_right Hx (abs_nonneg _)
  have T2 : (|L| + 1) * |y - M| < (|L| + 2) * (ε / (2 * (|L| + 2))) := by
    have step1 : (|L| + 1) * |y - M| ≤ (|L| + 1) * (ε / (2 * (|L| + 2))) :=
      mul_le_mul_of_nonneg_left (le_of_lt hy) (by positivity)
    have step2 : (|L| + 1) * (ε / (2 * (|L| + 2))) < (|L| + 2) * (ε / (2 * (|L| + 2))) :=
      mul_lt_mul_of_pos_right (by linarith) (div_pos hε b1_pos)
    exact step1.trans_lt step2
  have T3 : |M| * |x - L| ≤ |M| * (ε / (2 * (|M| + 1))) :=
    mul_le_mul_of_nonneg_left (le_of_lt hx2) (abs_nonneg _)
  have T4 : |M| * (ε / (2 * (|M| + 1))) < (|M| + 1) * (ε / (2 * (|M| + 1))) :=
    mul_lt_mul_of_pos_right (by linarith) (div_pos hε b2_pos)
  have eq1 : (|L| + 2) * (ε / (2 * (|L| + 2))) = ε / 2 := by
    calc (|L| + 2) * (ε / (2 * (|L| + 2)))
      _ = (|L| + 2) * (ε * (2 * (|L| + 2))⁻¹) := by rw [div_eq_mul_inv]
      _ = (|L| + 2) * (ε * (2⁻¹ * (|L| + 2)⁻¹)) := by rw [mul_inv]
      _ = (|L| + 2) * (|L| + 2)⁻¹ * (ε * 2⁻¹) := by ring
      _ = 1 * (ε * 2⁻¹) := by rw [mul_inv_cancel₀ (ne_of_gt b1)]
      _ = ε / 2 := by ring
  have eq2 : (|M| + 1) * (ε / (2 * (|M| + 1))) = ε / 2 := by
    calc (|M| + 1) * (ε / (2 * (|M| + 1)))
      _ = (|M| + 1) * (ε * (2 * (|M| + 1))⁻¹) := by rw [div_eq_mul_inv]
      _ = (|M| + 1) * (ε * (2⁻¹ * (|M| + 1)⁻¹)) := by rw [mul_inv]
      _ = (|M| + 1) * (|M| + 1)⁻¹ * (ε * 2⁻¹) := by ring
      _ = 1 * (ε * 2⁻¹) := by rw [mul_inv_cancel₀ (ne_of_gt b2)]
      _ = ε / 2 := by ring
  calc |x * y - L * M| = |x * (y - M) + M * (x - L)| := by congr 1; ring
    _ ≤ |x| * |y - M| + |M| * |x - L| := by
      have a1 : x * (y - M) ≤ |x * (y - M)| := le_abs_self _
      have a2 : -(x * (y - M)) ≤ |x * (y - M)| := neg_le_abs _
      have a3 : M * (x - L) ≤ |M * (x - L)| := le_abs_self _
      have a4 : -(M * (x - L)) ≤ |M * (x - L)| := neg_le_abs _
      rw [abs_mul] at a1 a2 a3 a4
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    _ < (|L| + 2) * (ε / (2 * (|L| + 2))) + (|M| + 1) * (ε / (2 * (|M| + 1))) := add_lt_add (T1.trans_lt T2) (T3.trans_lt T4)
    _ = ε / 2 + ε / 2 := by rw [eq1, eq2]
    _ = ε := add_halves ε

lemma inv_helper {y M ε : ℝ}
    (h1 : |y - M| < |M| / 2) (h2 : |y - M| < ε) (hM : M ≠ 0) (hε : 0 < ε)
  : |y⁻¹ - M⁻¹| < ε * 2 / M^2
:= by
  have H1 : |M| / 2 < |y| := by
    have : |M| ≤ |y| + |y - M| := by
      calc |M| = |y + (M - y)| := by congr 1; ring
        _ ≤ |y| + |M - y| := abs_add_le y (M - y)
        _ = |y| + |y - M| := by rw [abs_sub_comm]
    linarith
  have hy : y ≠ 0 := by
    intro hZ
    rw [hZ, abs_zero] at H1
    have : 0 ≤ |M| / 2 := by positivity
    linarith
  have h_eq : y⁻¹ - M⁻¹ = (M - y) / (y * M) := by
    symm
    apply mul_right_cancel₀ (mul_ne_zero hy hM)
    calc (M - y) / (y * M) * (y * M) = M - y := div_mul_cancel₀ _ (mul_ne_zero hy hM)
      _ = y⁻¹ * y * M - y * (M⁻¹ * M) := by rw [inv_mul_cancel₀ hy, inv_mul_cancel₀ hM]; ring
      _ = (y⁻¹ - M⁻¹) * (y * M) := by ring
  calc |y⁻¹ - M⁻¹| = |(M - y) / (y * M)| := by rw [h_eq]
    _ = |y - M| / (|y| * |M|) := by rw [abs_div, abs_mul, abs_sub_comm]
    _ < ε / (|y| * |M|) := by
      have : 0 < (|y| * |M|)⁻¹ := inv_pos.mpr (by positivity)
      calc |y - M| / (|y| * |M|) = |y - M| * (|y| * |M|)⁻¹ := rfl
        _ < ε * (|y| * |M|)⁻¹ := mul_lt_mul_of_pos_right h2 this
        _ = ε / (|y| * |M|) := rfl
    _ < ε / ((|M| / 2) * |M|) := by
      have H2 : (|y| * |M|)⁻¹ < ((|M| / 2) * |M|)⁻¹ := by
        rw [inv_lt_inv₀ (by positivity) (by positivity)]
        exact mul_lt_mul_of_pos_right H1 (by positivity)
      calc ε / (|y| * |M|) = ε * (|y| * |M|)⁻¹ := rfl
        _ < ε * ((|M| / 2) * |M|)⁻¹ := mul_lt_mul_of_pos_left H2 hε
        _ = ε / ((|M| / 2) * |M|) := rfl
    _ = ε * 2 / M^2 := by
      have : (|M| / 2) * |M| = M^2 / 2 := by rw [sq, ←abs_mul_abs_self, mul_comm, mul_div_assoc]
      rw [this]
      ring

/-- Sequence Limit of Scalar Multiplication -/
theorem SeqLimit.SMul {A : Sequence} {k L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (k • A) (k * L₁)
:= by
  rcases h_A with ⟨hf, hE⟩
  refine ⟨hf, fun ε hε => ?_⟩
  rcases hE (ε / (|k| + 1)) (div_pos hε (by positivity)) with ⟨N, hN⟩
  exact ⟨N, fun n hn => nbho_abs.mpr (smul_helper (nbho_abs.mp (hN n hn)))⟩

/-- Sequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul {a : ℕ → ℝ} {k : ℝ}
  : limₙ (k • a) =? the k * limₙ a
:= by
  unfold UdEqual; cases h : limₙ a with | none => trivial | some L =>
  have h_lim := SeqLimitExpr_to_SeqLimit (init := 0) h
  exact SeqLimit_to_SeqLimitExpr (SeqLimit.SMul h_lim)

/-- Function Limit of Scalar Multiplication -/
theorem FuncLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (k • F) x₀ (k * L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE (ε / (|k| + 1)) (div_pos hε (by positivity)) with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd =>
          nbho_abs.mpr (smul_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Function Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim (k • f) x₀ =? the k * lim f x₀
:= by
  cases h : lim f x₀ with
  | none => trivial
  | some L =>
    change lim (k • f) x₀ = some (k * L)
    have hL := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact FuncLimit_to_FuncLimitExpr (FuncLimit.SMul hL)

/-- Left Limit of Scalar Multiplication -/
theorem LeftLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (k • F) x₀ (k * L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE (ε / (|k| + 1)) (div_pos hε (by positivity)) with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd =>
          nbho_abs.mpr (smul_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₋ (k • f) x₀ =? the k * lim₋ f x₀
:= by
  cases h : lim₋ f x₀ with
  | none => trivial
  | some L =>
    change lim₋ (k • f) x₀ = some (k * L)
    have hL := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact LeftLimit_to_LeftLimitExpr (LeftLimit.SMul hL)

/-- Right Limit of Scalar Multiplication -/
theorem RightLimit.SMul {F : Function} {k x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (k • F) x₀ (k * L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE (ε / (|k| + 1)) (div_pos hε (by positivity)) with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd =>
          nbho_abs.mpr (smul_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₊ (k • f) x₀ =? the k * lim₊ f x₀
:= by
  cases h : lim₊ f x₀ with
  | none => trivial
  | some L =>
    change lim₊ (k • f) x₀ = some (k * L)
    have hL := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact RightLimit_to_RightLimitExpr (RightLimit.SMul hL)

/-- Sequence Limit of Additive Inverse -/
theorem SeqLimit.Neg {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (-A) (-L₁)
:= by
  rcases h_A with ⟨hf, hE⟩
  refine ⟨hf, fun ε hε => ?_⟩
  rcases hE ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => nbho_abs.mpr (neg_helper (nbho_abs.mp (hN n hn)))⟩

/-- Sequence Limit of Additive Inverse (Expression) -/
theorem SeqLimitExpr.Neg {a : ℕ → ℝ}
  : limₙ (-a) =? - limₙ a
:= by
  cases h : limₙ a with | none => trivial | some L =>
  have h_lim := SeqLimitExpr_to_SeqLimit (init := 0) h
  exact SeqLimit_to_SeqLimitExpr (SeqLimit.Neg h_lim)

/-- Function Limit of Additive Inverse -/
theorem FuncLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit (-F) x₀ (-L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE ε hε with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd => nbho_abs.mpr (neg_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Function Limit of Additive Inverse (Expression) -/
theorem FuncLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim (-f) x₀ =? - lim f x₀
:= by
  cases h : lim f x₀ with
  | none => trivial
  | some L =>
    change lim (-f) x₀ = some (-L)
    have hL := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact FuncLimit_to_FuncLimitExpr (FuncLimit.Neg hL)

/-- Left Limit of Additive Inverse -/
theorem LeftLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit (-F) x₀ (-L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE ε hε with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd => nbho_abs.mpr (neg_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Left Limit of Additive Inverse (Expression) -/
theorem LeftLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (-f) x₀ =? - lim₋ f x₀
:= by
  cases h : lim₋ f x₀ with
  | none => trivial
  | some L =>
    change lim₋ (-f) x₀ = some (-L)
    have hL := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact LeftLimit_to_LeftLimitExpr (LeftLimit.Neg hL)

/-- Right Limit of Additive Inverse -/
theorem RightLimit.Neg {F : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit (-F) x₀ (-L₁)
:= by
  rcases h_F with ⟨hD, hE⟩
  refine ⟨hD, fun ε hε => ?_⟩
  rcases hE ε hε with ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun x hx_nbhd => nbho_abs.mpr (neg_helper (nbho_abs.mp (hx x hx_nbhd)))⟩

/-- Right Limit of Additive Inverse (Expression) -/
theorem RightLimitExpr.Neg {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (-f) x₀ =? - lim₊ f x₀
:= by
  cases h : lim₊ f x₀ with
  | none => trivial
  | some L =>
    change lim₊ (-f) x₀ = some (-L)
    have hL := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h
    exact RightLimit_to_RightLimitExpr (RightLimit.Neg hL)

/-- Sequence Limit of Multiplicative Scalar Power -/
theorem SeqLimit.MSPow {A : Sequence} {n : ℕ} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit (A ^ n) (L₁ ^ n)
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power (Expression) -/
theorem SeqLimitExpr.MSPow {a : ℕ → ℝ} {n : ℕ}
  : limₙ (a ^ n) =? limₙ a ^ the (n : ℝ)
:= sorry

/-- Sequence Limit of Multiplicative Inverse -/
theorem SeqLimit.Inv {A : Sequence} {L₁ : ℝ}
    (h_A : SeqLimit A L₁)
  : SeqLimit A⁻¹ L₁⁻¹
:= sorry

/-- Sequence Limit of Multiplicative Inverse (Expression) -/
theorem SeqLimitExpr.Inv {a : ℕ → ℝ}
  : limₙ a⁻¹ =? (limₙ a)⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse -/
theorem FuncLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : FuncLimit F x₀ L₁)
  : FuncLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse (Expression) -/
theorem FuncLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim f⁻¹ x₀ =? (lim f x₀)⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse -/
theorem LeftLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : LeftLimit F x₀ L₁)
  : LeftLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse (Expression) -/
theorem LeftLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f⁻¹ x₀ =? (lim₋ f x₀)⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse -/
theorem RightLimit.Inv {F : Function} {x₀ L₁ : ℝ}
    (h_F : RightLimit F x₀ L₁)
  : RightLimit F⁻¹ x₀ L₁⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse (Expression) -/
theorem RightLimitExpr.Inv {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f⁻¹ x₀ =? (lim₊ f x₀)⁻¹
:= sorry

/-- Sequence Limit Addition -/
theorem SeqLimit.Add {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A + B) (L₁ + L₂)
:= by
  rcases h_A with ⟨hfA, hEA⟩
  rcases h_B with ⟨hfB, hEB⟩
  refine ⟨by dsimp [HAdd.hAdd, Add.add]; rw [hfA, hfB]; rfl, fun ε hε => ?_⟩
  rcases hEA (ε / 2) (by positivity) with ⟨N1, hN1⟩
  rcases hEB (ε / 2) (by positivity) with ⟨N2, hN2⟩
  exact ⟨max N1 N2, fun n hn =>
          nbho_abs.mpr (add_helper (nbho_abs.mp (hN1 n (by omega)))
          (nbho_abs.mp (hN2 n (by omega))))⟩

/-- Sequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add {a b : ℕ → ℝ}
  : limₙ (a + b) =? limₙ a + limₙ b
:= by
  cases hA : limₙ a <;> cases hB : limₙ b <;> try trivial
  rename_i L1 L2
  have hL1 := SeqLimitExpr_to_SeqLimit (init := 0) hA
  have hL2 := SeqLimitExpr_to_SeqLimit (init := 0) hB
  exact SeqLimit_to_SeqLimitExpr (SeqLimit.Add hL1 hL2)


/-- Function Limit Addition -/
theorem FuncLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F + G) x₀ (L₁ + L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Nbhd] at hx
    exact ⟨hD1 ⟨by linarith, by linarith, hx.2.2⟩, hD2 ⟨by linarith, by linarith, hx.2.2⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Nbhd] at hx
    exact nbho_abs.mpr (add_helper
          (nbho_abs.mp (hE3 x ⟨by linarith, by linarith, hx.2.2⟩))
          (nbho_abs.mp (hE4 x ⟨by linarith, by linarith, hx.2.2⟩)))

/-- Function Limit Addition (Expression) -/
theorem FuncLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f + g) x₀ =? lim f x₀ + lim g x₀
:= by
  cases hA : lim f x₀ with | none => trivial | some L1 =>
  cases hB : lim g x₀ with | none => trivial | some L2 =>
    change lim (f + g) x₀ = some (L1 + L2)
    have hL1 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact FuncLimit_to_FuncLimitExpr (FuncLimit.Add hL1 hL2)

/-- Left Limit Addition -/
theorem LeftLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F + G) x₀ (L₁ + L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx; exact ⟨hD1 ⟨by linarith, hx.2⟩, hD2 ⟨by linarith, hx.2⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Ioo] at hx
    exact nbho_abs.mpr (add_helper (nbho_abs.mp (hE3 x ⟨by linarith, hx.2⟩))
          (nbho_abs.mp (hE4 x ⟨by linarith, hx.2⟩)))

/-- Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f + g) x₀ =? lim₋ f x₀ + lim₋ g x₀
:= by
  cases hA : lim₋ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₋ g x₀ with | none => trivial | some L2 =>
    change lim₋ (f + g) x₀ = some (L1 + L2)
    have hL1 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact LeftLimit_to_LeftLimitExpr (LeftLimit.Add hL1 hL2)

/-- Right Limit Addition -/
theorem RightLimit.Add {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F + G) x₀ (L₁ + L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx; exact ⟨hD1 ⟨hx.1, by linarith⟩, hD2 ⟨hx.1, by linarith⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Ioo] at hx
    exact nbho_abs.mpr (add_helper (nbho_abs.mp (hE3 x ⟨hx.1, by linarith⟩))
          (nbho_abs.mp (hE4 x ⟨hx.1, by linarith⟩)))

/-- Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f + g) x₀ =? lim₊ f x₀ + lim₊ g x₀
:= by
  cases hA : lim₊ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₊ g x₀ with | none => trivial | some L2 =>
    change lim₊ (f + g) x₀ = some (L1 + L2)
    have hL1 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact RightLimit_to_RightLimitExpr (RightLimit.Add hL1 hL2)

/-- Sequence Limit Subtraction -/
theorem SeqLimit.Sub {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A - B) (L₁ - L₂)
:= by
  rcases h_A with ⟨hfA, hEA⟩; rcases h_B with ⟨hfB, hEB⟩
  refine ⟨by dsimp [HSub.hSub, Sub.sub]; rw [hfA, hfB]; rfl, fun ε hε => ?_⟩
  rcases hEA (ε / 2) (by positivity) with ⟨N1, hN1⟩
  rcases hEB (ε / 2) (by positivity) with ⟨N2, hN2⟩
  exact ⟨max N1 N2, fun n hn =>
          nbho_abs.mpr (sub_helper (nbho_abs.mp (hN1 n (by omega)))
          (nbho_abs.mp (hN2 n (by omega))))⟩

/-- Sequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub {a b : ℕ → ℝ}
  : limₙ (a - b) =? limₙ a - limₙ b
:= by
  cases hA : limₙ a <;> cases hB : limₙ b <;> try trivial
  rename_i L1 L2
  have hL1 := SeqLimitExpr_to_SeqLimit (init := 0) hA
  have hL2 := SeqLimitExpr_to_SeqLimit (init := 0) hB
  exact SeqLimit_to_SeqLimitExpr (SeqLimit.Sub hL1 hL2)

/-- Function Limit Subtraction -/
theorem FuncLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F - G) x₀ (L₁ - L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Nbhd] at hx
    exact ⟨hD1 ⟨by linarith, by linarith, hx.2.2⟩, hD2 ⟨by linarith, by linarith, hx.2.2⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Nbhd] at hx
    exact nbho_abs.mpr (sub_helper
          (nbho_abs.mp (hE3 x ⟨by linarith, by linarith, hx.2.2⟩))
          (nbho_abs.mp (hE4 x ⟨by linarith, by linarith, hx.2.2⟩)))

/-- Function Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f - g) x₀ =? lim f x₀ - lim g x₀
:= by
  cases hA : lim f x₀ with | none => trivial | some L1 =>
  cases hB : lim g x₀ with | none => trivial | some L2 =>
    change lim (f - g) x₀ = some (L1 - L2)
    have hL1 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact FuncLimit_to_FuncLimitExpr (FuncLimit.Sub hL1 hL2)

/-- Left Limit Subtraction -/
theorem LeftLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F - G) x₀ (L₁ - L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx; exact ⟨hD1 ⟨by linarith, hx.2⟩, hD2 ⟨by linarith, hx.2⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Ioo] at hx
    exact nbho_abs.mpr (sub_helper (nbho_abs.mp (hE3 x ⟨by linarith, hx.2⟩))
          (nbho_abs.mp (hE4 x ⟨by linarith, hx.2⟩)))

/-- Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f - g) x₀ =? lim₋ f x₀ - lim₋ g x₀
:= by
  cases hA : lim₋ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₋ g x₀ with | none => trivial | some L2 =>
    change lim₋ (f - g) x₀ = some (L1 - L2)
    have hL1 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact LeftLimit_to_LeftLimitExpr (LeftLimit.Sub hL1 hL2)

/-- Right Limit Subtraction -/
theorem RightLimit.Sub {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F - G) x₀ (L₁ - L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx; exact ⟨hD1 ⟨hx.1, by linarith⟩, hD2 ⟨hx.1, by linarith⟩⟩
  · rcases hE1 (ε / 2) (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE2 (ε / 2) (by positivity) with ⟨δ4, hδ4, hE4⟩
    use min δ3 δ4, by positivity
    intro x hx
    have m3 := min_le_left δ3 δ4; have m4 := min_le_right δ3 δ4
    dsimp [Ioo] at hx
    exact nbho_abs.mpr (sub_helper (nbho_abs.mp (hE3 x ⟨hx.1, by linarith⟩))
          (nbho_abs.mp (hE4 x ⟨hx.1, by linarith⟩)))

/-- Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f - g) x₀ =? lim₊ f x₀ - lim₊ g x₀
:= by
  cases hA : lim₊ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₊ g x₀ with | none => trivial | some L2 =>
    change lim₊ (f - g) x₀ = some (L1 - L2)
    have hL1 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact RightLimit_to_RightLimitExpr (RightLimit.Sub hL1 hL2)

/-- Sequence Limit Multiplication -/
theorem SeqLimit.Mul {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
  : SeqLimit (A * B) (L₁ * L₂)
:= by
  rcases h_A with ⟨hfA, hEA⟩; rcases h_B with ⟨hfB, hEB⟩
  refine ⟨by dsimp [HMul.hMul, Mul.mul]; rw [hfA, hfB]; rfl, fun ε hε => ?_⟩
  rcases hEA 1 (by positivity) with ⟨N1, hN1⟩
  rcases hEA (ε / (2 * (|L₂| + 1))) (div_pos hε (by positivity)) with ⟨N2, hN2⟩
  rcases hEB (ε / (2 * (|L₁| + 2))) (div_pos hε (by positivity)) with ⟨N3, hN3⟩
  exact ⟨max N1 (max N2 N3), fun n hn =>
          nbho_abs.mpr (mul_helper (nbho_abs.mp (hN1 n (by omega)))
          (nbho_abs.mp (hN2 n (by omega))) (nbho_abs.mp (hN3 n (by omega))) hε)⟩

/-- Sequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul {a b : ℕ → ℝ}
  : limₙ (a * b) =? limₙ a * limₙ b
:= by
  cases hA : limₙ a <;> cases hB : limₙ b <;> try trivial
  rename_i L1 L2
  have hL1 := SeqLimitExpr_to_SeqLimit (init := 0) hA
  have hL2 := SeqLimitExpr_to_SeqLimit (init := 0) hB
  exact SeqLimit_to_SeqLimitExpr (SeqLimit.Mul hL1 hL2)

/-- Function Limit Multiplication -/
theorem FuncLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
  : FuncLimit (F * G) x₀ (L₁ * L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Nbhd] at hx
    exact ⟨hD1 ⟨by linarith, by linarith, hx.2.2⟩, hD2 ⟨by linarith, by linarith, hx.2.2⟩⟩
  · rcases hE1 1 (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE1 (ε / (2 * (|L₂| + 1))) (div_pos hε (by positivity)) with ⟨δ4, hδ4, hE4⟩
    rcases hE2 (ε / (2 * (|L₁| + 2))) (div_pos hε (by positivity)) with ⟨δ5, hδ5, hE5⟩
    use min δ3 (min δ4 δ5), by positivity
    intro x hx
    have m3 := min_le_left δ3 (min δ4 δ5)
    have m4 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_left δ4 δ5)
    have m5 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_right δ4 δ5)
    dsimp [Nbhd] at hx
    have hx3 : x ∈ Nbhd x₀ δ3 := ⟨by linarith, by linarith, hx.2.2⟩
    have hx4 : x ∈ Nbhd x₀ δ4 := ⟨by linarith, by linarith, hx.2.2⟩
    have hx5 : x ∈ Nbhd x₀ δ5 := ⟨by linarith, by linarith, hx.2.2⟩
    exact nbho_abs.mpr (mul_helper (nbho_abs.mp (hE3 x hx3))
          (nbho_abs.mp (hE4 x hx4)) (nbho_abs.mp (hE5 x hx5)) hε)

/-- Function Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f * g) x₀ =? lim f x₀ * lim g x₀
:= by
  cases hA : lim f x₀ with | none => trivial | some L1 =>
  cases hB : lim g x₀ with | none => trivial | some L2 =>
    change lim (f * g) x₀ = some (L1 * L2)
    have hL1 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact FuncLimit_to_FuncLimitExpr (FuncLimit.Mul hL1 hL2)

/-- Left Limit Multiplication -/
theorem LeftLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
  : LeftLimit (F * G) x₀ (L₁ * L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx
    exact ⟨hD1 ⟨by linarith, hx.2⟩, hD2 ⟨by linarith, hx.2⟩⟩
  · rcases hE1 1 (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE1 (ε / (2 * (|L₂| + 1))) (div_pos hε (by positivity)) with ⟨δ4, hδ4, hE4⟩
    rcases hE2 (ε / (2 * (|L₁| + 2))) (div_pos hε (by positivity)) with ⟨δ5, hδ5, hE5⟩
    use min δ3 (min δ4 δ5), by positivity
    intro x hx
    have m3 := min_le_left δ3 (min δ4 δ5)
    have m4 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_left δ4 δ5)
    have m5 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_right δ4 δ5)
    dsimp [Ioo] at hx
    have hx3 : x ∈ Ioo (x₀ - δ3) x₀ := ⟨by linarith, hx.2⟩
    have hx4 : x ∈ Ioo (x₀ - δ4) x₀ := ⟨by linarith, hx.2⟩
    have hx5 : x ∈ Ioo (x₀ - δ5) x₀ := ⟨by linarith, hx.2⟩
    exact nbho_abs.mpr (mul_helper (nbho_abs.mp (hE3 x hx3))
          (nbho_abs.mp (hE4 x hx4)) (nbho_abs.mp (hE5 x hx5)) hε)

/-- Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f * g) x₀ =? lim₋ f x₀ * lim₋ g x₀
:= by
  cases hA : lim₋ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₋ g x₀ with | none => trivial | some L2 =>
    change lim₋ (f * g) x₀ = some (L1 * L2)
    have hL1 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact LeftLimit_to_LeftLimitExpr (LeftLimit.Mul hL1 hL2)

/-- Right Limit Multiplication -/
theorem RightLimit.Mul {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
  : RightLimit (F * G) x₀ (L₁ * L₂)
:= by
  rcases h_F with ⟨⟨δ1, hδ1, hD1⟩, hE1⟩; rcases h_G with ⟨⟨δ2, hδ2, hD2⟩, hE2⟩
  refine ⟨⟨min δ1 δ2, by positivity, fun x hx => ?_⟩, fun ε hε => ?_⟩
  · have m1 := min_le_left δ1 δ2; have m2 := min_le_right δ1 δ2
    dsimp [Ioo] at hx; exact ⟨hD1 ⟨hx.1, by linarith⟩, hD2 ⟨hx.1, by linarith⟩⟩
  · rcases hE1 1 (by positivity) with ⟨δ3, hδ3, hE3⟩
    rcases hE1 (ε / (2 * (|L₂| + 1))) (div_pos hε (by positivity)) with ⟨δ4, hδ4, hE4⟩
    rcases hE2 (ε / (2 * (|L₁| + 2))) (div_pos hε (by positivity)) with ⟨δ5, hδ5, hE5⟩
    use min δ3 (min δ4 δ5), by positivity
    intro x hx
    have m3 := min_le_left δ3 (min δ4 δ5)
    have m4 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_left δ4 δ5)
    have m5 := (min_le_right δ3 (min δ4 δ5)).trans (min_le_right δ4 δ5)
    dsimp [Ioo] at hx
    have hx3 : x ∈ Ioo x₀ (x₀ + δ3) := ⟨hx.1, by linarith⟩
    have hx4 : x ∈ Ioo x₀ (x₀ + δ4) := ⟨hx.1, by linarith⟩
    have hx5 : x ∈ Ioo x₀ (x₀ + δ5) := ⟨hx.1, by linarith⟩
    exact nbho_abs.mpr (mul_helper (nbho_abs.mp (hE3 x hx3))
          (nbho_abs.mp (hE4 x hx4)) (nbho_abs.mp (hE5 x hx5)) hε)

/-- Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f * g) x₀ =? lim₊ f x₀ * lim₊ g x₀
:= by
  cases hA : lim₊ f x₀ with | none => trivial | some L1 =>
  cases hB : lim₊ g x₀ with | none => trivial | some L2 =>
    change lim₊ (f * g) x₀ = some (L1 * L2)
    have hL1 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
    have hL2 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
    exact RightLimit_to_RightLimitExpr (RightLimit.Mul hL1 hL2)

/-- Sequence Limit Division -/
theorem SeqLimit.Div {A B : Sequence} {L₁ L₂ : ℝ}
    (h_A : SeqLimit A L₁) (h_B : SeqLimit B L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : SeqLimit (A / B) (L₁ / L₂)
:= sorry

/-- Sequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div {a b : ℕ → ℝ}
  : limₙ (a / b) =? limₙ a / limₙ b
:= by
  cases hA : limₙ a with
  | none =>
    cases hB : limₙ b with
    | none => trivial
    | some L2 =>
      by_cases hZ : L2 = 0
      · rw [hZ]
        dsimp [HDiv.hDiv, Div.div]
        rw [if_pos rfl]
        trivial
      · dsimp [HDiv.hDiv, Div.div]
        rw [if_neg (by intro h; injection h with eq; exact hZ eq)]
        trivial
  | some L1 =>
    cases hB : limₙ b with
    | none => trivial
    | some L2 =>
      by_cases hZ : L2 = 0
      · rw [hZ]
        dsimp [HDiv.hDiv, Div.div]
        rw [if_pos rfl]
        trivial
      · dsimp [HDiv.hDiv, Div.div]
        rw [if_neg (by intro h; injection h with eq; exact hZ eq)]
        have hL1 := SeqLimitExpr_to_SeqLimit (init := 0) hA
        have hL2 := SeqLimitExpr_to_SeqLimit (init := 0) hB
        have h_lim := SeqLimit.Div hL1 hL2 hZ
        have h_eq : ∃ N : ℕ, ∀ n > N,
          (⟨a, 0, none⟩ / ⟨b, 0, none⟩ : Sequence).map n = (a / b) n := ⟨0, fun _ _ => rfl⟩
        apply SeqLimit_to_SeqLimitExpr (init := 0)
        exact SeqLimit.Congr (B := ⟨a / b, 0, none⟩) h_lim rfl h_eq

/-- Function Limit Division -/
theorem FuncLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : FuncLimit F x₀ L₁) (h_G : FuncLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : FuncLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Function Limit Division (Expression) -/
theorem FuncLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f / g) x₀ =? lim f x₀ / lim g x₀
:= by
  cases hA : lim f x₀ with
  | none =>
    have h_none : (none / lim g x₀ : Option ℝ) = none := by
      dsimp [HDiv.hDiv, Div.div]
      by_cases hZ : lim g x₀ = some 0
      · rw [if_pos hZ]
      · rw [if_neg hZ]
    rw [h_none]; exact trivial
  | some L1 =>
    cases hB : lim g x₀ with
    | none =>
      have h_none : (some L1 / none : Option ℝ) = none := rfl
      rw [h_none]; exact trivial
    | some L2 =>
      by_cases hZ : L2 = 0
      · rw [hZ]
        have h_none : (some L1 / some 0 : Option ℝ) = none := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_pos rfl]
        rw [h_none]; exact trivial
      · have h_some : (some L1 / some L2 : Option ℝ) = some (L1 / L2) := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_neg (by intro h; injection h with eq; exact hZ eq)]
        rw [h_some]
        change lim (f / g) x₀ = some (L1 / L2)
        have hL1 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
        have hL2 := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
        exact FuncLimit_to_FuncLimitExpr (FuncLimit.Div hL1 hL2 hZ)

/-- Left Limit Division -/
theorem LeftLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : LeftLimit F x₀ L₁) (h_G : LeftLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : LeftLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f / g) x₀ =? lim₋ f x₀ / lim₋ g x₀
:= by
  cases hA : lim₋ f x₀ with
  | none =>
    have h_none : (none / lim₋ g x₀ : Option ℝ) = none := by
      dsimp [HDiv.hDiv, Div.div]
      by_cases hZ : lim₋ g x₀ = some 0
      · rw [if_pos hZ]
      · rw [if_neg hZ]
    rw [h_none]; exact trivial
  | some L1 =>
    cases hB : lim₋ g x₀ with
    | none =>
      have h_none : (some L1 / none : Option ℝ) = none := rfl
      rw [h_none]; exact trivial
    | some L2 =>
      by_cases hZ : L2 = 0
      · rw [hZ]
        have h_none : (some L1 / some 0 : Option ℝ) = none := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_pos rfl]
        rw [h_none]; exact trivial
      · have h_some : (some L1 / some L2 : Option ℝ) = some (L1 / L2) := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_neg (by intro h; injection h with eq; exact hZ eq)]
        rw [h_some]
        change lim₋ (f / g) x₀ = some (L1 / L2)
        have hL1 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
        have hL2 := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
        exact LeftLimit_to_LeftLimitExpr (LeftLimit.Div hL1 hL2 hZ)

/-- Right Limit Division -/
theorem RightLimit.Div {F G : Function} {x₀ L₁ L₂ : ℝ}
    (h_F : RightLimit F x₀ L₁) (h_G : RightLimit G x₀ L₂)
    (h_L₂_ne0 : L₂ ≠ 0)
  : RightLimit (F / G) x₀ (L₁ / L₂)
:= sorry

/-- Right Limit Division (Expression) -/
theorem RightLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f / g) x₀ =? lim₊ f x₀ / lim₊ g x₀
:= by
  cases hA : lim₊ f x₀ with
  | none =>
    have h_none : (none / lim₊ g x₀ : Option ℝ) = none := by
      dsimp [HDiv.hDiv, Div.div]
      by_cases hZ : lim₊ g x₀ = some 0
      · rw [if_pos hZ]
      · rw [if_neg hZ]
    rw [h_none]; exact trivial
  | some L1 =>
    cases hB : lim₊ g x₀ with
    | none =>
      have h_none : (some L1 / none : Option ℝ) = none := rfl
      rw [h_none]; exact trivial
    | some L2 =>
      by_cases hZ : L2 = 0
      · rw [hZ]
        have h_none : (some L1 / some 0 : Option ℝ) = none := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_pos rfl]
        rw [h_none]; exact trivial
      · have h_some : (some L1 / some L2 : Option ℝ) = some (L1 / L2) := by
          dsimp [HDiv.hDiv, Div.div]; rw [if_neg (by intro h; injection h with eq; exact hZ eq)]
        rw [h_some]
        change lim₊ (f / g) x₀ = some (L1 / L2)
        have hL1 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hA
        have hL2 := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hB
        exact RightLimit_to_RightLimitExpr (RightLimit.Div hL1 hL2 hZ)

/-- Function Limit Composition -/
theorem FuncLimit.Comp {x₀ u₀ L₁ : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_G_ne_u₀ : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, G.map x ≠ u₀)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_L : FuncLimit F u₀ L₁)
  : FuncLimit (F ⊙ G) x₀ L₁
:= by
  rcases h_L with ⟨_, h_epsF⟩
  rcases h_u₀ with ⟨_, h_epsG⟩
  rcases h_G_ne_u₀ with ⟨δ1, hδ1, hG_ne⟩
  refine ⟨h_Nbhd, fun ε hε => ?_⟩
  rcases h_epsF ε hε with ⟨δ2, hδ2, hF⟩
  rcases h_epsG δ2 hδ2 with ⟨δ3, hδ3, hG⟩
  use min δ1 δ3, by positivity
  intro x hx
  have m1 := min_le_left δ1 δ3
  have m3 := min_le_right δ1 δ3
  dsimp [Nbhd] at hx
  have hx1 : x ∈ Nbhd x₀ δ1 := ⟨by linarith, by linarith, hx.2.2⟩
  have hx3 : x ∈ Nbhd x₀ δ3 := ⟨by linarith, by linarith, hx.2.2⟩
  have h_ne := hG_ne x hx1
  have h_val := hG x hx3
  exact hF (G.map x) ⟨h_val.1, h_val.2, h_ne⟩

/-- Squeeze Theorem for Sequence Limit (Expression) -/
theorem SeqLimit.Squeeze {a b c : ℕ → ℝ} {L₁ : ℝ}
    (h_a : limₙ a = the L₁) (h_c : limₙ c = the L₁)
    (h_sqz : ∃ N : ℕ, ∀ n > N, a n ≤ b n ∧ b n ≤ c n)
  : limₙ b = the L₁
:= by
  have ha_lim := SeqLimitExpr_to_SeqLimit (init := 0) h_a
  have hc_lim := SeqLimitExpr_to_SeqLimit (init := 0) h_c
  have h_lim : SeqLimit ⟨b, 0, none⟩ L₁ := by
    refine ⟨rfl, fun ε hε => ?_⟩
    rcases ha_lim.2 ε hε with ⟨N1, hN1⟩
    rcases hc_lim.2 ε hε with ⟨N2, hN2⟩
    rcases h_sqz with ⟨N3, hN3⟩
    use max N1 (max N2 N3)
    intro n hn
    have hA := hN1 n (by omega)
    have hC := hN2 n (by omega)
    have hS := hN3 n (by omega)
    dsimp [Nbho] at hA hC ⊢
    exact ⟨by linarith, by linarith⟩
  exact SeqLimit_to_SeqLimitExpr h_lim

/-- Squeeze Theorem for Function Limit (Expression) -/
theorem FuncLimit.Squeeze {f g h : ℝ → ℝ} {x₀ L₁ : ℝ}
    (h_F : lim f x₀ = the L₁) (h_h : lim h x₀ = the L₁)
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≤ g x ∧ g x ≤ h x)
  : lim g x₀ = the L₁
:= by
  have hF_lim := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_F
  have hh_lim := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_h
  rcases hF_lim with ⟨_, h_epsF⟩; rcases hh_lim with ⟨_, h_epsH⟩; rcases h_sqz with ⟨δ1, hδ1, hSqz⟩
  have h_lim : FuncLimit ⟨g, Iii⟩ x₀ L₁ := by
    refine ⟨⟨1, zero_lt_one, Set.subset_univ _⟩, fun ε hε => ?_⟩
    rcases h_epsF ε hε with ⟨δ2, hδ2, hF2⟩; rcases h_epsH ε hε with ⟨δ3, hδ3, hH3⟩
    use min δ1 (min δ2 δ3), by positivity
    intro x hx
    have m1 := min_le_left δ1 (min δ2 δ3)
    have m2 := (min_le_right δ1 (min δ2 δ3)).trans (min_le_left δ2 δ3)
    have m3 := (min_le_right δ1 (min δ2 δ3)).trans (min_le_right δ2 δ3)
    dsimp [Nbhd] at hx
    have hx1 : x ∈ Nbhd x₀ δ1 := ⟨by linarith, by linarith, hx.2.2⟩
    have hx2 : x ∈ Nbhd x₀ δ2 := ⟨by linarith, by linarith, hx.2.2⟩
    have hx3 : x ∈ Nbhd x₀ δ3 := ⟨by linarith, by linarith, hx.2.2⟩
    have hS := hSqz x hx1
    have hF := hF2 x hx2
    have hH := hH3 x hx3
    rw [nbho_abs] at hF hH ⊢
    have : -ε < f x - L₁ := (abs_lt.mp hF).1
    have : h x - L₁ < ε := (abs_lt.mp hH).2
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  exact FuncLimit_to_FuncLimitExpr h_lim
