/-
    Calculus_21.Limit.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Sequence.Concepts
import «Calculus_21».Function.Concepts
set_option linter.style.header false


/-! # Definitions of Limit -/

/-- Sequence Limit -/
-- @[Lean2TeX "数列@1收敛于@2" Text]
def SeqLimit (A : Sequence) (L : ℝ) : Prop :=
  A.final = none
  ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, A.map n ∈ Nbho L ε

abbrev SeqConvergesAt (A : Sequence) : Prop :=
  ∃ L : ℝ, SeqLimit A L

/-- Function Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处收敛于@3" Text]
def FuncLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, F.map x ∈ Nbho L ε)

abbrev FuncConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, FuncLimit F x₀ L

/-- Left Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的左极限为@3" Text]
def LeftLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x ∈ Nbho L ε)

abbrev LeftConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftLimit F x₀ L

/-- Right Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的右极限为@3" Text]
def RightLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x ∈ Nbho L ε)

abbrev RightConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightLimit F x₀ L

/-- Limit at Negative Infinity -/
def NegInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)

abbrev ConvergesAtNegInfty (F : Function) : Prop :=
  ∃ L : ℝ, NegInftyLimit F L

/-- Limit at Positive Infinity -/
def PosInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

abbrev ConvergesAtPosInfty (F : Function) : Prop :=
  ∃ L : ℝ, PosInftyLimit F L

/-- Limit at Infinity -/
def InftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain ∧ Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      (∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)
      ∧ (∀ x ∈ Ioi M, F.map x ∈ Nbho L ε))

abbrev ConvergesAtInfty (F : Function) : Prop :=
  ∃ L : ℝ, InftyLimit F L


/-! # Properties of Limit -/

/-- Uniqueness of Sequence Limit -/
theorem SeqLimit_Unique {A : Sequence} {L₁ L₂ : ℝ}
    (h₁ : SeqLimit A L₁) (h₂ : SeqLimit A L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨N₁, hN₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨N₂, hN₂⟩
    have hx₁ := hN₁ (max N₁ N₂ + 1) (by omega)
    have hx₂ := hN₂ (max N₁ N₂ + 1) (by omega)
    dsimp [Nbho] at hx₁ hx₂
    rcases hx₁ with ⟨hx1_l, hx1_r⟩
    rcases hx₂ with ⟨hx2_l, hx2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨N₁, hN₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨N₂, hN₂⟩
    have hx₁ := hN₁ (max N₁ N₂ + 1) (by omega)
    have hx₂ := hN₂ (max N₁ N₂ + 1) (by omega)
    dsimp [Nbho] at hx₁ hx₂
    rcases hx₁ with ⟨hx1_l, hx1_r⟩
    rcases hx₂ with ⟨hx2_l, hx2_r⟩
    linarith

/-- Boundedness of Convergent Sequence -/
theorem SeqLimit_Bounded {A : Sequence}
    (h_conv : SeqConvergesAt A)
  : SeqBounded A
:= by
  rcases h_conv with ⟨L, hL_fin, hL⟩
  rcases hL 1 zero_lt_one with ⟨N, hN⟩
  unfold SeqBounded
  rw [hL_fin]
  dsimp
  have H : ∀ k : ℕ, ∃ M > 0, ∀ n, A.init ≤ n → n < A.init + k → |A.map n| < M := by
    intro k
    induction k with
    | zero =>
      use 1, zero_lt_one
      intro n hn1 hn2
      omega
    | succ k ih =>
      rcases ih with ⟨M, hM_pos, hM⟩
      use max M (|A.map (A.init + k)| + 1)
      refine ⟨?_, ?_⟩
      · have : M ≤ max M (|A.map (A.init + k)| + 1) := le_max_left _ _
        linarith
      · intro n hn1 hn2
        have : n < A.init + k ∨ n = A.init + k := by omega
        rcases this with h_lt | rfl
        · have h1 := hM n hn1 h_lt
          have h2 : M ≤ max M (|A.map (A.init + k)| + 1) := le_max_left _ _
          linarith
        · have : |A.map (A.init + k)| + 1 ≤ max M (|A.map (A.init + k)| + 1) := le_max_right _ _
          linarith
  rcases H (N + 1 - A.init) with ⟨M1, hM1_pos, hM1⟩
  use max M1 (|L| + 1)
  refine ⟨?_, ?_⟩
  · have : M1 ≤ max M1 (|L| + 1) := le_max_left _ _
    linarith
  · intro n hn
    rw [Set.mem_Ici] at hn
    by_cases h_le : n ≤ N
    · have h_lt : n < A.init + (N + 1 - A.init) := by omega
      have h1 := hM1 n hn h_lt
      have h2 : M1 ≤ max M1 (|L| + 1) := le_max_left _ _
      linarith
    · have h_gt : n > N := by omega
      have hN_val := hN n h_gt
      have : |A.map n| < |L| + 1 := by
        dsimp [Nbho] at hN_val
        rcases hN_val with ⟨hN_l, hN_r⟩
        rw [abs_lt]
        exact ⟨by linarith [neg_le_abs L], by linarith [le_abs_self L]⟩
      have : |L| + 1 ≤ max M1 (|L| + 1) := le_max_right _ _
      linarith

/-- Uniqueness of Function Limit -/
theorem FuncLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : FuncLimit F x₀ L₁) (h₂ : FuncLimit F x₀ L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ + min δ₁ δ₂ / 2
    have hx₁ : x ∈ Nbhd x₀ δ₁ := by
      dsimp [Nbhd, x]
      exact ⟨by linarith, by linarith, by linarith⟩
    have hx₂ : x ∈ Nbhd x₀ δ₂ := by
      dsimp [Nbhd, x]
      exact ⟨by linarith, by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ + min δ₁ δ₂ / 2
    have hx₁ : x ∈ Nbhd x₀ δ₁ := by
      dsimp [Nbhd, x]
      exact ⟨by linarith, by linarith, by linarith⟩
    have hx₂ : x ∈ Nbhd x₀ δ₂ := by
      dsimp [Nbhd, x]
      exact ⟨by linarith, by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Local Boundedness of Convergent Function -/
theorem FuncLimit_Bounded {F : Function} {x₀ : ℝ}
    (h_conv : FuncConvergesAt F x₀)
  : FuncLocalBounded F x₀
:= by
  rcases h_conv with ⟨L, ⟨δ0, hδ0⟩, hL⟩
  rcases hL 1 zero_lt_one with ⟨δ, hδ_pos, hδ⟩
  dsimp [FuncLocalBounded]
  use δ, hδ_pos, |L| + 1 + |F.map x₀|
  have H : |L| + 1 + |F.map x₀| > 0 := by
    have : 0 ≤ |L| := abs_nonneg L
    have : 0 ≤ |F.map x₀| := abs_nonneg (F.map x₀)
    linarith
  use H
  intro x hx
  rcases hx with ⟨_, hx_nbho⟩
  by_cases h_eq : x = x₀
  · rw [h_eq]
    have : 0 ≤ |L| := abs_nonneg L
    linarith
  · have hx_nbhd : x ∈ Nbhd x₀ δ := by
      dsimp [Nbhd, Nbho] at *
      tauto
    have hN_val := hδ x hx_nbhd
    have abs_L_pos : L ≤ |L| := le_abs_self L
    have abs_L_neg : -L ≤ |L| := neg_le_abs L
    have : |F.map x| < |L| + 1 := by
      dsimp [Nbho] at hN_val
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    have : 0 ≤ |F.map x₀| := abs_nonneg (F.map x₀)
    linarith

/-- Uniqueness of Left Limit -/
theorem LeftLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : LeftLimit F x₀ L₁) (h₂ : LeftLimit F x₀ L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ - min δ₁ δ₂ / 2
    have hx₁ : x ∈ Ioo (x₀ - δ₁) x₀ := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have hx₂ : x ∈ Ioo (x₀ - δ₂) x₀ := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ - min δ₁ δ₂ / 2
    have hx₁ : x ∈ Ioo (x₀ - δ₁) x₀ := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have hx₂ : x ∈ Ioo (x₀ - δ₂) x₀ := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Uniqueness of Right Limit -/
theorem RightLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : RightLimit F x₀ L₁) (h₂ : RightLimit F x₀ L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ + min δ₁ δ₂ / 2
    have hx₁ : x ∈ Ioo x₀ (x₀ + δ₁) := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have hx₂ : x ∈ Ioo x₀ (x₀ + δ₂) := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
    have hδ1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    have hδ2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    have hδ_pos : 0 < min δ₁ δ₂ := lt_min hδ₁_pos hδ₂_pos
    let x := x₀ + min δ₁ δ₂ / 2
    have hx₁ : x ∈ Ioo x₀ (x₀ + δ₁) := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have hx₂ : x ∈ Ioo x₀ (x₀ + δ₂) := by
      dsimp [x, Ioo]
      exact ⟨by linarith, by linarith⟩
    have H1 := hδ₁ x hx₁
    have H2 := hδ₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Uniqueness of Limit at Negative Infinity -/
theorem NegInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : NegInftyLimit F L₁) (h₂ : NegInftyLimit F L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨M₁, hM₁_pos, hM₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨M₂, hM₂_pos, hM₂⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := -max M₁ M₂ - 1
    have hx₁ : x ∈ Iio (-M₁) := by
      dsimp [x, Iio]
      linarith
    have hx₂ : x ∈ Iio (-M₂) := by
      dsimp [x, Iio]
      linarith
    have H1 := hM₁ x hx₁
    have H2 := hM₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨M₁, hM₁_pos, hM₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨M₂, hM₂_pos, hM₂⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := -max M₁ M₂ - 1
    have hx₁ : x ∈ Iio (-M₁) := by
      dsimp [x, Iio]
      linarith
    have hx₂ : x ∈ Iio (-M₂) := by
      dsimp [x, Iio]
      linarith
    have H1 := hM₁ x hx₁
    have H2 := hM₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Local Boundedness of Function Convergent at Negative Infinity -/
theorem NegInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtNegInfty F)
  : FuncLocalBounded_NegInfty F
:= by
  rcases h_conv with ⟨L, ⟨M, hM_pos, hM_dom⟩, hL⟩
  rcases hL 1 zero_lt_one with ⟨M1, hM1_pos, hM1⟩
  dsimp [FuncLocalBounded_NegInfty]
  use M1 + 1, by linarith, |L| + 1
  have : |L| + 1 > 0 := by
    have h1 : 0 ≤ |L| := abs_nonneg L
    linarith
  use this
  intro x hx
  rcases hx with ⟨_, hx2⟩
  have hx3 : x ∈ Iio (-M1) := by
    dsimp [Iic, Iio] at *
    linarith
  have hM1_val := hM1 x hx3
  have : |F.map x| < |L| + 1 := by
    dsimp [Nbho] at hM1_val
    rcases hM1_val with ⟨hl, hr⟩
    rw [abs_lt]
    exact ⟨by linarith [neg_le_abs L], by linarith [le_abs_self L]⟩
  linarith [abs_nonneg (F.map x)]

/-- Uniqueness of Limit at Positive Infinity -/
theorem PosInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : PosInftyLimit F L₁) (h₂ : PosInftyLimit F L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨M₁, hM₁_pos, hM₁⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨M₂, hM₂_pos, hM₂⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := max M₁ M₂ + 1
    have hx₁ : x ∈ Ioi M₁ := by
      dsimp [x, Ioi]
      linarith
    have hx₂ : x ∈ Ioi M₂ := by
      dsimp [x, Ioi]
      linarith
    have H1 := hM₁ x hx₁
    have H2 := hM₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨M₁, hM₁_pos, hM₁⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨M₂, hM₂_pos, hM₂⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := max M₁ M₂ + 1
    have hx₁ : x ∈ Ioi M₁ := by
      dsimp [x, Ioi]
      linarith
    have hx₂ : x ∈ Ioi M₂ := by
      dsimp [x, Ioi]
      linarith
    have H1 := hM₁ x hx₁
    have H2 := hM₂ x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Local Boundedness of Function Convergent at Positive Infinity -/
theorem PosInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtPosInfty F)
  : FuncLocalBounded_PosInfty F
:= by
  rcases h_conv with ⟨L, ⟨M, hM_pos, hM_dom⟩, hL⟩
  rcases hL 1 zero_lt_one with ⟨M1, hM1_pos, hM1⟩
  dsimp [FuncLocalBounded_PosInfty]
  use M1 + 1, by linarith, |L| + 1
  have : |L| + 1 > 0 := by
    have h1 : 0 ≤ |L| := abs_nonneg L
    linarith
  use this
  intro x hx
  rcases hx with ⟨_, hx2⟩
  have hx3 : x ∈ Ioi M1 := by
    dsimp [Ici, Ioi] at *
    linarith
  have hM1_val := hM1 x hx3
  have : |F.map x| < |L| + 1 := by
    dsimp [Nbho] at hM1_val
    rcases hM1_val with ⟨hl, hr⟩
    rw [abs_lt]
    exact ⟨by linarith [neg_le_abs L], by linarith [le_abs_self L]⟩
  linarith [abs_nonneg (F.map x)]

/-- Uniqueness of Limit at Infinity -/
theorem InftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : InftyLimit F L₁) (h₂ : InftyLimit F L₂)
  : L₁ = L₂
:= by
  by_contra h
  rcases lt_trichotomy L₁ L₂ with h_lt | h_eq | h_gt
  · have hε : (L₂ - L₁) / 2 > 0 := by linarith
    rcases h₁.2 ((L₂ - L₁) / 2) hε with ⟨M₁, hM₁_pos, _, hM₁_pos_cond⟩
    rcases h₂.2 ((L₂ - L₁) / 2) hε with ⟨M₂, hM₂_pos, _, hM₂_pos_cond⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := max M₁ M₂ + 1
    have hx₁ : x ∈ Ioi M₁ := by
      dsimp [x, Ioi]
      linarith
    have hx₂ : x ∈ Ioi M₂ := by
      dsimp [x, Ioi]
      linarith
    have H1 := hM₁_pos_cond x hx₁
    have H2 := hM₂_pos_cond x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith
  · exact h h_eq
  · have hε : (L₁ - L₂) / 2 > 0 := by linarith
    rcases h₁.2 ((L₁ - L₂) / 2) hε with ⟨M₁, hM₁_pos, _, hM₁_pos_cond⟩
    rcases h₂.2 ((L₁ - L₂) / 2) hε with ⟨M₂, hM₂_pos, _, hM₂_pos_cond⟩
    have hM1 : M₁ ≤ max M₁ M₂ := le_max_left _ _
    have hM2 : M₂ ≤ max M₁ M₂ := le_max_right _ _
    let x := max M₁ M₂ + 1
    have hx₁ : x ∈ Ioi M₁ := by
      dsimp [x, Ioi]
      linarith
    have hx₂ : x ∈ Ioi M₂ := by
      dsimp [x, Ioi]
      linarith
    have H1 := hM₁_pos_cond x hx₁
    have H2 := hM₂_pos_cond x hx₂
    dsimp [Nbho] at H1 H2
    rcases H1 with ⟨H1_l, H1_r⟩
    rcases H2 with ⟨H2_l, H2_r⟩
    linarith

/-- Congruence of Sequence Limit -/
lemma SeqLimit.Congr {A B : Sequence} {L : ℝ}
    (h_lim : SeqLimit A L)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimit B L
:= by
  rcases h_lim with ⟨_, hA⟩
  constructor
  · exact h_B_inf
  · intro ε hε
    rcases hA ε hε with ⟨N1, hN1⟩
    rcases h_congr with ⟨N2, hN2⟩
    use max N1 N2
    intro n hn
    have hn1 : n > N1 := by omega
    have hn2 : n > N2 := by omega
    rw [← hN2 n hn2]
    exact hN1 n hn1

/-- Congruence of Function Limit -/
lemma FuncLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain ∧ ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= by
  rcases h_lim with ⟨⟨δF, hδF⟩, hF⟩
  rcases h_congr with ⟨δC, hδC_pos, hδC_dom, hδC_eq⟩
  constructor
  · exact ⟨δC, hδC_pos, hδC_dom⟩
  · intro ε hε
    rcases hF ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    use min δ1 δC
    refine ⟨lt_min hδ1_pos hδC_pos, ?_⟩
    intro x hx
    have hx1 : x ∈ Nbhd x₀ δ1 := by
      dsimp [Nbhd] at *
      have : min δ1 δC ≤ δ1 := min_le_left _ _
      exact ⟨by linarith, by linarith, hx.2.2⟩
    have hxC : x ∈ Nbhd x₀ δC := by
      dsimp [Nbhd] at *
      have : min δ1 δC ≤ δC := min_le_right _ _
      exact ⟨by linarith, by linarith, hx.2.2⟩
    rw [← hδC_eq x hxC]
    exact hδ1 x hx1

/-- Congruence of Left Limit -/
lemma LeftLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : LeftLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain
                        ∧ ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= by
  rcases h_lim with ⟨⟨δF, hδF⟩, hF⟩
  rcases h_congr with ⟨δC, hδC_pos, hδC_dom, hδC_eq⟩
  constructor
  · exact ⟨δC, hδC_pos, hδC_dom⟩
  · intro ε hε
    rcases hF ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    use min δ1 δC
    refine ⟨lt_min hδ1_pos hδC_pos, ?_⟩
    intro x hx
    have hx1 : x ∈ Ioo (x₀ - δ1) x₀ := by
      dsimp [Ioo] at *
      have : min δ1 δC ≤ δ1 := min_le_left _ _
      exact ⟨by linarith, hx.2⟩
    have hxC : x ∈ Ioo (x₀ - δC) x₀ := by
      dsimp [Ioo] at *
      have : min δ1 δC ≤ δC := min_le_right _ _
      exact ⟨by linarith, hx.2⟩
    rw [← hδC_eq x hxC]
    exact hδ1 x hx1

/-- Congruence of Right Limit -/
lemma RightLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : RightLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain
                        ∧ ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= by
  rcases h_lim with ⟨⟨δF, hδF⟩, hF⟩
  rcases h_congr with ⟨δC, hδC_pos, hδC_dom, hδC_eq⟩
  constructor
  · exact ⟨δC, hδC_pos, hδC_dom⟩
  · intro ε hε
    rcases hF ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    use min δ1 δC
    refine ⟨lt_min hδ1_pos hδC_pos, ?_⟩
    intro x hx
    have hx1 : x ∈ Ioo x₀ (x₀ + δ1) := by
      dsimp [Ioo] at *
      have : min δ1 δC ≤ δ1 := min_le_left _ _
      exact ⟨hx.1, by linarith⟩
    have hxC : x ∈ Ioo x₀ (x₀ + δC) := by
      dsimp [Ioo] at *
      have : min δ1 δC ≤ δC := min_le_right _ _
      exact ⟨hx.1, by linarith⟩
    rw [← hδC_eq x hxC]
    exact hδ1 x hx1

/-- Congruence of Limit at Negative Infinity -/
lemma NegInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : NegInftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain
                        ∧ ∀ x ∈ Iio (-M), F.map x = G.map x)
  : NegInftyLimit G L
:= by
  rcases h_lim with ⟨⟨MF, hMF⟩, hF⟩
  rcases h_congr with ⟨MC, hMC_pos, hMC_dom, hMC_eq⟩
  constructor
  · exact ⟨MC, hMC_pos, hMC_dom⟩
  · intro ε hε
    rcases hF ε hε with ⟨M1, hM1_pos, hM1⟩
    use max M1 MC
    refine ⟨lt_max_iff.mpr (Or.inl hM1_pos), ?_⟩
    intro x hx
    have hx1 : x ∈ Iio (-M1) := by
      dsimp [Iio] at *
      have : M1 ≤ max M1 MC := le_max_left _ _
      linarith
    have hxC : x ∈ Iio (-MC) := by
      dsimp [Iio] at *
      have : MC ≤ max M1 MC := le_max_right _ _
      linarith
    rw [← hMC_eq x hxC]
    exact hM1 x hx1

/-- Congruence of Limit at Positive Infinity -/
lemma PosInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : PosInftyLimit F L)
    (h_congr : ∃ M > 0, Ioi M ⊆ G.domain
                        ∧ ∀ x ∈ Ioi M, F.map x = G.map x)
  : PosInftyLimit G L
:= by
  rcases h_lim with ⟨⟨MF, hMF⟩, hF⟩
  rcases h_congr with ⟨MC, hMC_pos, hMC_dom, hMC_eq⟩
  constructor
  · exact ⟨MC, hMC_pos, hMC_dom⟩
  · intro ε hε
    rcases hF ε hε with ⟨M1, hM1_pos, hM1⟩
    use max M1 MC
    refine ⟨lt_max_iff.mpr (Or.inl hM1_pos), ?_⟩
    intro x hx
    have hx1 : x ∈ Ioi M1 := by
      dsimp [Ioi] at *
      have : M1 ≤ max M1 MC := le_max_left _ _
      linarith
    have hxC : x ∈ Ioi MC := by
      dsimp [Ioi] at *
      have : MC ≤ max M1 MC := le_max_right _ _
      linarith
    rw [← hMC_eq x hxC]
    exact hM1 x hx1

/-- Congruence of Limit at Infinity -/
lemma InftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain ∧ Ioi M ⊆ G.domain
                        ∧ (∀ x ∈ Iio (-M), F.map x = G.map x)
                        ∧ (∀ x ∈ Ioi M, F.map x = G.map x))
  : InftyLimit G L
:= by
  rcases h_lim with ⟨⟨MF, hMF⟩, hF⟩
  rcases h_congr with ⟨MC, hMC_pos, hMC_dom_neg, hMC_dom_pos, hMC_eq_neg, hMC_eq_pos⟩
  constructor
  · exact ⟨MC, hMC_pos, hMC_dom_neg, hMC_dom_pos⟩
  · intro ε hε
    rcases hF ε hε with ⟨M1, hM1_pos, hM1_neg, hM1_pos'⟩
    use max M1 MC
    refine ⟨lt_max_iff.mpr (Or.inl hM1_pos), ?_, ?_⟩
    · intro x hx
      have hx1 : x ∈ Iio (-M1) := by
        dsimp [Iio] at *
        have : M1 ≤ max M1 MC := le_max_left _ _
        linarith
      have hxC : x ∈ Iio (-MC) := by
        dsimp [Iio] at *
        have : MC ≤ max M1 MC := le_max_right _ _
        linarith
      rw [← hMC_eq_neg x hxC]
      exact hM1_neg x hx1
    · intro x hx
      have hx1 : x ∈ Ioi M1 := by
        dsimp [Ioi] at *
        have : M1 ≤ max M1 MC := le_max_left _ _
        linarith
      have hxC : x ∈ Ioi MC := by
        dsimp [Ioi] at *
        have : MC ≤ max M1 MC := le_max_right _ _
        linarith
      rw [← hMC_eq_pos x hxC]
      exact hM1_pos' x hx1

/-- Function Limit → Left Limit -/
theorem FuncLimit_toLeft {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= by
  rcases h_lim with ⟨⟨δ, hδ_pos, hδ_dom⟩, hL⟩
  constructor
  · use δ, hδ_pos
    intro x hx
    apply hδ_dom
    dsimp [Ioo] at hx
    dsimp [Nbhd]
    exact ⟨hx.1, by linarith, by linarith⟩
  · intro ε hε
    rcases hL ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    use δ1, hδ1_pos
    intro x hx
    apply hδ1
    dsimp [Ioo] at hx
    dsimp [Nbhd]
    exact ⟨hx.1, by linarith, by linarith⟩

/-- Function Limit → Right Limit -/
theorem FuncLimit_toRight {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= by
  rcases h_lim with ⟨⟨δ, hδ_pos, hδ_dom⟩, hL⟩
  constructor
  · use δ, hδ_pos
    intro x hx
    apply hδ_dom
    dsimp [Ioo] at hx
    dsimp [Nbhd]
    exact ⟨by linarith, hx.2, by linarith⟩
  · intro ε hε
    rcases hL ε hε with ⟨δ1, hδ1_pos, hδ1⟩
    use δ1, hδ1_pos
    intro x hx
    apply hδ1
    dsimp [Ioo] at hx
    dsimp [Nbhd]
    exact ⟨by linarith, hx.2, by linarith⟩

/-- Limit at Infinity → Limit at Negative Infinity -/
theorem InftyLimit_toNeg {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : NegInftyLimit F L
:= by
  rcases h_lim with ⟨⟨M, hM_pos, hM_dom_neg, _⟩, hL⟩
  constructor
  · exact ⟨M, hM_pos, hM_dom_neg⟩
  · intro ε hε
    rcases hL ε hε with ⟨M1, hM1_pos, hM1_neg, _⟩
    exact ⟨M1, hM1_pos, hM1_neg⟩

/-- Limit at Infinity → Limit at Positive Infinity -/
theorem InftyLimit_toPos {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : PosInftyLimit F L
:= by
  rcases h_lim with ⟨⟨M, hM_pos, _, hM_dom_pos⟩, hL⟩
  constructor
  · exact ⟨M, hM_pos, hM_dom_pos⟩
  · intro ε hε
    rcases hL ε hε with ⟨M1, hM1_pos, _, hM1_pos'⟩
    exact ⟨M1, hM1_pos, hM1_pos'⟩
