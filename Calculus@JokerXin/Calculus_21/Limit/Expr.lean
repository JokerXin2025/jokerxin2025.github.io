/-
    Calculus_21.Limit.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Limit.Defs
set_option linter.style.header false


/-! # Limit Expression -/

noncomputable section

open Classical in
/-- Sequence Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℕ)\\to\\infty}@1" Expr]
def SeqLimitExpr (a : ℕ → ℝ) : Option ℝ :=
  if h : SeqConvergesAt ⟨a, 0, none⟩ then the (choose h)
  else none

open Classical in
/-- Function Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2}@1" Expr]
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : FuncConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Left Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^-}@1" Expr]
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : LeftConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Right Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^+}@1" Expr]
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : RightConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtNegInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtPosInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtInfty ⟨f, Iii⟩ then the (choose h)
  else none

end

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)
macro "lim₋∞" : term => `(NegInftyLimitExpr)
macro "lim₊∞" : term => `(PosInftyLimitExpr)
macro "lim∞" : term => `(InftyLimitExpr)


/-! # Bridges between Limit & Limit Expression -/

open Classical in
/-- Sequence Limit → Sequence Limit Expression -/
theorem SeqLimit_to_SeqLimitExpr {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : SeqLimit ⟨a, init, none⟩ L)
  : limₙ a = the L
:= by
  unfold SeqLimitExpr
  have h_conv : SeqConvergesAt ⟨a, 0, none⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact SeqLimit_Unique (choose_spec h_conv) h_lim

open Classical in
/-- Sequence Limit Expression → Sequence Limit -/
theorem SeqLimitExpr_to_SeqLimit {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : limₙ a = the L)
  : SeqLimit ⟨a, init, none⟩ L := by
  unfold SeqLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_conv
  · contradiction

open Classical in
/-- Function Limit → Function Limit Expression -/
theorem FuncLimit_to_FuncLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : FuncLimit ⟨f, I⟩ x₀ L)
  : lim f x₀ = the L
:= by
  have h_lim_Iii : FuncLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold FuncLimitExpr
  have h_conv : FuncConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim_Iii⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact FuncLimit_Unique (choose_spec h_conv) h_lim_Iii

open Classical in
/-- Function Limit Expression → Function Limit -/
theorem FuncLimitExpr_to_FuncLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_lim : lim f x₀ = the L)
  : FuncLimit ⟨f, I⟩ x₀ L
:= by
  unfold FuncLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- Left Limit → Left Limit Expression -/
theorem LeftLimit_to_LeftLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : LeftLimit ⟨f, I⟩ x₀ L)
  : lim₋ f x₀ = the L
:= by
  have h_lim : LeftLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold LeftLimitExpr
  have h_conv : LeftConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact LeftLimit_Unique (choose_spec h_conv) h_lim

open Classical in
/-- Left Limit Expression → Left Limit -/
theorem LeftLimitExpr_to_LeftLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ I)
    (h_lim : lim₋ f x₀ = the L)
  : LeftLimit ⟨f, I⟩ x₀ L
:= by
  unfold LeftLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- Right Limit → Right Limit Expression -/
theorem RightLimit_to_RightLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : RightLimit ⟨f, I⟩ x₀ L)
  : lim₊ f x₀ = the L
:= by
  have h_lim : RightLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold RightLimitExpr
  have h_conv : RightConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact RightLimit_Unique (choose_spec h_conv) h_lim

open Classical in
/-- Right Limit Expression → Right Limit -/
theorem RightLimitExpr_to_RightLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ I)
    (h_lim : lim₊ f x₀ = the L)
  : RightLimit ⟨f, I⟩ x₀ L
:= by
  unfold RightLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- Limit at Negative Infinity → Expression of Limit at Negative Infinity -/
theorem NegInftyLimit_to_NegInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : NegInftyLimit ⟨f, I⟩ L)
  : lim₋∞ f = the L
:= by
  have h_lim : NegInftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold NegInftyLimitExpr
  have h_conv : ConvergesAtNegInfty ⟨f, Iii⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact NegInftyLimit_Unique (choose_spec h_conv) h_lim

open Classical in
/-- Expression of Limit at Negative Infinity → Limit at Negative Infinity -/
theorem NegInftyLimitExpr_to_NegInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I)
    (h_lim : lim₋∞ f = the L)
  : NegInftyLimit ⟨f, I⟩ L
:= by
  unfold NegInftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- Limit at Positive Infinity → Expression of Limit at Positive Infinity -/
theorem PosInftyLimit_to_PosInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : PosInftyLimit ⟨f, I⟩ L)
  : lim₊∞ f = the L
:= by
  have h_lim : PosInftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold PosInftyLimitExpr
  have h_conv : ConvergesAtPosInfty ⟨f, Iii⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact PosInftyLimit_Unique (choose_spec h_conv) h_lim

open Classical in
/-- Expression of Limit at Positive Infinity → Limit at Positive Infinity -/
theorem PosInftyLimitExpr_to_PosInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Ioi M ⊆ I)
    (h_lim : lim₊∞ f = the L)
  : PosInftyLimit ⟨f, I⟩ L
:= by
  unfold PosInftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- Limit at Infinity → Expression of Limit at Infinity -/
theorem InftyLimit_to_InftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : InftyLimit ⟨f, I⟩ L)
  : lim∞ f = the L
:= by
  have h_lim_univ : InftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨M, h_M_pos, _, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨M, h_M_pos, fun x _ => trivial, fun x _ => trivial⟩, h_eps_delta⟩
  unfold InftyLimitExpr
  have h_conv : ConvergesAtInfty ⟨f, Iii⟩ := ⟨L, h_lim_univ⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact InftyLimit_Unique (choose_spec h_conv) h_lim_univ

open Classical in
/-- Expression of Limit at Infinity → Limit at Infinity -/
theorem InftyLimitExpr_to_InftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I ∧ Ioi M ⊆ I)
    (h_lim : lim∞ f = the L)
  : InftyLimit ⟨f, I⟩ L
:= by
  unfold InftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction


/-! # Properties of Limit Expression -/

open Classical in
/-- Congruence of Sequence Limit (Expression) -/
lemma SeqLimitExpr.Congr {a b : ℕ → ℝ}
    (h_congr : ∃ N : ℕ, ∀ n > N, a n = b n)
  : limₙ a =? limₙ b
:= by
  unfold UdEqual
  cases hb : limₙ b with
  | none => trivial
  | some L =>
    unfold SeqLimitExpr at hb
    split at hb
    · rename_i h_conv
      injection hb with hb_eq
      have hb_lim : SeqLimit ⟨b, 0, none⟩ L := hb_eq ▸ choose_spec h_conv
      have ha_lim : SeqLimit ⟨a, 0, none⟩ L := by
        have h_congr' : ∃ N, ∀ n > N, b n = a n := by
          rcases h_congr with ⟨N, hN⟩
          exact ⟨N, fun n hn => (hN n hn).symm⟩
        exact SeqLimit.Congr hb_lim rfl h_congr'
      unfold SeqLimitExpr
      have ha_conv : SeqConvergesAt ⟨a, 0, none⟩ := ⟨L, ha_lim⟩
      simp only [dif_pos ha_conv]
      apply congrArg
      exact SeqLimit_Unique (choose_spec ha_conv) ha_lim
    · contradiction

/-- Congruence of Function Limit (Expression) -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x)
  : lim f x₀ =? lim g x₀
:= by
  unfold UdEqual
  cases hg : lim g x₀ with
  | none => trivial
  | some L =>
    have hg_lim := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hg
    have hf_lim : FuncLimit ⟨f, Iii⟩ x₀ L := by
      rcases h_congr with ⟨δ, hδ_pos, hδ_eq⟩
      have h_congr' : ∃ δ' > 0, Nbhd x₀ δ' ⊆ Iii ∧ ∀ x ∈ Nbhd x₀ δ', g x = f x :=
        ⟨δ, hδ_pos, Set.subset_univ _, fun x hx => (hδ_eq x hx).symm⟩
      exact FuncLimit.Congr hg_lim h_congr'
    exact FuncLimit_to_FuncLimitExpr hf_lim

/-- Congruence of Left Limit (Expression) -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= by
  unfold UdEqual
  cases hg : lim₋ g x₀ with
  | none => trivial
  | some L =>
    have hg_lim := LeftLimitExpr_to_LeftLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hg
    have hf_lim : LeftLimit ⟨f, Iii⟩ x₀ L := by
      rcases h_congr with ⟨δ, hδ_pos, hδ_eq⟩
      have h_congr' : ∃ δ' > 0, Ioo (x₀ - δ') x₀ ⊆ Iii ∧ ∀ x ∈ Ioo (x₀ - δ') x₀, g x = f x :=
        ⟨δ, hδ_pos, Set.subset_univ _, fun x hx => (hδ_eq x hx).symm⟩
      exact LeftLimit.Congr hg_lim h_congr'
    exact LeftLimit_to_LeftLimitExpr hf_lim

/-- Congruence of Right Limit (Expression) -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= by
  unfold UdEqual
  cases hg : lim₊ g x₀ with
  | none => trivial
  | some L =>
    have hg_lim := RightLimitExpr_to_RightLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hg
    have hf_lim : RightLimit ⟨f, Iii⟩ x₀ L := by
      rcases h_congr with ⟨δ, hδ_pos, hδ_eq⟩
      have h_congr' : ∃ δ' > 0, Ioo x₀ (x₀ + δ') ⊆ Iii ∧ ∀ x ∈ Ioo x₀ (x₀ + δ'), g x = f x :=
        ⟨δ, hδ_pos, Set.subset_univ _, fun x hx => (hδ_eq x hx).symm⟩
      exact RightLimit.Congr hg_lim h_congr'
    exact RightLimit_to_RightLimitExpr hf_lim

/-- Congruence of Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Iio (-M), f x = g x)
  : lim₋∞ f =? lim₋∞ g
:= by
  unfold UdEqual
  cases hg : lim₋∞ g with
  | none => trivial
  | some L =>
    have hg_lim := NegInftyLimitExpr_to_NegInftyLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hg
    have hf_lim : NegInftyLimit ⟨f, Iii⟩ L := by
      rcases h_congr with ⟨M, hM_pos, hM_eq⟩
      have h_congr' : ∃ M' > 0, Iio (-M') ⊆ Iii ∧ ∀ x ∈ Iio (-M'), g x = f x :=
        ⟨M, hM_pos, Set.subset_univ _, fun x hx => (hM_eq x hx).symm⟩
      exact NegInftyLimit.Congr hg_lim h_congr'
    exact NegInftyLimit_to_NegInftyLimitExpr hf_lim

/-- Congruence of Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Ioi M, f x = g x)
  : lim₊∞ f =? lim₊∞ g
:= by
  unfold UdEqual
  cases hg : lim₊∞ g with
  | none => trivial
  | some L =>
    have hg_lim := PosInftyLimitExpr_to_PosInftyLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ hg
    have hf_lim : PosInftyLimit ⟨f, Iii⟩ L := by
      rcases h_congr with ⟨M, hM_pos, hM_eq⟩
      have h_congr' : ∃ M' > 0, Ioi M' ⊆ Iii ∧ ∀ x ∈ Ioi M', g x = f x :=
        ⟨M, hM_pos, Set.subset_univ _, fun x hx => (hM_eq x hx).symm⟩
      exact PosInftyLimit.Congr hg_lim h_congr'
    exact PosInftyLimit_to_PosInftyLimitExpr hf_lim

/-- Congruence of Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, (∀ x ∈ Iio (-M), f x = g x) ∧ (∀ x ∈ Ioi M, f x = g x))
  : lim∞ f =? lim∞ g
:= by
  unfold UdEqual
  cases hg : lim∞ g with
  | none => trivial
  | some L =>
    have hg_lim := InftyLimitExpr_to_InftyLimit
      ⟨1, zero_lt_one, ⟨Set.subset_univ _, Set.subset_univ _⟩⟩ hg
    have hf_lim : InftyLimit ⟨f, Iii⟩ L := by
      rcases h_congr with ⟨M, hM_pos, hM_eq_neg, hM_eq_pos⟩
      have h_congr' : ∃ M' > 0, Iio (-M') ⊆ Iii ∧ Ioi M' ⊆ Iii
                                ∧ (∀ x ∈ Iio (-M'), g x = f x)
                                ∧ (∀ x ∈ Ioi M', g x = f x) :=
        ⟨M, hM_pos, Set.subset_univ _, Set.subset_univ _,
        fun x hx => (hM_eq_neg x hx).symm, fun x hx => (hM_eq_pos x hx).symm⟩
      exact InftyLimit.Congr hg_lim h_congr'
    exact InftyLimit_to_InftyLimitExpr hf_lim


/-- Function Limit → Left Limit (Expression) -/
theorem FuncLimitExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f x₀ =? lim f x₀
:= by
  unfold UdEqual
  cases h_lim : lim f x₀ with
  | none => trivial
  | some L =>
    have hf_lim := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_lim
    exact LeftLimit_to_LeftLimitExpr (FuncLimit_toLeft hf_lim)

/-- Function Limit → Right Limit (Expression) -/
theorem FuncLimitExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f x₀ =? lim f x₀
:= by
  unfold UdEqual
  cases h_lim : lim f x₀ with
  | none => trivial
  | some L =>
    have hf_lim := FuncLimitExpr_to_FuncLimit ⟨1, zero_lt_one, Set.subset_univ _⟩ h_lim
    exact RightLimit_to_RightLimitExpr (FuncLimit_toRight hf_lim)

/-- Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr_toNeg {f : ℝ → ℝ}
  : lim₋∞ f =? lim∞ f
:= by
  unfold UdEqual
  cases h_lim : lim∞ f with
  | none => trivial
  | some L =>
    have hf_lim := InftyLimitExpr_to_InftyLimit
      ⟨1, zero_lt_one, ⟨Set.subset_univ _, Set.subset_univ _⟩⟩ h_lim
    exact NegInftyLimit_to_NegInftyLimitExpr (InftyLimit_toNeg hf_lim)

/-- Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr_toPos {f : ℝ → ℝ}
  : lim₊∞ f =? lim∞ f
:= by
  unfold UdEqual
  cases h_lim : lim∞ f with
  | none => trivial
  | some L =>
    have hf_lim := InftyLimitExpr_to_InftyLimit
      ⟨1, zero_lt_one, ⟨Set.subset_univ _, Set.subset_univ _⟩⟩ h_lim
    exact PosInftyLimit_to_PosInftyLimitExpr (InftyLimit_toPos hf_lim)
