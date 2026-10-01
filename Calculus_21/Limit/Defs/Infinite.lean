/-
    «Calculus_21».Limit.Defs.Infinite
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
 -/

import «Calculus_21».Limit.Defs.Seq
import «Calculus_21».Limit.Defs.Func
set_option linter.style.header false


/-! # Infinite limits -/

section
variable (A : RSequence) (F : RFunction) (x₀ : ℝ)

def SeqLimitPosInfty : Prop :=
  A.final = none
  ∧ ∀ M > 0, ∃ N : ℕ, ∀ n > N, A.map n > M

def SeqLimitNegInfty : Prop :=
  A.final = none
  ∧ ∀ M > 0, ∃ N : ℕ, ∀ n > N, A.map n < -M

def SeqLimitInfty : Prop :=
  A.final = none
  ∧ ∀ M > 0, ∃ N : ℕ, ∀ n > N, |A.map n| > M

def FuncLimitPosInfty : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, F.map x > M

def FuncLimitNegInfty : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, F.map x < -M

def FuncLimitInfty : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, |F.map x| > M

def LeftLimitPosInfty : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x > M

def LeftLimitNegInfty : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x < -M

def LeftLimitInfty : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, |F.map x| > M

def RightLimitPosInfty : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x > M

def RightLimitNegInfty : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x < -M

def RightLimitInfty : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), |F.map x| > M

def PosInftyLimitPosInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X, F.map x > M

def PosInftyLimitNegInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X, F.map x < -M

def PosInftyLimitInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X, |F.map x| > M

def NegInftyLimitPosInfty : Prop :=
  (∃ X > 0, Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Iio (-X), F.map x > M

def NegInftyLimitNegInfty : Prop :=
  (∃ X > 0, Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Iio (-X), F.map x < -M

def NegInftyLimitInfty : Prop :=
  (∃ X > 0, Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Iio (-X), |F.map x| > M

def InftyLimitPosInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain ∧ Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), F.map x > M

def InftyLimitNegInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain ∧ Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), F.map x < -M

def InftyLimitInfty : Prop :=
  (∃ X > 0, Ioi X ⊆ F.domain ∧ Iio (-X) ⊆ F.domain)
  ∧ ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), |F.map x| > M

end


/-! # Basic Properties of Infinite Limits -/

section
variable {A : RSequence} {F : RFunction} {x₀ : ℝ}

@theorem SeqLimitPosInfty.toSeqLimitInfty
  : SeqLimitPosInfty A → SeqLimitInfty A
:= by
  intro h
  rcases h with ⟨h_final, h_pos⟩
  refine ⟨h_final, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_of_lt_of_le (hN n hn) (le_abs_self _)

@theorem SeqLimitNegInfty.toSeqLimitInfty
  : SeqLimitNegInfty A → SeqLimitInfty A
:= by
  intro h
  rcases h with ⟨h_final, h_neg⟩
  refine ⟨h_final, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h_neg : A.map n < 0 := by
    linarith [hN n hn]
  have h_abs : |A.map n| = -A.map n := abs_of_neg h_neg
  rw [h_abs]
  linarith [hN n hn]

@theorem FuncLimitPosInfty.toFuncLimitInfty
  : FuncLimitPosInfty F x₀ → FuncLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hδ' x h_x) (le_abs_self _)

@theorem FuncLimitNegInfty.toFuncLimitInfty
  : FuncLimitNegInfty F x₀ → FuncLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  have h_neg : F.map x < 0 := by
    linarith [hδ' x h_x]
  have h_abs : |F.map x| = -F.map x := abs_of_neg h_neg
  rw [h_abs]
  linarith [hδ' x h_x]

@theorem LeftLimitPosInfty.toLeftLimitInfty
  : LeftLimitPosInfty F x₀ → LeftLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hδ' x h_x) (le_abs_self _)

@theorem LeftLimitNegInfty.toLeftLimitInfty
  : LeftLimitNegInfty F x₀ → LeftLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  have h_x_neg : F.map x < 0 := by
    linarith [hδ' x h_x]
  have h_abs : |F.map x| = -F.map x := abs_of_neg h_x_neg
  rw [h_abs]
  linarith [hδ' x h_x]

@theorem RightLimitPosInfty.toRightLimitInfty
  : RightLimitPosInfty F x₀ → RightLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hδ' x h_x) (le_abs_self _)

@theorem RightLimitNegInfty.toRightLimitInfty
  : RightLimitNegInfty F x₀ → RightLimitInfty F x₀
:= by
  intro h
  rcases h with ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  have h_x_neg : F.map x < 0 := by
    linarith [hδ' x h_x]
  have h_abs : |F.map x| = -F.map x := abs_of_neg h_x_neg
  rw [h_abs]
  linarith [hδ' x h_x]

@theorem PosInftyLimitPosInfty.toPosInftyLimitInfty
  : PosInftyLimitPosInfty F → PosInftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_pos K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hM' x h_x) (le_abs_self _)

@theorem PosInftyLimitNegInfty.toPosInftyLimitInfty
  : PosInftyLimitNegInfty F → PosInftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_neg K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  have h_neg : F.map x < 0 := by
    linarith [hM' x h_x]
  have h_abs : |F.map x| = -F.map x := abs_of_neg h_neg
  rw [h_abs]
  linarith [hM' x h_x]

@theorem NegInftyLimitPosInfty.toNegInftyLimitInfty
  : NegInftyLimitPosInfty F → NegInftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hM' x h_x) (le_abs_self _)

@theorem NegInftyLimitNegInfty.toNegInftyLimitInfty
  : NegInftyLimitNegInfty F → NegInftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  have h_neg : F.map x < 0 := by
    linarith [hM' x h_x]
  have h_abs : |F.map x| = -F.map x := abs_of_neg h_neg
  rw [h_abs]
  linarith [hM' x h_x]

@theorem InftyLimitPosInfty.toInftyLimitInfty
  : InftyLimitPosInfty F → InftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_pos K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  exact lt_of_lt_of_le (hM' x h_x) (le_abs_self _)

@theorem InftyLimitNegInfty.toInftyLimitInfty
  : InftyLimitNegInfty F → InftyLimitInfty F
:= by
  intro h
  rcases h with ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_neg K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  have h_x_neg : F.map x < 0 := by
    linarith [hM' x h_x]
  rw [abs_of_neg h_x_neg]
  linarith [hM' x h_x]

@theorem SeqLimitPosInfty.Congr {B : RSequence}
    (h_lim : SeqLimitPosInfty A)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimitPosInfty B
:= by
  rcases h_lim with ⟨_, h_lim⟩
  rcases h_congr with ⟨N, hN⟩
  refine ⟨h_B_inf, ?_⟩
  intro M hM
  rcases h_lim M hM with ⟨K, hK⟩
  refine ⟨max N K, ?_⟩
  intro n hn
  rw [← hN n (lt_of_le_of_lt (Nat.le_max_left _ _) hn)]
  exact hK n (lt_of_le_of_lt (Nat.le_max_right _ _) hn)

@theorem SeqLimitNegInfty.Congr {B : RSequence}
    (h_lim : SeqLimitNegInfty A)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimitNegInfty B
:= by
  rcases h_lim with ⟨_, h_lim⟩
  rcases h_congr with ⟨N, hN⟩
  refine ⟨h_B_inf, ?_⟩
  intro M hM
  rcases h_lim M hM with ⟨K, hK⟩
  refine ⟨max N K, ?_⟩
  intro n hn
  rw [← hN n (lt_of_le_of_lt (Nat.le_max_left _ _) hn)]
  exact hK n (lt_of_le_of_lt (Nat.le_max_right _ _) hn)

@theorem SeqLimitInfty.Congr {B : RSequence}
    (h_lim : SeqLimitInfty A)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimitInfty B
:= by
  rcases h_lim with ⟨_, h_lim⟩
  rcases h_congr with ⟨N, hN⟩
  refine ⟨h_B_inf, ?_⟩
  intro M hM
  rcases h_lim M hM with ⟨K, hK⟩
  refine ⟨max N K, ?_⟩
  intro n hn
  rw [← hN n (lt_of_le_of_lt (Nat.le_max_left _ _) hn)]
  exact hK n (lt_of_le_of_lt (Nat.le_max_right _ _) hn)

private theorem infiniteLimitCongr
    {S : ℝ → Set ℝ} {p : ℝ → Prop} {q : ℝ → ℝ → Prop} {G : RFunction}
    (h_lim : (∃ r, p r ∧ S r ⊆ F.domain) ∧
      ∀ M > 0, ∃ r, p r ∧ ∀ x ∈ S r, q M (F.map x))
    (h_congr : ∃ r, p r ∧ S r ⊆ G.domain ∧
      ∀ x ∈ S r, F.map x = G.map x)
    (h_sh_rink : ∀ {r s}, p r → p s → ∃ t, p t ∧ S t ⊆ S r ∩ S s)
  : (∃ r, p r ∧ S r ⊆ G.domain) ∧
      ∀ M > 0, ∃ r, p r ∧ ∀ x ∈ S r, q M (G.map x)
:= by
  rcases h_congr with ⟨r, h_r, hGdom, heq⟩
  refine ⟨⟨r, h_r, hGdom⟩, ?_⟩
  intro M hM
  rcases h_lim.2 M hM with ⟨s, hs, hmap⟩
  rcases h_sh_rink h_r hs with ⟨t, ht, ht_sub⟩
  refine ⟨t, ht, ?_⟩
  intro x h_x
  have h_x' := ht_sub h_x
  rw [← heq x h_x'.1]
  exact hmap x h_x'.2

private lemma nbhdMinSubset {r s : ℝ}
  : Nbhd x₀ (min r s) ⊆ Nbhd x₀ r ∩ Nbhd x₀ s
:= by
  intro x h_x
  exact ⟨⟨by linarith [h_x.1, min_le_left r s],
    by linarith [h_x.2.1, min_le_left r s], h_x.2.2⟩,
    ⟨by linarith [h_x.1, min_le_right r s],
    by linarith [h_x.2.1, min_le_right r s], h_x.2.2⟩⟩

private lemma leftMinSubset {r s : ℝ}
  : Ioo (x₀ - min r s) x₀ ⊆ Ioo (x₀ - r) x₀ ∩ Ioo (x₀ - s) x₀
:= by
  intro x h_x
  exact ⟨⟨by linarith [h_x.1, min_le_left r s], h_x.2⟩,
    ⟨by linarith [h_x.1, min_le_right r s], h_x.2⟩⟩

private lemma rightMinSubset {r s : ℝ}
  : Ioo x₀ (x₀ + min r s) ⊆ Ioo x₀ (x₀ + r) ∩ Ioo x₀ (x₀ + s)
:= by
  intro x h_x
  exact ⟨⟨h_x.1, by linarith [h_x.2, min_le_left r s]⟩,
    ⟨h_x.1, by linarith [h_x.2, min_le_right r s]⟩⟩

private lemma ioiMaxSubset {r s : ℝ}
  : Ioi (max r s) ⊆ Ioi r ∩ Ioi s
:= by
  intro x h_x
  exact ⟨lt_of_le_of_lt (le_max_left r s) h_x,
    lt_of_le_of_lt (le_max_right r s) h_x⟩

private lemma iioMaxSubset {r s : ℝ}
  : Iio (-max r s) ⊆ Iio (-r) ∩ Iio (-s)
:= by
  intro x h_x
  change x < -max r s at h_x
  constructor
  · change x < -r
    linarith [le_max_left r s]
  · change x < -s
    linarith [le_max_right r s]

private lemma inftyMaxSubset {r s : ℝ}
  : Ioi (max r s) ∪ Iio (-max r s) ⊆
      (Ioi r ∪ Iio (-r)) ∩ (Ioi s ∪ Iio (-s))
:= by
  intro x h_x
  rcases h_x with h_x | h_x
  · exact ⟨Or.inl (lt_of_le_of_lt (le_max_left r s) h_x),
      Or.inl (lt_of_le_of_lt (le_max_right r s) h_x)⟩
  · change x < -max r s at h_x
    exact ⟨Or.inr (by change x < -r; linarith [le_max_left r s]),
      Or.inr (by change x < -s; linarith [le_max_right r s])⟩

private theorem inftyLimitCongr
    {q : ℝ → ℝ → Prop} {G : RFunction}
    (h_lim : (∃ X > 0, Ioi X ⊆ F.domain ∧ Iio (-X) ⊆ F.domain) ∧
      ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), q M (F.map x))
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧ Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Ioi X ∪ Iio (-X), F.map x = G.map x)
  : (∃ X > 0, Ioi X ⊆ G.domain ∧ Iio (-X) ⊆ G.domain) ∧
      ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), q M (G.map x)
:= by
  have h_lim' : (∃ X > 0, Ioi X ∪ Iio (-X) ⊆ F.domain) ∧
      ∀ M > 0, ∃ X > 0, ∀ x ∈ Ioi X ∪ Iio (-X), q M (F.map x) := by
    rcases h_lim.1 with ⟨X, hX, hpos, hneg⟩
    exact ⟨⟨X, hX, fun x h_x => h_x.elim (fun h_x => hpos h_x) (fun h_x => hneg h_x)⟩,
      h_lim.2⟩
  have h_congr' : ∃ X > 0, Ioi X ∪ Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Ioi X ∪ Iio (-X), F.map x = G.map x := by
    rcases h_congr with ⟨X, hX, hpos, hneg, heq⟩
    exact ⟨X, hX, fun x h_x => h_x.elim (fun h_x => hpos h_x) (fun h_x => hneg h_x), heq⟩
  have h_result := infiniteLimitCongr h_lim' h_congr' (fun {r s} h_r hs =>
    ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), inftyMaxSubset⟩)
  rcases h_result.1 with ⟨X, hX, hdom⟩
  exact ⟨⟨X, hX, fun x h_x => hdom (Or.inl h_x),
    fun x h_x => hdom (Or.inr h_x)⟩, h_result.2⟩

@theorem FuncLimitPosInfty.Congr {G : RFunction}
    (h_lim : FuncLimitPosInfty F x₀)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain ∧
      ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimitPosInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, nbhdMinSubset⟩

@theorem FuncLimitNegInfty.Congr {G : RFunction}
    (h_lim : FuncLimitNegInfty F x₀)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain ∧
      ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimitNegInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y < -M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, nbhdMinSubset⟩

@theorem FuncLimitInfty.Congr {G : RFunction}
    (h_lim : FuncLimitInfty F x₀)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain ∧
      ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimitInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => |y| > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, nbhdMinSubset⟩

@theorem LeftLimitPosInfty.Congr {G : RFunction}
    (h_lim : LeftLimitPosInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain ∧
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimitPosInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, leftMinSubset⟩

@theorem LeftLimitNegInfty.Congr {G : RFunction}
    (h_lim : LeftLimitNegInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain ∧
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimitNegInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y < -M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, leftMinSubset⟩

@theorem LeftLimitInfty.Congr {G : RFunction}
    (h_lim : LeftLimitInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain ∧
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimitInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => |y| > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, leftMinSubset⟩

@theorem RightLimitPosInfty.Congr {G : RFunction}
    (h_lim : RightLimitPosInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain ∧
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimitPosInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, rightMinSubset⟩

@theorem RightLimitNegInfty.Congr {G : RFunction}
    (h_lim : RightLimitNegInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain ∧
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimitNegInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => y < -M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, rightMinSubset⟩

@theorem RightLimitInfty.Congr {G : RFunction}
    (h_lim : RightLimitInfty F x₀)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain ∧
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimitInfty G x₀
:= by
  apply infiniteLimitCongr (q := fun M y => |y| > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨min r s, lt_min h_r hs, rightMinSubset⟩

@theorem PosInftyLimitPosInfty.Congr {G : RFunction}
    (h_lim : PosInftyLimitPosInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧
      ∀ x ∈ Ioi X, F.map x = G.map x)
  : PosInftyLimitPosInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => y > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), ioiMaxSubset⟩

@theorem PosInftyLimitNegInfty.Congr {G : RFunction}
    (h_lim : PosInftyLimitNegInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧
      ∀ x ∈ Ioi X, F.map x = G.map x)
  : PosInftyLimitNegInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => y < -M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), ioiMaxSubset⟩

@theorem PosInftyLimitInfty.Congr {G : RFunction}
    (h_lim : PosInftyLimitInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧
      ∀ x ∈ Ioi X, F.map x = G.map x)
  : PosInftyLimitInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => |y| > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), ioiMaxSubset⟩

@theorem NegInftyLimitPosInfty.Congr {G : RFunction}
    (h_lim : NegInftyLimitPosInfty F)
    (h_congr : ∃ X > 0, Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Iio (-X), F.map x = G.map x)
  : NegInftyLimitPosInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => y > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), iioMaxSubset⟩

@theorem NegInftyLimitNegInfty.Congr {G : RFunction}
    (h_lim : NegInftyLimitNegInfty F)
    (h_congr : ∃ X > 0, Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Iio (-X), F.map x = G.map x)
  : NegInftyLimitNegInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => y < -M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), iioMaxSubset⟩

@theorem NegInftyLimitInfty.Congr {G : RFunction}
    (h_lim : NegInftyLimitInfty F)
    (h_congr : ∃ X > 0, Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Iio (-X), F.map x = G.map x)
  : NegInftyLimitInfty G
:= by
  apply infiniteLimitCongr (q := fun M y => |y| > M) h_lim h_congr
  intro r s h_r hs
  exact ⟨max r s, lt_of_lt_of_le h_r (le_max_left r s), iioMaxSubset⟩

@theorem InftyLimitPosInfty.Congr {G : RFunction}
    (h_lim : InftyLimitPosInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧ Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Ioi X ∪ Iio (-X), F.map x = G.map x)
  : InftyLimitPosInfty G
:= by
  exact inftyLimitCongr (q := fun M y => y > M) h_lim h_congr

@theorem InftyLimitNegInfty.Congr {G : RFunction}
    (h_lim : InftyLimitNegInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧ Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Ioi X ∪ Iio (-X), F.map x = G.map x)
  : InftyLimitNegInfty G
:= by
  exact inftyLimitCongr (q := fun M y => y < -M) h_lim h_congr

@theorem InftyLimitInfty.Congr {G : RFunction}
    (h_lim : InftyLimitInfty F)
    (h_congr : ∃ X > 0, Ioi X ⊆ G.domain ∧ Iio (-X) ⊆ G.domain ∧
      ∀ x ∈ Ioi X ∪ Iio (-X), F.map x = G.map x)
  : InftyLimitInfty G
:= by
  exact inftyLimitCongr (q := fun M y => |y| > M) h_lim h_congr

@theorem SeqLimitPosInfty.neg
  : SeqLimitPosInfty A → SeqLimitNegInfty (-A)
:= by
  intro ⟨h_final, h_pos⟩
  refine ⟨h_final, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change -A.map n < -M
  linarith [hN n hn]

@theorem SeqLimitNegInfty.neg
  : SeqLimitNegInfty A → SeqLimitPosInfty (-A)
:= by
  intro ⟨h_final, h_neg⟩
  refine ⟨h_final, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change M < -A.map n
  linarith [hN n hn]

@theorem FuncLimitPosInfty.neg
  : FuncLimitPosInfty F x₀ → FuncLimitNegInfty (-F) x₀
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change -F.map x < -M
  linarith [hδ' x h_x]

@theorem FuncLimitNegInfty.neg
  : FuncLimitNegInfty F x₀ → FuncLimitPosInfty (-F) x₀
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change M < -F.map x
  linarith [hδ' x h_x]

@theorem LeftLimitPosInfty.neg
  : LeftLimitPosInfty F x₀ → LeftLimitNegInfty (-F) x₀
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change -F.map x < -M
  linarith [hδ' x h_x]

@theorem LeftLimitNegInfty.neg
  : LeftLimitNegInfty F x₀ → LeftLimitPosInfty (-F) x₀
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change M < -F.map x
  linarith [hδ' x h_x]

@theorem RightLimitPosInfty.neg
  : RightLimitPosInfty F x₀ → RightLimitNegInfty (-F) x₀
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_pos M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change -F.map x < -M
  linarith [hδ' x h_x]

@theorem RightLimitNegInfty.neg
  : RightLimitNegInfty F x₀ → RightLimitPosInfty (-F) x₀
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro M hM
  rcases h_neg M hM with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro x h_x
  change M < -F.map x
  linarith [hδ' x h_x]

@theorem PosInftyLimitPosInfty.neg
  : PosInftyLimitPosInfty F → PosInftyLimitNegInfty (-F)
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_pos K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change -F.map x < -K
  linarith [hM' x h_x]

@theorem PosInftyLimitNegInfty.neg
  : PosInftyLimitNegInfty F → PosInftyLimitPosInfty (-F)
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_neg K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change K < -F.map x
  linarith [hM' x h_x]

@theorem NegInftyLimitPosInfty.neg
  : NegInftyLimitPosInfty F → NegInftyLimitNegInfty (-F)
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_pos K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change -F.map x < -K
  linarith [hM' x h_x]

@theorem NegInftyLimitNegInfty.neg
  : NegInftyLimitNegInfty F → NegInftyLimitPosInfty (-F)
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_neg K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change K < -F.map x
  linarith [hM' x h_x]

@theorem InftyLimitPosInfty.neg
  : InftyLimitPosInfty F → InftyLimitNegInfty (-F)
:= by
  intro ⟨h_dom, h_pos⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_pos K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change -F.map x < -K
  linarith [hM' x h_x]

@theorem InftyLimitNegInfty.neg
  : InftyLimitNegInfty F → InftyLimitPosInfty (-F)
:= by
  intro ⟨h_dom, h_neg⟩
  refine ⟨h_dom, ?_⟩
  intro K hK
  rcases h_neg K hK with ⟨M, hM, hM'⟩
  refine ⟨M, hM, ?_⟩
  intro x h_x
  change K < -F.map x
  linarith [hM' x h_x]

@theorem SeqLimitInfty.notBounded
  : SeqLimitInfty A → ¬ SeqBounded A
:= by
  intro ⟨h_final, h⟩ h_bounded
  have h_bounded' : ∃ B > 0, ∀ n ∈ Ici A.init, |A.map n| < B := by
    simpa [SeqBounded, h_final] using h_bounded
  rcases h_bounded' with ⟨B, hB, h_bound⟩
  rcases h B hB with ⟨N, hN⟩
  have hn_init : N + A.init + 1 ∈ Ici A.init := by
    simp only [mem_Ici]
    omega
  have hn_gt : N + A.init + 1 > N := by
    omega
  have h_abs := h_bound (N + A.init + 1) hn_init
  have h_large := hN (N + A.init + 1) hn_gt
  linarith

@theorem FuncLimitInfty.notBounded
  : FuncLimitInfty F x₀ → ¬ FuncLocalBounded F x₀
:= by
  intro ⟨h_dom, h_inf⟩ ⟨δ₀, hδ₀, M, hM, h_bound⟩
  rcases h_dom with ⟨δ₁, hδ₁, hδ₁'⟩
  have hM1 : 0 < M + 1 := by linarith
  rcases h_inf (M + 1) hM1 with ⟨δ₂, hδ₂, hδ₂'⟩
  let d := min δ₀ (min δ₁ δ₂)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hd₁ : d ≤ δ₁ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_left δ₁ δ₂)
  have hd₂ : d ≤ δ₂ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_right δ₁ δ₂)
  have hd₁ : d ≤ δ₁ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_left δ₁ δ₂)
  have hd₂ : d ≤ δ₂ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_right δ₁ δ₂)
  let x := x₀ - d / 2
  have h_x_nbho : x ∈ Nbho x₀ δ₀ := by
    change x₀ - δ₀ < x ∧ x < x₀ + δ₀
    dsimp [x, d]
    constructor <;> linarith [min_le_left δ₀ (min δ₁ δ₂)]
  have h_x_dom_nbhd : x ∈ Nbhd x₀ δ₁ := by
    change x₀ - δ₁ < x ∧ x < x₀ + δ₁ ∧ x ≠ x₀
    dsimp [x, d]
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hd₁, hd]
  have h_x_dom : x ∈ F.domain := hδ₁' h_x_dom_nbhd
  have h_bound' : |F.map x| < M := h_bound x ⟨h_x_dom, h_x_nbho⟩
  have h_large : M + 1 < |F.map x| := by
    have h_x_nbhd₂ : x ∈ Nbhd x₀ δ₂ := by
      change x₀ - δ₂ < x ∧ x < x₀ + δ₂ ∧ x ≠ x₀
      dsimp [x, d]
      refine ⟨?_, ?_, ?_⟩ <;> linarith [hd₂, hd]
    exact hδ₂' x h_x_nbhd₂
  linarith

@theorem LeftLimitInfty.notBounded
  : LeftLimitInfty F x₀ → ¬ FuncLocalBounded F x₀
:= by
  intro ⟨h_dom, h_inf⟩ ⟨δ₀, hδ₀, M, hM, h_bound⟩
  rcases h_dom with ⟨δ₁, hδ₁, hδ₁'⟩
  have hM1 : 0 < M + 1 := by linarith
  rcases h_inf (M + 1) hM1 with ⟨δ₂, hδ₂, hδ₂'⟩
  let d := min δ₀ (min δ₁ δ₂)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hd₁ : d ≤ δ₁ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_left δ₁ δ₂)
  have hd₂ : d ≤ δ₂ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_right δ₁ δ₂)
  let x := x₀ - d / 2
  have h_x_left : x ∈ Ioo (x₀ - δ₂) x₀ := by
    dsimp [x, d]
    constructor <;>
      linarith [hd₂, hδ₂]
  have h_x_nbho : x ∈ Nbho x₀ δ₀ := by
    change x₀ - δ₀ < x ∧ x < x₀ + δ₀
    dsimp [x, d]
    constructor <;> linarith [min_le_left δ₀ (min δ₁ δ₂)]
  have h_x_dom_left : x ∈ Ioo (x₀ - δ₁) x₀ := by
    change x₀ - δ₁ < x ∧ x < x₀
    dsimp [x, d]
    constructor <;> linarith [hd₁, hd]
  have h_x_dom : x ∈ F.domain := hδ₁' h_x_dom_left
  have h_bound' : |F.map x| < M := h_bound x ⟨h_x_dom, h_x_nbho⟩
  have h_large : M + 1 < |F.map x| := hδ₂' x h_x_left
  linarith

@theorem RightLimitInfty.notBounded
  : RightLimitInfty F x₀ → ¬ FuncLocalBounded F x₀
:= by
  intro ⟨h_dom, h_inf⟩ ⟨δ₀, hδ₀, M, hM, h_bound⟩
  rcases h_dom with ⟨δ₁, hδ₁, hδ₁'⟩
  have hM1 : 0 < M + 1 := by linarith
  rcases h_inf (M + 1) hM1 with ⟨δ₂, hδ₂, hδ₂'⟩
  let d := min δ₀ (min δ₁ δ₂)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hd₁ : d ≤ δ₁ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_left δ₁ δ₂)
  have hd₂ : d ≤ δ₂ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_right δ₁ δ₂)
  have hd₁ : d ≤ δ₁ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_left δ₁ δ₂)
  have hd₂ : d ≤ δ₂ := by
    dsimp [d]
    exact le_trans (min_le_right δ₀ (min δ₁ δ₂)) (min_le_right δ₁ δ₂)
  let x := x₀ + d / 2
  have h_x_right : x ∈ Ioo x₀ (x₀ + δ₂) := by
    dsimp [x, d]
    constructor <;>
      linarith [hd₂, hδ₂]
  have h_x_nbho : x ∈ Nbho x₀ δ₀ := by
    change x₀ - δ₀ < x ∧ x < x₀ + δ₀
    dsimp [x, d]
    constructor <;> linarith [min_le_left δ₀ (min δ₁ δ₂)]
  have h_x_dom_right : x ∈ Ioo x₀ (x₀ + δ₁) := by
    change x₀ < x ∧ x < x₀ + δ₁
    dsimp [x, d]
    constructor <;> linarith [hd₁, hd]
  have h_x_dom : x ∈ F.domain := hδ₁' h_x_dom_right
  have h_bound' : |F.map x| < M := h_bound x ⟨h_x_dom, h_x_nbho⟩
  have h_large : M + 1 < |F.map x| := hδ₂' x h_x_right
  linarith

@theorem PosInftyLimitInfty.notBounded
  : PosInftyLimitInfty F → ¬ FuncLocalBounded_PosInfty F
:= by
  intro ⟨h_dom, h_inf⟩ ⟨M₁, hM₁, M₂, hM₂, h_bound⟩
  rcases h_dom with ⟨M₃, hM₃, hM₃'⟩
  have hM₂1 : 0 < M₂ + 1 := by linarith
  rcases h_inf (M₂ + 1) hM₂1 with ⟨M₄, hM₄, hM₄'⟩
  let x := max (max M₁ M₃) M₄ + 1
  have h_x_M₁ : M₁ ≤ x := by
    dsimp [x]
    linarith [le_max_left M₁ M₃, le_max_left (max M₁ M₃) M₄]
  have h_x_M₃ : M₃ < x := by
    dsimp [x]
    linarith [le_max_right M₁ M₃, le_max_left (max M₁ M₃) M₄]
  have h_x_M₄ : M₄ < x := by
    dsimp [x]
    linarith [le_max_right (max M₁ M₃) M₄]
  have h_x : x ∈ Ioi M₄ := by
    exact h_x_M₄
  have h_x_bound : x ∈ Ici M₁ := by
    exact h_x_M₁
  have h_x_dom' : x ∈ Ioi M₃ := by
    exact h_x_M₃
  have h_x_dom : x ∈ F.domain := hM₃' h_x_dom'
  have h_bound' : |F.map x| < M₂ := h_bound x ⟨h_x_dom, h_x_bound⟩
  have h_large : M₂ + 1 < |F.map x| := hM₄' x h_x
  linarith

@theorem NegInftyLimitInfty.notBounded
  : NegInftyLimitInfty F → ¬ FuncLocalBounded_NegInfty F
:= by
  intro ⟨h_dom, h_inf⟩ ⟨M₁, hM₁, M₂, hM₂, h_bound⟩
  rcases h_dom with ⟨M₃, hM₃, hM₃'⟩
  have hM₂1 : 0 < M₂ + 1 := by linarith
  rcases h_inf (M₂ + 1) hM₂1 with ⟨M₄, hM₄, hM₄'⟩
  let x := -(max (max M₁ M₃) M₄ + 1)
  have h_x_M₁ : x ≤ -M₁ := by
    dsimp [x]
    linarith [le_max_left M₁ M₃, le_max_left (max M₁ M₃) M₄]
  have h_x_M₃ : x < -M₃ := by
    dsimp [x]
    linarith [le_max_right M₁ M₃, le_max_left (max M₁ M₃) M₄]
  have h_x_M₄ : x < -M₄ := by
    dsimp [x]
    linarith [le_max_right (max M₁ M₃) M₄]
  have h_x : x ∈ Iio (-M₄) := by
    exact h_x_M₄
  have h_x_bound : x ∈ Iic (-M₁) := by
    exact h_x_M₁
  have h_x_dom' : x ∈ Iio (-M₃) := by
    exact h_x_M₃
  have h_x_dom : x ∈ F.domain := hM₃' h_x_dom'
  have h_bound' : |F.map x| < M₂ := h_bound x ⟨h_x_dom, h_x_bound⟩
  have h_large : M₂ + 1 < |F.map x| := hM₄' x h_x
  linarith

@theorem InftyLimitInfty.notBounded
  : InftyLimitInfty F → ¬ FuncBounded F
:= by
  intro ⟨h_dom, h_inf⟩ ⟨B, hB, h_bound⟩
  rcases h_inf (B + 1) (by linarith) with ⟨M, hM, hM'⟩
  rcases h_dom with ⟨X, hX, hXpos, hXneg⟩
  let x := max M X + 1
  have h_x : x ∈ Ioi M := by
    change M < max M X + 1
    linarith [le_max_left M X]
  have h_x_bound : x ∈ F.domain := by
    apply hXpos
    change X < x
    dsimp [x]
    linarith [le_max_right M X]
  have h_bound' : |F.map x| < B := h_bound x h_x_bound
  have h_large : B + 1 < |F.map x| := hM' x (Or.inl h_x)
  linarith

theorem SeqLimitPosInfty.notFinite
  : SeqLimitPosInfty A → ¬ SeqConverges A
:= by
  intro h h_contra
  exact (SeqLimitInfty.notBounded (SeqLimitPosInfty.toSeqLimitInfty h))
    (SeqLimit_Bounded h_contra)

theorem SeqLimitNegInfty.notFinite
  : SeqLimitNegInfty A → ¬ SeqConverges A
:= by
  intro h h_contra
  exact (SeqLimitInfty.notBounded (SeqLimitNegInfty.toSeqLimitInfty h))
    (SeqLimit_Bounded h_contra)

theorem SeqLimitInfty.notFinite
  : SeqLimitInfty A → ¬ SeqConverges A
:= by
  intro h h_contra
  exact (SeqLimitInfty.notBounded h) (SeqLimit_Bounded h_contra)

theorem SeqLimitPosInfty.notNegInfty
  : SeqLimitPosInfty A → ¬ SeqLimitNegInfty A
:= by
  intro h h_contra
  rcases h.2 1 (by norm_num) with ⟨Nn, hNn⟩
  rcases h_contra.2 1 (by norm_num) with ⟨Np, hNp⟩
  let n := max Nn Np + 1
  have hn' : A.map n < -1 := hNp n (by omega)
  have hp' : A.map n > 1 := hNn n (by omega)
  linarith

theorem SeqLimitNegInfty.notPosInfty
  : SeqLimitNegInfty A → ¬ SeqLimitPosInfty A
:= Imp.swap.mp SeqLimitPosInfty.notNegInfty

theorem FuncLimitPosInfty.notFinite
  : FuncLimitPosInfty F x₀ → ¬ FuncConvergesAt F x₀
:= by
  intro h h_contra
  exact (FuncLimitInfty.notBounded (FuncLimitPosInfty.toFuncLimitInfty h))
    (FuncLimit_Bounded h_contra)

theorem FuncLimitNegInfty.notFinite
  : FuncLimitNegInfty F x₀ → ¬ FuncConvergesAt F x₀
:= by
  intro h h_contra
  exact (FuncLimitInfty.notBounded (FuncLimitNegInfty.toFuncLimitInfty h))
    (FuncLimit_Bounded h_contra)

theorem FuncLimitInfty.notFinite
  : FuncLimitInfty F x₀ → ¬ FuncConvergesAt F x₀
:= by
  intro h h_contra
  exact (FuncLimitInfty.notBounded h) (FuncLimit_Bounded h_contra)

theorem FuncLimitPosInfty.notNegInfty
  : FuncLimitPosInfty F x₀ → ¬ FuncLimitNegInfty F x₀
:= by
  intro h_neg h_pos
  rcases h_neg.2 1 (by norm_num) with ⟨δ_neg, hδ_neg, h_neg⟩
  rcases h_pos.2 1 (by norm_num) with ⟨δ_pos, hδ_pos, h_pos⟩
  let δ := min δ_neg δ_pos
  let x := x₀ + δ / 2
  have hδ : 0 < δ := lt_min hδ_neg hδ_pos
  have h_x_neg : x ∈ Nbhd x₀ δ_neg := by
    change x₀ - δ_neg < x ∧ x < x₀ + δ_neg ∧ x ≠ x₀
    dsimp [x, δ]
    refine ⟨?_, ?_, ?_⟩ <;> linarith [min_le_left δ_neg δ_pos, hδ]
  have h_x_pos : x ∈ Nbhd x₀ δ_pos := by
    change x₀ - δ_pos < x ∧ x < x₀ + δ_pos ∧ x ≠ x₀
    dsimp [x, δ]
    refine ⟨?_, ?_, ?_⟩ <;> linarith [min_le_right δ_neg δ_pos, hδ]
  linarith [h_neg x h_x_neg, h_pos x h_x_pos]

theorem FuncLimitNegInfty.notPosInfty
  : FuncLimitNegInfty F x₀ → ¬ FuncLimitPosInfty F x₀
:= Imp.swap.mp FuncLimitPosInfty.notNegInfty

theorem LeftLimitPosInfty.notFinite
  : LeftLimitPosInfty F x₀ → ¬ LeftConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ - δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo (x₀ - δ_inf) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo (x₀ - δ_lim) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_large : |L| + 2 < |F.map x| :=
    lt_of_lt_of_le (h_inf x h_x_inf) (le_abs_self _)
  linarith

theorem LeftLimitNegInfty.notFinite
  : LeftLimitNegInfty F x₀ → ¬ LeftConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ - δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo (x₀ - δ_inf) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo (x₀ - δ_lim) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_map_neg : F.map x < 0 := by
    linarith [abs_nonneg L, h_inf x h_x_inf]
  rw [abs_of_neg h_map_neg] at h_abs
  linarith [h_inf x h_x_inf]

theorem LeftLimitInfty.notFinite
  : LeftLimitInfty F x₀ → ¬ LeftConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ - δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo (x₀ - δ_inf) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo (x₀ - δ_lim) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  linarith [h_inf x h_x_inf]

theorem LeftLimitPosInfty.notNegInfty
  : LeftLimitPosInfty F x₀ → ¬ LeftLimitNegInfty F x₀
:= by
  intro h_pos h_neg
  rcases h_pos.2 1 (by norm_num) with ⟨δ_pos, hδ_pos, h_pos⟩
  rcases h_neg.2 1 (by norm_num) with ⟨δ_neg, hδ_neg, h_neg⟩
  let δ := min δ_neg δ_pos
  let x := x₀ - δ / 2
  have hδ : 0 < δ := lt_min hδ_neg hδ_pos
  have h_x_neg : x ∈ Ioo (x₀ - δ_neg) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_neg δ_pos, hδ]
  have h_x_pos : x ∈ Ioo (x₀ - δ_pos) x₀ := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_neg δ_pos, hδ]
  linarith [h_neg x h_x_neg, h_pos x h_x_pos]

theorem LeftLimitNegInfty.notPosInfty
  : LeftLimitNegInfty F x₀ → ¬ LeftLimitPosInfty F x₀
:= Imp.swap.mp LeftLimitPosInfty.notNegInfty

theorem RightLimitPosInfty.notFinite
  : RightLimitPosInfty F x₀ → ¬ RightConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ + δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo x₀ (x₀ + δ_inf) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo x₀ (x₀ + δ_lim) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_large : |L| + 2 < |F.map x| :=
    lt_of_lt_of_le (h_inf x h_x_inf) (le_abs_self _)
  linarith

theorem RightLimitNegInfty.notFinite
  : RightLimitNegInfty F x₀ → ¬ RightConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ + δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo x₀ (x₀ + δ_inf) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo x₀ (x₀ + δ_lim) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_map_neg : F.map x < 0 := by
    linarith [abs_nonneg L, h_inf x h_x_inf]
  rw [abs_of_neg h_map_neg] at h_abs
  linarith [h_inf x h_x_inf]

theorem RightLimitInfty.notFinite
  : RightLimitInfty F x₀ → ¬ RightConvergesAt F x₀
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨δ_inf, hδ_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨δ_lim, hδ_lim, h_lim⟩
  let δ := min δ_inf δ_lim
  let x := x₀ + δ / 2
  have hδ : 0 < δ := lt_min hδ_inf hδ_lim
  have h_x_inf : x ∈ Ioo x₀ (x₀ + δ_inf) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_inf δ_lim, hδ]
  have h_x_lim : x ∈ Ioo x₀ (x₀ + δ_lim) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_inf δ_lim, hδ]
  have h_near := h_lim x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  linarith [h_inf x h_x_inf]

theorem RightLimitPosInfty.notNegInfty
  : RightLimitPosInfty F x₀ → ¬ RightLimitNegInfty F x₀
:= by
  intro h_pos h_neg
  rcases h_pos.2 1 (by norm_num) with ⟨δ_pos, hδ_pos, h_pos⟩
  rcases h_neg.2 1 (by norm_num) with ⟨δ_neg, hδ_neg, h_neg⟩
  let δ := min δ_neg δ_pos
  let x := x₀ + δ / 2
  have hδ : 0 < δ := lt_min hδ_neg hδ_pos
  have h_x_neg : x ∈ Ioo x₀ (x₀ + δ_neg) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_left δ_neg δ_pos, hδ]
  have h_x_pos : x ∈ Ioo x₀ (x₀ + δ_pos) := by
    dsimp [x, δ]
    constructor <;> linarith [min_le_right δ_neg δ_pos, hδ]
  linarith [h_neg x h_x_neg, h_pos x h_x_pos]

theorem RightLimitNegInfty.notPosInfty
  : RightLimitNegInfty F x₀ → ¬ RightLimitPosInfty F x₀
:= Imp.swap.mp RightLimitPosInfty.notNegInfty

theorem PosInftyLimitPosInfty.notFinite
  : PosInftyLimitPosInfty F → ¬ ConvergesAtPosInfty F
:= by
  intro h h_contra
  exact (PosInftyLimitInfty.notBounded (PosInftyLimitPosInfty.toPosInftyLimitInfty h))
    (PosInftyLimit_Bounded h_contra)

theorem PosInftyLimitNegInfty.notFinite
  : PosInftyLimitNegInfty F → ¬ ConvergesAtPosInfty F
:= by
  intro h h_contra
  exact (PosInftyLimitInfty.notBounded (PosInftyLimitNegInfty.toPosInftyLimitInfty h))
    (PosInftyLimit_Bounded h_contra)

theorem PosInftyLimitInfty.notFinite
  : PosInftyLimitInfty F → ¬ ConvergesAtPosInfty F
:= by
  intro h h_contra
  exact (PosInftyLimitInfty.notBounded h) (PosInftyLimit_Bounded h_contra)

theorem PosInftyLimitPosInfty.notNegInfty
  : PosInftyLimitPosInfty F → ¬ PosInftyLimitNegInfty F
:= by
  intro h_pos h_neg
  rcases h_pos.2 1 (by norm_num) with ⟨X_pos, hX_pos, h_pos⟩
  rcases h_neg.2 1 (by norm_num) with ⟨X_neg, hX_neg, h_neg⟩
  let x := max X_neg X_pos + 1
  have h_x_neg : x ∈ Ioi X_neg := by
    change X_neg < max X_neg X_pos + 1
    linarith [le_max_left X_neg X_pos]
  have h_x_pos : x ∈ Ioi X_pos := by
    change X_pos < max X_neg X_pos + 1
    linarith [le_max_right X_neg X_pos]
  linarith [h_neg x h_x_neg, h_pos x h_x_pos]

theorem PosInftyLimitNegInfty.notPosInfty
  : PosInftyLimitNegInfty F → ¬ PosInftyLimitPosInfty F
:= Imp.swap.mp PosInftyLimitPosInfty.notNegInfty

theorem NegInftyLimitPosInfty.notFinite
  : NegInftyLimitPosInfty F → ¬ ConvergesAtNegInfty F
:= by
  intro h h_contra
  exact (NegInftyLimitInfty.notBounded (NegInftyLimitPosInfty.toNegInftyLimitInfty h))
    (NegInftyLimit_Bounded h_contra)

theorem NegInftyLimitNegInfty.notFinite
  : NegInftyLimitNegInfty F → ¬ ConvergesAtNegInfty F
:= by
  intro h h_contra
  exact (NegInftyLimitInfty.notBounded (NegInftyLimitNegInfty.toNegInftyLimitInfty h))
    (NegInftyLimit_Bounded h_contra)

theorem NegInftyLimitInfty.notFinite
  : NegInftyLimitInfty F → ¬ ConvergesAtNegInfty F
:= by
  intro h h_contra
  exact (NegInftyLimitInfty.notBounded h) (NegInftyLimit_Bounded h_contra)

theorem NegInftyLimitPosInfty.notNegInfty
  : NegInftyLimitPosInfty F → ¬ NegInftyLimitNegInfty F
:= by
  intro h_pos h_neg
  rcases h_pos.2 1 (by norm_num) with ⟨X_pos, hX_pos, h_pos⟩
  rcases h_neg.2 1 (by norm_num) with ⟨X_neg, hX_neg, h_neg⟩
  let x := -(max X_neg X_pos + 1)
  have h_x_neg : x ∈ Iio (-X_neg) := by
    change -(max X_neg X_pos + 1) < -X_neg
    linarith [le_max_left X_neg X_pos]
  have h_x_pos : x ∈ Iio (-X_pos) := by
    change -(max X_neg X_pos + 1) < -X_pos
    linarith [le_max_right X_neg X_pos]
  linarith [h_neg x h_x_neg, h_pos x h_x_pos]

theorem NegInftyLimitNegInfty.notPosInfty
  : NegInftyLimitNegInfty F → ¬ NegInftyLimitPosInfty F
:= Imp.swap.mp NegInftyLimitPosInfty.notNegInfty

theorem InftyLimitPosInfty.notFinite
  : InftyLimitPosInfty F → ¬ ConvergesAtInfty F
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨X_inf, hX_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨X_lim, hX_lim, h_lim_neg, h_lim_pos⟩
  let x := max X_inf X_lim + 1
  have h_x_inf : x ∈ Ioi X_inf := by
    change X_inf < max X_inf X_lim + 1
    linarith [le_max_left X_inf X_lim]
  have h_x_lim : x ∈ Ioi X_lim := by
    change X_lim < max X_inf X_lim + 1
    linarith [le_max_right X_inf X_lim]
  have h_near := h_lim_pos x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_large : |L| + 2 < |F.map x| :=
    lt_of_lt_of_le (h_inf x (Or.inl h_x_inf)) (le_abs_self _)
  linarith

theorem InftyLimitNegInfty.notFinite
  : InftyLimitNegInfty F → ¬ ConvergesAtInfty F
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨X_inf, hX_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨X_lim, hX_lim, h_lim_neg, h_lim_pos⟩
  let x := max X_inf X_lim + 1
  have h_x_inf : x ∈ Ioi X_inf := by
    change X_inf < max X_inf X_lim + 1
    linarith [le_max_left X_inf X_lim]
  have h_x_lim : x ∈ Ioi X_lim := by
    change X_lim < max X_inf X_lim + 1
    linarith [le_max_right X_inf X_lim]
  have h_near := h_lim_pos x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  have h_map_neg : F.map x < 0 := by
    linarith [abs_nonneg L, h_inf x (Or.inl h_x_inf)]
  rw [abs_of_neg h_map_neg] at h_abs
  linarith [h_inf x (Or.inl h_x_inf)]

theorem InftyLimitInfty.notFinite
  : InftyLimitInfty F → ¬ ConvergesAtInfty F
:= by
  intro h h_contra
  rcases h_contra with ⟨L, hL⟩
  rcases h.2 (|L| + 2) (by positivity) with ⟨X_inf, hX_inf, h_inf⟩
  rcases hL.2 1 (by norm_num) with ⟨X_lim, hX_lim, h_lim_neg, h_lim_pos⟩
  let x := max X_inf X_lim + 1
  have h_x_inf : x ∈ Ioi X_inf := by
    change X_inf < max X_inf X_lim + 1
    linarith [le_max_left X_inf X_lim]
  have h_x_lim : x ∈ Ioi X_lim := by
    change X_lim < max X_inf X_lim + 1
    linarith [le_max_right X_inf X_lim]
  have h_near := h_lim_pos x h_x_lim
  rw [Nbho_abs] at h_near
  have h_abs : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  linarith [h_inf x (Or.inl h_x_inf)]

theorem InftyLimitPosInfty.notNegInfty
  : InftyLimitPosInfty F → ¬ InftyLimitNegInfty F
:= by
  intro h_pos h_neg
  rcases h_pos.2 1 (by norm_num) with ⟨X_pos, hX_pos, h_pos⟩
  rcases h_neg.2 1 (by norm_num) with ⟨X_neg, hX_neg, h_neg⟩
  let x := max X_neg X_pos + 1
  have h_x_neg : x ∈ Ioi X_neg := by
    change X_neg < max X_neg X_pos + 1
    linarith [le_max_left X_neg X_pos]
  have h_x_pos : x ∈ Ioi X_pos := by
    change X_pos < max X_neg X_pos + 1
    linarith [le_max_right X_neg X_pos]
  linarith [h_neg x (Or.inl h_x_neg), h_pos x (Or.inl h_x_pos)]

theorem InftyLimitNegInfty.notPosInfty
  : InftyLimitNegInfty F → ¬ InftyLimitPosInfty F
:= Imp.swap.mp InftyLimitPosInfty.notNegInfty

end


page_end
