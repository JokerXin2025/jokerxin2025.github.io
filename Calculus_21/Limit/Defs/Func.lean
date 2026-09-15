/-
    «Calculus_21».Limit.Defs.Func
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Function.Concepts
set_option linter.style.header false


/-! # Definitions of Function Limit -/

section
variable (F : Function) (x₀ L : ℝ)

/-- Function Limit -/
def FuncLimit : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, F.map x ∈ Nbho L ε)

def FuncConvergesAt : Prop :=
  ∃ L : ℝ, FuncLimit F x₀ L

/-- (Function's) Left Limit -/
def LeftLimit : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x ∈ Nbho L ε)

def LeftConvergesAt : Prop :=
  ∃ L : ℝ, LeftLimit F x₀ L

/-- (Function's) Right Limit -/
def RightLimit : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x ∈ Nbho L ε)

def RightConvergesAt : Prop :=
  ∃ L : ℝ, RightLimit F x₀ L

/-- (Function's) Limit at Positive Infinity -/
def PosInftyLimit : Prop :=
  (∃ M > 0, Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

def ConvergesAtPosInfty : Prop :=
  ∃ L : ℝ, PosInftyLimit F L

/-- (Function's) Limit at Negative Infinity -/
def NegInftyLimit : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)

def ConvergesAtNegInfty : Prop :=
  ∃ L : ℝ, NegInftyLimit F L

/-- (Function's) Limit at Infinity -/
def InftyLimit : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain ∧ Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      (∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)
      ∧ (∀ x ∈ Ioi M, F.map x ∈ Nbho L ε))

def ConvergesAtInfty : Prop :=
  ∃ L : ℝ, InftyLimit F L

end


/-! # Properties of Function Limit -/

section
variable {F G : Function} {x₀ L L₁ L₂ : ℝ}

@lemma LimitUniqueLemma
    (h : ∀ ε > 0, ∃ y : ℝ, y ∈ Nbho L₁ ε ∧ y ∈ Nbho L₂ ε)
  : L₁ = L₂
:= by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · rcases h ((L₂ - L₁) / 3) (by linarith) with ⟨y, h1, h2⟩
    rcases h1 with ⟨h1l, h1r⟩
    rcases h2 with ⟨h2l, h2r⟩
    linarith
  · rcases h ((L₁ - L₂) / 3) (by linarith) with ⟨y, h1, h2⟩
    rcases h1 with ⟨h1l, h1r⟩
    rcases h2 with ⟨h2l, h2r⟩
    linarith

/-- Uniqueness of Function Limit -/
@theorem FuncLimit_Unique
    (h₁ : FuncLimit F x₀ L₁) (h₂ : FuncLimit F x₀ L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨δ₁, hδ₁, h₁⟩
  rcases h₂.2 ε h_ε with ⟨δ₂, hδ₂, h₂⟩
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have h_x₁ : x₀ + δ / 2 ∈ Nbhd x₀ δ₁ := by
    dsimp [Nbhd]
    exact ⟨by linarith [min_le_left δ₁ δ₂], by linarith [hδ₁, min_le_left δ₁ δ₂],
      by linarith [hδ]⟩
  have h_x₂ : x₀ + δ / 2 ∈ Nbhd x₀ δ₂ := by
    dsimp [Nbhd]
    exact ⟨by linarith [min_le_right δ₁ δ₂], by linarith [hδ₂, min_le_right δ₁ δ₂],
      by linarith [hδ]⟩
  exact ⟨F.map (x₀ + δ / 2), h₁ _ h_x₁, h₂ _ h_x₂⟩

/-- Local Boundedness of Convergent Function -/
@theorem FuncLimit_Bounded
    (h_conv : FuncConvergesAt F x₀)
  : FuncLocalBounded F x₀
:= by
  rcases h_conv with ⟨L, hL⟩
  rcases hL with ⟨hdom, hlim⟩
  rcases hdom with ⟨δ₁, hδ₁, hdomain⟩
  rcases hlim 1 (by norm_num) with ⟨δ₂, hδ₂, hmap⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, |L| + |F.map x₀| + 2,
    by positivity, ?_⟩
  intro x h_x
  by_cases h_x0 : x = x₀
  · subst x
    linarith [abs_nonneg L]
  · have h_x2 : x ∈ Nbhd x₀ δ₂ := by
      rcases h_x.2 with ⟨hlo, hhi⟩
      exact ⟨by linarith [min_le_right δ₁ δ₂],
        by linarith [min_le_right δ₁ δ₂], h_x0⟩
    have hv := hmap x h_x2
    rw [Nbho_abs] at hv
    have htri : |F.map x| ≤ |F.map x - L| + |L| := by
      calc
        |F.map x| = |(F.map x - L) + L| := by ring_nf
        _ ≤ |F.map x - L| + |L| := abs_add_le _ _
    linarith [abs_nonneg (F.map x₀)]

/-- Uniqueness of Left Limit -/
@theorem LeftLimit_Unique
    (h₁ : LeftLimit F x₀ L₁) (h₂ : LeftLimit F x₀ L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨δ₁, hδ₁, h₁⟩
  rcases h₂.2 ε h_ε with ⟨δ₂, hδ₂, h₂⟩
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have h_x₁ : x₀ - δ / 2 ∈ Ioo (x₀ - δ₁) x₀ := by
    exact ⟨by linarith [min_le_left δ₁ δ₂], by linarith [hδ]⟩
  have h_x₂ : x₀ - δ / 2 ∈ Ioo (x₀ - δ₂) x₀ := by
    exact ⟨by linarith [min_le_right δ₁ δ₂], by linarith [hδ]⟩
  exact ⟨F.map (x₀ - δ / 2), h₁ _ h_x₁, h₂ _ h_x₂⟩

/-- Uniqueness of Right Limit -/
@theorem RightLimit_Unique
    (h₁ : RightLimit F x₀ L₁) (h₂ : RightLimit F x₀ L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨δ₁, hδ₁, h₁⟩
  rcases h₂.2 ε h_ε with ⟨δ₂, hδ₂, h₂⟩
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have h_x₁ : x₀ + δ / 2 ∈ Ioo x₀ (x₀ + δ₁) := by
    exact ⟨by linarith [hδ], by linarith [hδ₁, min_le_left δ₁ δ₂]⟩
  have h_x₂ : x₀ + δ / 2 ∈ Ioo x₀ (x₀ + δ₂) := by
    exact ⟨by linarith [hδ], by linarith [hδ₂, min_le_right δ₁ δ₂]⟩
  exact ⟨F.map (x₀ + δ / 2), h₁ _ h_x₁, h₂ _ h_x₂⟩

/-- Uniqueness of Limit at Positive Infinity -/
@theorem PosInftyLimit_Unique
    (h₁ : PosInftyLimit F L₁) (h₂ : PosInftyLimit F L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨M₁, hM₁, h₁⟩
  rcases h₂.2 ε h_ε with ⟨M₂, hM₂, h₂⟩
  exact ⟨F.map (max M₁ M₂ + 1), h₁ _ (by change M₁ < max M₁ M₂ + 1; linarith [le_max_left M₁ M₂]),
    h₂ _ (by change M₂ < max M₁ M₂ + 1; linarith [le_max_right M₁ M₂])⟩

/-- Local Boundedness of Function Convergent at Positive Infinity -/
@theorem PosInftyLimit_Bounded
    (h_conv : ConvergesAtPosInfty F)
  : FuncLocalBounded_PosInfty F
:= by
  rcases h_conv with ⟨L, hL⟩
  rcases hL with ⟨hdom, hlim⟩
  rcases hlim 1 (by norm_num) with ⟨M, hM, hmap⟩
  refine ⟨M + 1, by linarith, |L| + 2, by positivity, ?_⟩
  intro x h_x
  have h_xM : x ∈ Ioi M := by
    change M < x
    rcases h_x with ⟨_, h_xle⟩
    change M + 1 ≤ x at h_xle
    linarith
  have hv := hmap x h_xM
  rw [Nbho_abs] at hv
  have htri : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  linarith

/-- Uniqueness of Limit at Negative Infinity -/
@theorem NegInftyLimit_Unique
    (h₁ : NegInftyLimit F L₁) (h₂ : NegInftyLimit F L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨M₁, hM₁, h₁⟩
  rcases h₂.2 ε h_ε with ⟨M₂, hM₂, h₂⟩
  exists F.map (-(max M₁ M₂ + 1))
  constructor
  · exact h₁ _ (by change -(max M₁ M₂ + 1) < -M₁; linarith [le_max_left M₁ M₂])
  · exact h₂ _ (by change -(max M₁ M₂ + 1) < -M₂; linarith [le_max_right M₁ M₂])

/-- Local Boundedness of Function Convergent at Negative Infinity -/
@theorem NegInftyLimit_Bounded
    (h_conv : ConvergesAtNegInfty F)
  : FuncLocalBounded_NegInfty F
:= by
  rcases h_conv with ⟨L, hL⟩
  rcases hL with ⟨hdom, hlim⟩
  rcases hlim 1 (by norm_num) with ⟨M, hM, hmap⟩
  refine ⟨M + 1, by linarith, |L| + 2, by positivity, ?_⟩
  intro x h_x
  have h_xM : x ∈ Iio (-M) := by
    change x < -M
    rcases h_x with ⟨_, h_xle⟩
    change x ≤ -(M + 1) at h_xle
    linarith
  have hv := hmap x h_xM
  rw [Nbho_abs] at hv
  have htri : |F.map x| ≤ |F.map x - L| + |L| := by
    calc
      |F.map x| = |(F.map x - L) + L| := by ring_nf
      _ ≤ |F.map x - L| + |L| := abs_add_le _ _
  linarith

/-- Uniqueness of Limit at Infinity -/
@theorem InftyLimit_Unique
    (h₁ : InftyLimit F L₁) (h₂ : InftyLimit F L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨M₁, hM₁, h₁neg, h₁pos⟩
  rcases h₂.2 ε h_ε with ⟨M₂, hM₂, h₂neg, h₂pos⟩
  refine ⟨F.map (max M₁ M₂ + 1), ?_, ?_⟩
  · apply h₁pos
    change M₁ < max M₁ M₂ + 1
    linarith [le_max_left M₁ M₂]
  · apply h₂pos
    change M₂ < max M₁ M₂ + 1
    linarith [le_max_right M₁ M₂]

/-- Congruence of Function Limit -/
@theorem FuncLimit.Congr
    (h_lim : FuncLimit F x₀ L)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain
                        ∧ ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= by
  rcases h_lim with ⟨hdom, h_ε⟩
  rcases h_congr with ⟨δ, hδ, hGdom, heq⟩
  constructor
  · exact ⟨δ, hδ, hGdom⟩
  · intro ε h_ε'
    rcases h_ε ε h_ε' with ⟨η, hη, hmap⟩
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro x h_x
    have h_xδ : x ∈ Nbhd x₀ δ := by
      rcases h_x with ⟨h_xlo, h_xhi, h_xne⟩
      exact ⟨by linarith [min_le_left δ η],
        by linarith [min_le_left δ η], h_xne⟩
    rw [← heq x h_xδ]
    apply hmap x
    rcases h_x with ⟨h_xlo, h_xhi, h_xne⟩
    exact ⟨by linarith [min_le_right δ η],
      by linarith [min_le_right δ η], h_xne⟩

/-- Congruence of Left Limit -/
@theorem LeftLimit.Congr
    (h_lim : LeftLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain
                        ∧ ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= by
  rcases h_lim with ⟨hdom, h_ε⟩
  rcases h_congr with ⟨δ, hδ, hGdom, heq⟩
  constructor
  · exact ⟨δ, hδ, hGdom⟩
  · intro ε h_ε'
    rcases h_ε ε h_ε' with ⟨η, hη, hmap⟩
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro x h_x
    have h_xδ : x ∈ Ioo (x₀ - δ) x₀ := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_left δ η]
    rw [← heq x h_xδ]
    exact hmap x (by
      constructor <;> linarith [h_x.1, h_x.2, min_le_right δ η])

/-- Congruence of Right Limit -/
@theorem RightLimit.Congr
    (h_lim : RightLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain
                        ∧ ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= by
  rcases h_lim with ⟨hdom, h_ε⟩
  rcases h_congr with ⟨δ, hδ, hGdom, heq⟩
  constructor
  · exact ⟨δ, hδ, hGdom⟩
  · intro ε h_ε'
    rcases h_ε ε h_ε' with ⟨η, hη, hmap⟩
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro x h_x
    have h_xδ : x ∈ Ioo x₀ (x₀ + δ) := by
      constructor <;> linarith [h_x.1, h_x.2, min_le_left δ η]
    rw [← heq x h_xδ]
    exact hmap x (by
      constructor <;> linarith [h_x.1, h_x.2, min_le_right δ η])

/-- Congruence of Limit at Positive Infinity -/
@theorem PosInftyLimit.Congr
    (h_lim : PosInftyLimit F L)
    (h_congr : ∃ M > 0, Ioi M ⊆ G.domain
                        ∧ ∀ x ∈ Ioi M, F.map x = G.map x)
  : PosInftyLimit G L
:= by
  rcases h_lim with ⟨hdom, h_ε⟩
  rcases h_congr with ⟨M, hM, hGdom, heq⟩
  constructor
  · exact ⟨M, hM, hGdom⟩
  · intro ε h_ε'
    rcases h_ε ε h_ε' with ⟨K, hK, hmap⟩
    refine ⟨max M K, lt_of_lt_of_le hM (le_max_left M K), ?_⟩
    intro x h_x
    have h_xM : x ∈ Ioi M := by
      change M < x
      change max M K < x at h_x
      exact lt_of_le_of_lt (le_max_left M K) h_x
    rw [← heq x h_xM]
    apply hmap x
    change K < x
    change max M K < x at h_x
    exact lt_of_le_of_lt (le_max_right M K) h_x

/-- Congruence of Limit at Negative Infinity -/
@theorem NegInftyLimit.Congr
    (h_lim : NegInftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain
                        ∧ ∀ x ∈ Iio (-M), F.map x = G.map x)
  : NegInftyLimit G L
:= by
  rcases h_lim with ⟨hdom, h_ε⟩
  rcases h_congr with ⟨M, hM, hGdom, heq⟩
  constructor
  · exact ⟨M, hM, hGdom⟩
  · intro ε h_ε'
    rcases h_ε ε h_ε' with ⟨K, hK, hmap⟩
    refine ⟨max M K, lt_of_lt_of_le hM (le_max_left M K), ?_⟩
    intro x h_x
    have h_xM : x ∈ Iio (-M) := by
      change x < -M
      change x < -max M K at h_x
      linarith [le_max_left M K]
    rw [← heq x h_xM]
    apply hmap x
    change x < -K
    change x < -max M K at h_x
    linarith [le_max_right M K]

/-- Congruence of Limit at Infinity -/
@theorem InftyLimit.Congr
    (h_lim : InftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain ∧ Ioi M ⊆ G.domain
                        ∧ (∀ x ∈ Iio (-M), F.map x = G.map x)
                        ∧ (∀ x ∈ Ioi M, F.map x = G.map x))
  : InftyLimit G L
:= by
  rcases h_lim with ⟨hdom, hlim⟩
  rcases h_congr with ⟨M, hM, hGneg, hGpos, heqneg, heqpos⟩
  constructor
  · exact ⟨M, hM, hGneg, hGpos⟩
  · intro ε h_ε
    rcases hlim ε h_ε with ⟨K, hK, hneg, hpos⟩
    refine ⟨max M K, lt_of_lt_of_le hM (le_max_left M K), ?_, ?_⟩
    · intro x h_x
      have h_xM : x ∈ Iio (-M) := by
        change x < -M
        change x < -max M K at h_x
        linarith [le_max_left M K]
      rw [← heqneg x h_xM]
      apply hneg x
      change x < -K
      change x < -max M K at h_x
      linarith [le_max_right M K]
    · intro x h_x
      have h_xM : x ∈ Ioi M := by
        change M < x
        change max M K < x at h_x
        exact lt_of_le_of_lt (le_max_left M K) h_x
      rw [← heqpos x h_xM]
      apply hpos x
      change K < x
      change max M K < x at h_x
      exact lt_of_le_of_lt (le_max_right M K) h_x

/-- Function Limit → Left Limit -/
@theorem FuncLimit.toLeft
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= by
  rcases h_lim with ⟨hdom, hlim⟩
  constructor
  · rcases hdom with ⟨δ, hδ, hdom⟩
    exact ⟨δ, hδ, fun x h_x => hdom ⟨h_x.1, by linarith [h_x.2, hδ], ne_of_lt h_x.2⟩⟩
  · intro ε h_ε
    rcases hlim ε h_ε with ⟨δ, hδ, hmap⟩
    exact ⟨δ, hδ, fun x h_x => hmap x ⟨h_x.1, by linarith [h_x.2, hδ], ne_of_lt h_x.2⟩⟩

/-- Function Limit → Right Limit -/
@theorem FuncLimit.toRight
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= by
  rcases h_lim with ⟨hdom, hlim⟩
  constructor
  · rcases hdom with ⟨δ, hδ, hdom⟩
    exact ⟨δ, hδ, fun x h_x => hdom ⟨by linarith [h_x.1, hδ], h_x.2, ne_of_gt h_x.1⟩⟩
  · intro ε h_ε
    rcases hlim ε h_ε with ⟨δ, hδ, hmap⟩
    exact ⟨δ, hδ, fun x h_x => hmap x ⟨by linarith [h_x.1, hδ], h_x.2, ne_of_gt h_x.1⟩⟩

/-- Limit at Infinity → Limit at Negative Infinity -/
@theorem InftyLimit.toNeg
    (h_lim : InftyLimit F L)
  : NegInftyLimit F L
:= by
  rcases h_lim with ⟨hdom, hlim⟩
  constructor
  · rcases hdom with ⟨M, hM, hneg, hpos⟩
    exact ⟨M, hM, hneg⟩
  · intro ε h_ε
    rcases hlim ε h_ε with ⟨M, hM, hneg, hpos⟩
    exact ⟨M, hM, hneg⟩

/-- Limit at Infinity → Limit at Positive Infinity -/
@theorem InftyLimit.toPos
    (h_lim : InftyLimit F L)
  : PosInftyLimit F L
:= by
  rcases h_lim with ⟨hdom, hlim⟩
  constructor
  · rcases hdom with ⟨M, hM, hneg, hpos⟩
    exact ⟨M, hM, hpos⟩
  · intro ε h_ε
    rcases hlim ε h_ε with ⟨M, hM, hneg, hpos⟩
    exact ⟨M, hM, hpos⟩

end


page_end
