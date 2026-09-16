/-
    «Calculus_21».Limit.Defs.Seq
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Sequence.Concepts
import «Calculus_21».Function.Concepts
set_option linter.style.header false


/-! # Definition of RSequence Limit -/

/-- RSequence Limit -/
def SeqLimit (A : RSequence) (L : ℝ) : Prop :=
  A.final = none
  ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, A.map n ∈ Nbho L ε

def SeqConverges (A : RSequence) : Prop :=
  ∃ L : ℝ, SeqLimit A L


/-! # Properties of RSequence Limit -/

section
variable {A B : RSequence} {L L₁ L₂ : ℝ}

private lemma LimitUniqueLemma
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

/-- Uniqueness of RSequence Limit -/
@theorem SeqLimit_Unique
    (h₁ : SeqLimit A L₁) (h₂ : SeqLimit A L₂)
  : L₁ = L₂
:= by
  apply LimitUniqueLemma
  intro ε h_ε
  rcases h₁.2 ε h_ε with ⟨N₁, hN₁⟩
  rcases h₂.2 ε h_ε with ⟨N₂, hN₂⟩
  exists A.map (max N₁ N₂ + 1)
  constructor
  · exact hN₁ _ (by omega)
  · exact hN₂ _ (by omega)

/-- Boundedness of Convergent RSequence -/
@theorem SeqLimit_Bounded
    (h_conv : SeqConverges A)
  : SeqBounded A
:= by
  rcases h_conv with ⟨L, hL⟩
  rcases hL with ⟨hfinal, hlim⟩
  simp only [SeqBounded, hfinal]
  rcases hlim 1 (by norm_num) with ⟨N, hN⟩
  let s : Finset ℕ := range (N + 1)
  have hs : s.Nonempty := by
    dsimp [s]
    exact ⟨0, by simp⟩
  rcases Finset.exists_max_image s (fun n => |A.map n|) hs with ⟨k, hk, hmax⟩
  let M : ℝ := |A.map k| + |L| + 2
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro n hn
  by_cases hnN : n ≤ N
  · have hmem : n ∈ s := by
      dsimp [s]
      exact Finset.mem_range.mpr (by omega)
    have hle : |A.map n| ≤ |A.map k| := hmax n hmem
    dsimp [M]
    linarith [abs_nonneg L]
  · have hnear := hN n (by omega)
    rw [Nbho_abs] at hnear
    have htri : |A.map n| ≤ |A.map n - L| + |L| := by
      calc
        |A.map n| = |(A.map n - L) + L| := by ring_nf
        _ ≤ |A.map n - L| + |L| := abs_add_le _ _
    dsimp [M]
    linarith [abs_nonneg (A.map k)]

/-- Congruence of RSequence Limit -/
@theorem SeqLimit.Congr
    (h_lim : SeqLimit A L)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimit B L
:= by
  rcases h_lim with ⟨h_final, h_lim⟩
  rcases h_congr with ⟨N, hN⟩
  constructor
  · exact h_B_inf
  · intro ε h_ε
    rcases h_lim ε h_ε with ⟨K, hK⟩
    refine ⟨max N K, ?_⟩
    intro n hn
    rw [← hN n (lt_of_le_of_lt (Nat.le_max_left _ _) hn)]
    exact hK n (lt_of_le_of_lt (Nat.le_max_right _ _) hn)

end


page_end
