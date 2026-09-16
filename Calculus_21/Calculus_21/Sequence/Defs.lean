/-
    «Calculus_21».Sequence.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Definition of RSequence -/

/-- Real Number RSequence with Domain
    - `A.map`, `A.init` and `A.final` refer to `A`'s total map, initial item's
    index and final item's index (but incremented by 1), respectively
    - for infinite sequence `A`, the value of `A.final` is `none` -/
@[ext]
structure RSequence where
  map : ℕ → ℝ
  init : ℕ
  final : WithTop ℕ


/-! # RSequence Operations -/

/-- RSequence's Addition -/
instance : Add RSequence where
  add A B := ⟨A.map + B.map, max A.init B.init, min A.final B.final⟩

/-- RSequence's Subtraction -/
instance : Sub RSequence where
  sub A B := ⟨A.map - B.map, max A.init B.init, min A.final B.final⟩

/-- RSequence's Multiplication -/
instance : Mul RSequence where
  mul A B := ⟨A.map * B.map, max A.init B.init, min A.final B.final⟩

/-- RSequence's Division -/
noncomputable instance : Div RSequence where
  div A B := ⟨A.map / B.map, max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | B.map n = 0 }))⟩

/-- RSequence's Power -/
noncomputable instance : HomogeneousPow RSequence where
  pow A B := ⟨(fun x ↦ A.map x ^ B.map x), max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | A.map n ≤ 0 }))⟩

/-- RSequence's Scalar Multiplication -/
instance : SMul ℝ RSequence where
  smul k A := ⟨k • A.map, A.init, A.final⟩

/-- RSequence's Additive Inverse -/
instance : Neg RSequence where
  neg A := ⟨- A.map, A.init, A.final⟩

/-- RSequence's Multiplicative Scalar Power
    - This may allow `0 ^ 0 = 1` -/
instance : NatPow RSequence where
  pow A n := ⟨A.map ^ n, A.init, A.final⟩

/-- RSequence's Multiplicative Inverse -/
noncomputable instance : Inv RSequence where
  inv A := ⟨A.map⁻¹, A.init, min A.final (some (sInf { n : ℕ | A.map n = 0 }))⟩

page_end
