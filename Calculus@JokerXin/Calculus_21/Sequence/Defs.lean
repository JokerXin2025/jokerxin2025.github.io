/-
    Calculus_21.Sequence.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Definition of Sequence -/

/-- Real Number Sequence with Domain
    - `a.map`, `a.init` and `a.final` refer to `a`'s total map, initial item's
    index and the final item's index + 1, respectively
    - for infinite sequence `a`, the value of `a.final` is `none` -/
structure Sequence where
  map : ℕ → ℝ
  init : ℕ
  final : WithTop ℕ


/-! # Sequence Operations -/

/-- Sequence's Addition -/
instance : Add Sequence where
  add A B := ⟨A.map + B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Subtraction -/
instance : Sub Sequence where
  sub A B := ⟨A.map - B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Multiplication -/
instance : Mul Sequence where
  mul A B := ⟨A.map * B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Division -/
noncomputable instance : Div Sequence where
  div A B := ⟨A.map / B.map, max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | B.map n = 0 }))⟩

/-- Sequence's Power -/
noncomputable instance : HomogeneousPow Sequence where
  pow A B := ⟨(fun x ↦ A.map x ^ B.map x), max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | A.map n ≤ 0 }))⟩

/-- Sequence's Scalar Multiplication -/
instance : SMul ℝ Sequence where
  smul k A := ⟨k • A.map, A.init, A.final⟩

/-- Sequence's Additive Inverse -/
instance : Neg Sequence where
  neg A := ⟨- A.map, A.init, A.final⟩

/-- Sequence's Multiplication Scalar Power
    - this may allow `0 ^ 0 = 1` -/
instance : NatPow Sequence where
  pow A n := ⟨A.map ^ n, A.init, A.final⟩

/-- Sequence's Multiplicative Inverse -/
noncomputable instance : Inv Sequence where
  inv A := ⟨A.map⁻¹, A.init, min A.final (some (sInf { n : ℕ | A.map n = 0 }))⟩
