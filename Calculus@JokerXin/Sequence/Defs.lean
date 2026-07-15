import «Calculus@JokerXin».Prelude


/-! # Definition of Sequence -/

/-- Real number sequence with domain
    - `a.map`, `a.init` and `a.final` refer to `a`'s total map, initial item's
    index and the final item's index + 1, respectively
    - for infinite sequence `a`, the value of `a.final` is `none` -/
structure Sequence where
  map : ℕ → ℝ
  init : ℕ
  final : WithTop ℕ


/-! # Sequence Operations -/

/-- Free Unary Operation -/
def Sequence_Free₁ (A : Sequence) (op₁ : ℝ → ℝ) : Sequence :=
  ⟨(fun x ↦ op₁ (A.map x)), A.init, A.final⟩

/-- Free Binary Operation -/
def Sequence_Free₂ (A B : Sequence) (op₂ : ℝ → ℝ → ℝ) : Sequence :=
  ⟨(fun x ↦ op₂ (A.map x) (B.map x)), max A.init B.init, min A.final B.final⟩

/-- Division -/
noncomputable def Sequence_Div (A B : Sequence) : Sequence :=
  ⟨(fun x ↦ A.map x / B.map x),
   max A.init B.init,
   min (min A.final B.final) (some (sInf { n : ℕ | B.map n = 0 }))⟩

/-- Scalar Multiplication -/
def Sequence_SMul (k : ℝ) (A : Sequence) : Sequence :=
  ⟨k • A.map, A.init, A.final⟩

/-- Multiplication Scalar Power
    - this may allow `0 ^ 0 = 1` -/
def Sequence_MSPow (A : Sequence) (n : ℕ) : Sequence :=
  ⟨A.map ^ n, A.init, A.final⟩

instance : Add Sequence where  -- Addition
  add := (Sequence_Free₂ · · (· + ·))
instance : Sub Sequence where  -- Subtraction
  sub := (Sequence_Free₂ · · (· - ·))
instance : Mul Sequence where  -- Multiplication
  mul := (Sequence_Free₂ · · (· * ·))
noncomputable instance : Div Sequence where
  div := Sequence_Div
/- # To be Modified ↓ -/
noncomputable instance : HomogeneousPow Sequence where
  pow := (Sequence_Free₂ · · (· ^ ·))
instance : SMul ℝ Sequence where
  smul := Sequence_SMul
instance : Neg Sequence where
  neg := (Sequence_Free₁ · (-·))
instance : NatPow Sequence where
  pow := Sequence_MSPow
/- # To be Modified ↓ -/
noncomputable instance : Inv Sequence where
  inv := (Sequence_Free₁ · (·⁻¹))
