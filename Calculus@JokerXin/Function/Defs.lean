import «Calculus@JokerXin».Prelude


/-! # Definition of Function -/

/-- Real function with domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
structure Function where
  map : ℝ → ℝ
  domain : Set ℝ


/-! # Function Operations -/

/-- Free Unary Operation -/
def Function_Free₁ (F : Function) (op₁ : ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op₁ (F.map x)), F.domain⟩

/-- Free Binary Operation -/
def Function_Free₂ (F G : Function) (op₂ : ℝ → ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op₂ (F.map x) (G.map x)), F.domain ∩ G.domain⟩

/-- Division -/
noncomputable def Function_Div (F G : Function) : Function :=
  ⟨(fun x ↦ F.map x / G.map x), F.domain ∩ G.domain ∩ { x : ℝ | G.map x ≠ 0}⟩

/-- Power -/
noncomputable def Function_Pow (F G : Function) : Function :=
  ⟨(fun x ↦ F.map x / G.map x), F.domain ∩ G.domain ∩ { x : ℝ | F.map x > 0 }⟩

/-- Scalar Multiplication -/
def Function_SMul (k : ℝ) (F : Function) : Function :=
  ⟨k • F.map, F.domain⟩

/-- Multiplicative Scalar Power
    - this may allow `0 ^ 0 = 1` -/
def Function_MSPow (F : Function) (n : ℕ) : Function :=
  ⟨F.map ^ n, F.domain⟩

/-- Composition -/
def Function_Comp (F G : Function) : Function :=
  ⟨F.map ∘ G.map, F.domain ∩ G.domain⟩

instance : Add Function where  -- Addition
  add := (Function_Free₂ · · (· + ·))
instance : Sub Function where  -- Subtraction
  sub := (Function_Free₂ · · (· - ·))
instance : Mul Function where  -- Multiplication
  mul := (Function_Free₂ · · (· * ·))
noncomputable instance : Div Function where
  div := Function_Div
noncomputable instance : HomogeneousPow Function where
  pow := Function_Pow
instance : SMul ℝ Function where
  smul := Function_SMul
instance : Neg Function where  -- Additive Inverse
  neg := (Function_Free₁ · (-·))
instance : NatPow Function where
  pow := Function_MSPow
/- # To be Modified ↓ -/
noncomputable instance : Inv Function where
  inv := (Function_Free₁ · (·⁻¹))

infixr:90 " ⊙ " => (Function_Comp · ·)


/-! # Fundamental Functions -/

/-- Constant Function -/
def Constant (C : ℝ) : Function := ⟨const C, Iii⟩

/-- Identity Function -/
def Identity : Function := ⟨id, Iii⟩

/-- Absolute Value Function -/
def Abs : Function := ⟨abs, Iii⟩

/-- Square Root Function -/
noncomputable def Sqrt : Function := ⟨sqrt, Ici 0⟩

open Classical in
/-- Power Function -/
noncomputable def Power (a : ℝ) : Function :=
  if h : ∃ n : ℤ, a = ↑n then
    if a > 0 then ⟨npow (choose h), Iii⟩
    else ⟨const 1, { x : ℝ | x ≠ 0 }⟩
  else if a > 0 then ⟨pow a, Ici 0⟩
  else ⟨pow a, Ioi 0⟩

/-- Natural Exponential Function -/
noncomputable def Exp : Function := ⟨exp, Iii⟩

/-- Exponential Function
    - **`a > 0` must hold true!**
    - When `a = 1`, it degenerates into a constant function -/
noncomputable def Expow (a : ℝ) : Function := ⟨(a ^ ·), Iii⟩

/-- Natural Logarithm Function -/
noncomputable def Ln : Function := ⟨ln, Ioi 0⟩

/-- Logarithm Function
    - **`a > 0 ∧ a ≠ 1` must hold true!** -/
noncomputable def Log (a : ℝ) : Function := ⟨log a, Ioi 0⟩

/-- Sine Function -/
noncomputable def Sin : Function := ⟨sin, Iii⟩

/-- Cosine Function -/
noncomputable def Cos : Function := ⟨cos, Iii⟩

/-- Tangent Function -/
noncomputable def Tan : Function := ⟨tan, { x : ℝ | cos x ≠ 0 }⟩

/-- Cotangent Function -/
noncomputable def Cot : Function := ⟨cot, { x : ℝ | sin x ≠ 0 }⟩

/-- Secant Function -/
noncomputable def Sec : Function := ⟨sec, { x : ℝ | cos x ≠ 0 }⟩

/-- Cosecant Function -/
noncomputable def Csc : Function := ⟨csc, { x : ℝ | sin x ≠ 0 }⟩

/-- Hyp-Sine Function -/
noncomputable def Sinh : Function := ⟨sinh, Iii⟩

/-- Hyp-Cosine Function -/
noncomputable def Cosh : Function := ⟨cosh, Iii⟩

/-- Hyp-Tangent Function -/
noncomputable def Tanh : Function := ⟨tanh, Iii⟩

/-- Hyp-Cotangent Function -/
noncomputable def Coth : Function := ⟨coth, { x : ℝ | x ≠ 0 }⟩

/-- Hyp-Secant Function -/
noncomputable def Sech : Function := ⟨sech, Iii⟩

/-- Hyp-Cosecant Function -/
noncomputable def Csch : Function := ⟨csch, { x : ℝ | x ≠ 0 }⟩

/-- Arc-Sine Function -/
noncomputable def Arcsin : Function := ⟨arcsin, Icc (-1) 1⟩

/-- Arc-Cosine Function -/
noncomputable def Arccos : Function := ⟨arccos, Icc (-1) 1⟩

/-- Arc-Tangent Function -/
noncomputable def Arctan : Function := ⟨arctan, Iii⟩

/-- Arc-Cotangent Function -/
noncomputable def Arccot : Function := ⟨arccot, Iii⟩

/-- Arc-Secant Function -/
noncomputable def Arcsec : Function := ⟨arcsec, Iic (-1) ∪ Ici 1⟩

/-- Arc-Cosecant Function -/
noncomputable def Arccsc : Function := ⟨arccsc, Iic (-1) ∪ Ici 1⟩
