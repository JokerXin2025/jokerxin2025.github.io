/-
    Calculus_21.Function.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Definition of Function -/

/-- Real Function with Domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
structure Function where
  map : ℝ → ℝ
  domain : Set ℝ


/-! # Function Operations -/

/-- Function's Addition -/
instance : Add Function where
  add F G := ⟨F.map + G.map, F.domain ∩ G.domain⟩

/-- Function's Subtraction -/
instance : Sub Function where
  sub F G := ⟨F.map - G.map, F.domain ∩ G.domain⟩

/-- Function's Multiplication -/
instance : Mul Function where
  mul F G := ⟨F.map * G.map, F.domain ∩ G.domain⟩

/-- Function's Division -/
noncomputable instance : Div Function where
  div F G := ⟨F.map / G.map, F.domain ∩ G.domain ∩ { x : ℝ | G.map x ≠ 0}⟩

/-- Function's Power -/
noncomputable instance : HomogeneousPow Function where
  pow F G := ⟨(fun x ↦ F.map x ^ G.map x), F.domain ∩ G.domain ∩ { x : ℝ | F.map x > 0 }⟩

/-- Function's Scalar Multiplication -/
instance : SMul ℝ Function where
  smul k F := ⟨k • F.map, F.domain⟩

/-- Function's Additive Inverse -/
instance : Neg Function where
  neg F := ⟨- F.map, F.domain⟩

/-- Function's Multiplication Scalar Power
    - this may allow `0 ^ 0 = 1` -/
instance : NatPow Function where
  pow F n := ⟨F.map ^ n, F.domain⟩

/-- Function's Multiplicative Inverse -/
noncomputable instance : Inv Function where
  inv F := ⟨F.map⁻¹, F.domain ∩ { x : ℝ | F.map x ≠ 0}⟩

/-- Function's Composition -/
def Function_Comp (F G : Function) : Function :=
  ⟨F.map ∘ G.map, G.domain ∩ { x : ℝ | G.map x ∈ F.domain }⟩

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
