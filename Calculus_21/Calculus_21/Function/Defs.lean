/-
    «Calculus_21».Function.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Definition of RFunction -/

/-- Real RFunction with Domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
@[ext]
structure RFunction where
  map : ℝ → ℝ
  domain : Set ℝ


/-! # RFunction Operations -/

/-- RFunction's Addition -/
instance : Add RFunction where
  add F G := ⟨F.map + G.map, F.domain ∩ G.domain⟩

/-- RFunction's Subtraction -/
instance : Sub RFunction where
  sub F G := ⟨F.map - G.map, F.domain ∩ G.domain⟩

/-- RFunction's Multiplication -/
instance : Mul RFunction where
  mul F G := ⟨F.map * G.map, F.domain ∩ G.domain⟩

/-- RFunction's Division -/
noncomputable instance : Div RFunction where
  div F G := ⟨F.map / G.map, F.domain ∩ G.domain ∩ { x : ℝ | G.map x ≠ 0}⟩

/-- RFunction's Power -/
noncomputable instance : HomogeneousPow RFunction where
  pow F G := ⟨(fun x ↦ F.map x ^ G.map x), F.domain ∩ G.domain ∩ { x : ℝ | F.map x > 0 }⟩

/-- RFunction's Scalar Multiplication -/
instance : SMul ℝ RFunction where
  smul k F := ⟨k • F.map, F.domain⟩

/-- RFunction's Additive Inverse -/
instance : Neg RFunction where
  neg F := ⟨- F.map, F.domain⟩

/-- RFunction's Multiplicative Scalar Power
    - this may allow `0 ^ 0 = 1` -/
instance : NatPow RFunction where
  pow F n := ⟨F.map ^ n, F.domain⟩

/-- RFunction's Multiplicative Inverse -/
noncomputable instance : Inv RFunction where
  inv F := ⟨F.map⁻¹, F.domain ∩ { x : ℝ | F.map x ≠ 0}⟩

/-- RFunction's Composition -/
def Function_Comp (F G : RFunction) : RFunction :=
  ⟨F.map ∘ G.map, G.domain ∩ { x : ℝ | G.map x ∈ F.domain }⟩

infixr:90 " ⊙ " => (Function_Comp · ·)


/-! # Fundamental Functions -/

/-- Constant RFunction -/
def Constant (C : ℝ) : RFunction := ⟨const C, Iii⟩

/-- Identity RFunction -/
def Identity : RFunction := ⟨id, Iii⟩

/-- Absolute Value RFunction -/
def Abs : RFunction := ⟨abs, Iii⟩

/-- Square Root RFunction -/
noncomputable def Sqrt : RFunction := ⟨sqrt, Ici 0⟩

/-- Power RFunction -/
noncomputable def Power (a : ℝ) : RFunction :=
  if a > 0 then ⟨pow a, Ici 0⟩
  else ⟨pow a, Ioi 0⟩

/-- Integral Power RFunction -/
noncomputable def NPower (n : ℤ) : RFunction :=
  if n > 0 then ⟨npow n, Iii⟩
  else ⟨npow n, { x : ℝ | x ≠ 0 }⟩

/-- Natural Exponential RFunction -/
noncomputable def Exp : RFunction := ⟨exp, Iii⟩

/-- Exponential RFunction
    - Before using it, please **make sure that `a > 0`**
    - When `a = 1`, it degenerates into a constant function -/
noncomputable def Expow (a : ℝ) : RFunction := ⟨(a ^ ·), Iii⟩

/-- Natural Logarithm RFunction -/
noncomputable def Ln : RFunction := ⟨ln, Ioi 0⟩

/-- Logarithm RFunction
    - Before using it, please **make sure that `a > 0 ∧ a ≠ 1`** -/
noncomputable def Log (a : ℝ) : RFunction := ⟨log a, Ioi 0⟩

/-- Sine RFunction -/
noncomputable def Sin : RFunction := ⟨sin, Iii⟩

/-- Cosine RFunction -/
noncomputable def Cos : RFunction := ⟨cos, Iii⟩

/-- Tangent RFunction -/
noncomputable def Tan : RFunction := ⟨tan, { x : ℝ | cos x ≠ 0 }⟩

/-- Cotangent RFunction -/
noncomputable def Cot : RFunction := ⟨cot, { x : ℝ | sin x ≠ 0 }⟩

/-- Secant RFunction -/
noncomputable def Sec : RFunction := ⟨sec, { x : ℝ | cos x ≠ 0 }⟩

/-- Cosecant RFunction -/
noncomputable def Csc : RFunction := ⟨csc, { x : ℝ | sin x ≠ 0 }⟩

/-- Hyp-Sine RFunction -/
noncomputable def Sinh : RFunction := ⟨sinh, Iii⟩

/-- Hyp-Cosine RFunction -/
noncomputable def Cosh : RFunction := ⟨cosh, Iii⟩

/-- Hyp-Tangent RFunction -/
noncomputable def Tanh : RFunction := ⟨tanh, Iii⟩

/-- Hyp-Cotangent RFunction -/
noncomputable def Coth : RFunction := ⟨coth, { x : ℝ | x ≠ 0 }⟩

/-- Hyp-Secant RFunction -/
noncomputable def Sech : RFunction := ⟨sech, Iii⟩

/-- Hyp-Cosecant RFunction -/
noncomputable def Csch : RFunction := ⟨csch, { x : ℝ | x ≠ 0 }⟩

/-- Arc-Sine RFunction -/
noncomputable def Arcsin : RFunction := ⟨arcsin, Icc (-1) 1⟩

/-- Arc-Cosine RFunction -/
noncomputable def Arccos : RFunction := ⟨arccos, Icc (-1) 1⟩

/-- Arc-Tangent RFunction -/
noncomputable def Arctan : RFunction := ⟨arctan, Iii⟩

/-- Arc-Cotangent RFunction -/
noncomputable def Arccot : RFunction := ⟨arccot, Iii⟩

/-- Arc-Secant RFunction -/
noncomputable def Arcsec : RFunction := ⟨arcsec, Iic (-1) ∪ Ici 1⟩

/-- Arc-Cosecant RFunction -/
noncomputable def Arccsc : RFunction := ⟨arccsc, Iic (-1) ∪ Ici 1⟩


/-! # Identities of Fundamental Functions -/

/-- Exponential function written using the natural exponential function. -/
lemma Expow_eq {a : ℝ} (h_a : 0 < a) :
    Exp ⊙ (Constant (ln a) * Identity) = Expow a := by
  apply RFunction.ext
  · funext x
    simp only [Function_Comp, Exp, Constant, Identity, Function.comp_apply, Expow]
    exact (Real.rpow_def_of_pos h_a x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | True} ↔ x ∈ Iii
    simp

/-- Logarithm written as a quotient of natural logarithms. -/
lemma Log_eq {a : ℝ} (h_a : 0 < a) (h_a_ne_one : a ≠ 1) :
    Ln / Constant (ln a) = Log a := by
  have h_log_ne : ln a ≠ 0 := by
    change Real.log a ≠ 0
    rw [Real.log_ne_zero]
    exact ⟨h_a.ne', h_a_ne_one, by linarith⟩
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Ioi 0 ∩ Iii ∩ {x | ln a ≠ 0} ↔ x ∈ Ioi 0
    simp [h_log_ne]

/-- Tangent written as sine divided by cosine. -/
lemma Tan_eq : Sin / Cos = Tan := by
  apply RFunction.ext
  · funext x
    exact (Real.tan_eq_sin_div_cos x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cos x ≠ 0} ↔ cos x ≠ 0
    simp

/-- Cotangent written as cosine divided by sine. -/
lemma Cot_eq : Cos / Sin = Cot := by
  apply RFunction.ext
  · funext x
    exact (Real.cot_eq_cos_div_sin x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sin x ≠ 0} ↔ sin x ≠ 0
    simp

/-- Secant written as the reciprocal of cosine. -/
lemma Sec_eq : Constant 1 / Cos = Sec := by
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cos x ≠ 0} ↔ cos x ≠ 0
    simp

/-- Cosecant written as the reciprocal of sine. -/
lemma Csc_eq : Constant 1 / Sin = Csc := by
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sin x ≠ 0} ↔ sin x ≠ 0
    simp

/-- Hyperbolic sine written using exponentials. -/
lemma Sinh_eq : (2 : ℝ)⁻¹ • (Exp - Exp ⊙ (-Identity)) = Sinh := by
  apply RFunction.ext
  · funext x
    change (2 : ℝ)⁻¹ * (exp x - exp (-x)) = sinh x
    rw [Real.sinh_eq]
    ring
  · ext x
    change (x ∈ Iii ∧ (x ∈ Iii ∧ True)) ↔ x ∈ Iii
    simp

/-- Hyperbolic cosine written using exponentials. -/
lemma Cosh_eq : (2 : ℝ)⁻¹ • (Exp + Exp ⊙ (-Identity)) = Cosh := by
  apply RFunction.ext
  · funext x
    change (2 : ℝ)⁻¹ * (exp x + exp (-x)) = cosh x
    rw [Real.cosh_eq]
    ring
  · ext x
    change (x ∈ Iii ∧ (x ∈ Iii ∧ True)) ↔ x ∈ Iii
    simp

/-- Hyperbolic tangent written as hyperbolic sine divided by cosine. -/
lemma Tanh_eq : Sinh / Cosh = Tanh := by
  apply RFunction.ext
  · funext x
    exact (Real.tanh_eq_sinh_div_cosh x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cosh x ≠ 0} ↔ x ∈ Iii
    simp [(Real.cosh_pos x).ne']

/-- Hyperbolic sine is nonzero exactly away from the origin. -/
lemma Sinh_ne_zero_iff {x : ℝ} : sinh x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h_sinh h_x
    subst x
    exact h_sinh (by simp [Real.sinh_eq])
  · intro h_x h_sinh
    rw [Real.sinh_eq] at h_sinh
    have h_exp : exp x = exp (-x) := by linarith
    have h_x_neg : x = -x := Real.exp_injective h_exp
    exact h_x (by linarith)

/-- Hyperbolic tangent is nonzero exactly away from the origin. -/
lemma Tanh_ne_zero_iff {x : ℝ} : tanh x ≠ 0 ↔ x ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  simp [(Real.cosh_pos x).ne', Sinh_ne_zero_iff]

/-- Hyperbolic cotangent written as the reciprocal of hyperbolic tangent. -/
lemma Coth_eq : Constant 1 / Tanh = Coth := by
  apply RFunction.ext
  · rfl
  · ext x
    simp only [HDiv.hDiv, Div.div, Constant, Tanh, Coth, Set.mem_inter_iff,
      Set.mem_univ, true_and, Set.mem_setOf_eq]
    exact Tanh_ne_zero_iff

/-- Hyperbolic secant written as the reciprocal of hyperbolic cosine. -/
lemma Sech_eq : Constant 1 / Cosh = Sech := by
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cosh x ≠ 0} ↔ x ∈ Iii
    simp [(Real.cosh_pos x).ne']

/-- Hyperbolic cosecant written as the reciprocal of hyperbolic sine. -/
lemma Csch_eq : Constant 1 / Sinh = Csch := by
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sinh x ≠ 0} ↔ x ≠ 0
    simp [Sinh_ne_zero_iff]

/-- Arccosine written using arcsine. -/
lemma Arccos_eq : Constant (π / 2) - Arcsin = Arccos := by
  apply RFunction.ext
  · funext x
    exact (Real.arccos_eq_pi_div_two_sub_arcsin x).symm
  · ext x
    change x ∈ Iii ∩ Icc (-1) 1 ↔ x ∈ Icc (-1) 1
    simp

/-- Arccotangent written using arctangent. -/
lemma Arccot_eq : Constant (π / 2) - Arctan = Arccot := by
  apply RFunction.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ↔ x ∈ Iii
    simp

private lemma inv_mem_Icc_iff {x : ℝ} :
    x ≠ 0 ∧ x⁻¹ ∈ Icc (-1) 1 ↔ x ∈ Iic (-1) ∪ Ici 1 := by
  constructor
  · rintro ⟨h_x_ne, h_inv⟩
    have h_abs_pos : 0 < |x| := abs_pos.mpr h_x_ne
    have h_abs_inv : |x⁻¹| ≤ 1 := abs_le.mpr h_inv
    rw [abs_inv] at h_abs_inv
    have h_abs : 1 ≤ |x| := (inv_le_one₀ h_abs_pos).mp h_abs_inv
    rw [le_abs] at h_abs
    rcases h_abs with h_abs | h_abs
    · exact Or.inr h_abs
    · exact Or.inl (show x ≤ -1 by linarith)
  · intro h_x
    have h_abs : 1 ≤ |x| := by
      rw [le_abs]
      rcases h_x with h_x | h_x
      · change x ≤ -1 at h_x
        exact Or.inr (by linarith)
      · change 1 ≤ x at h_x
        exact Or.inl h_x
    have h_x_ne : x ≠ 0 := by
      intro h
      subst x
      norm_num at h_abs
    have h_abs_pos : 0 < |x| := abs_pos.mpr h_x_ne
    have h_abs_inv : |x⁻¹| ≤ 1 := by
      rw [abs_inv]
      exact (inv_le_one₀ h_abs_pos).mpr h_abs
    exact ⟨h_x_ne, abs_le.mp h_abs_inv⟩

/-- Arcsecant written as arccosine composed with the reciprocal function. -/
lemma Arcsec_eq : Arccos ⊙ Identity⁻¹ = Arcsec := by
  apply RFunction.ext
  · rfl
  · ext x
    change ((x ∈ Iii ∩ {x | id x ≠ 0}) ∧ (id x)⁻¹ ∈ Icc (-1) 1) ↔
      x ∈ Iic (-1) ∪ Ici 1
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq, id_eq]
    exact inv_mem_Icc_iff

/-- Arccosecant written as arcsine composed with the reciprocal function. -/
lemma Arccsc_eq : Arcsin ⊙ Identity⁻¹ = Arccsc := by
  apply RFunction.ext
  · rfl
  · ext x
    change ((x ∈ Iii ∩ {x | id x ≠ 0}) ∧ (id x)⁻¹ ∈ Icc (-1) 1) ↔
      x ∈ Iic (-1) ∪ Ici 1
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq, id_eq]
    exact inv_mem_Icc_iff

page_end
