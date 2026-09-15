/-
    «Calculus_21».Function.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Definition of Function -/

/-- Real Function with Domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
@[ext]
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

/-- Function's Multiplicative Scalar Power
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

/-- Power Function -/
noncomputable def Power (a : ℝ) : Function :=
  if a > 0 then ⟨pow a, Ici 0⟩
  else ⟨pow a, Ioi 0⟩

/-- Integral Power Function -/
noncomputable def NPower (n : ℤ) : Function :=
  if n > 0 then ⟨npow n, Iii⟩
  else ⟨npow n, { x : ℝ | x ≠ 0 }⟩

/-- Natural Exponential Function -/
noncomputable def Exp : Function := ⟨exp, Iii⟩

/-- Exponential Function
    - Before using it, please **make sure that `a > 0`**
    - When `a = 1`, it degenerates into a constant function -/
noncomputable def Expow (a : ℝ) : Function := ⟨(a ^ ·), Iii⟩

/-- Natural Logarithm Function -/
noncomputable def Ln : Function := ⟨ln, Ioi 0⟩

/-- Logarithm Function
    - Before using it, please **make sure that `a > 0 ∧ a ≠ 1`** -/
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


/-! # Identities of Fundamental Functions -/

/-- Exponential function written using the natural exponential function. -/
lemma Expow_eq {a : ℝ} (h_a : 0 < a) :
    Exp ⊙ (Constant (ln a) * Identity) = Expow a := by
  apply Function.ext
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
  apply Function.ext
  · rfl
  · ext x
    change x ∈ Ioi 0 ∩ Iii ∩ {x | ln a ≠ 0} ↔ x ∈ Ioi 0
    simp [h_log_ne]

/-- Tangent written as sine divided by cosine. -/
lemma Tan_eq : Sin / Cos = Tan := by
  apply Function.ext
  · funext x
    exact (Real.tan_eq_sin_div_cos x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cos x ≠ 0} ↔ cos x ≠ 0
    simp

/-- Cotangent written as cosine divided by sine. -/
lemma Cot_eq : Cos / Sin = Cot := by
  apply Function.ext
  · funext x
    exact (Real.cot_eq_cos_div_sin x).symm
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sin x ≠ 0} ↔ sin x ≠ 0
    simp

/-- Secant written as the reciprocal of cosine. -/
lemma Sec_eq : Constant 1 / Cos = Sec := by
  apply Function.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cos x ≠ 0} ↔ cos x ≠ 0
    simp

/-- Cosecant written as the reciprocal of sine. -/
lemma Csc_eq : Constant 1 / Sin = Csc := by
  apply Function.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sin x ≠ 0} ↔ sin x ≠ 0
    simp

/-- Hyperbolic sine written using exponentials. -/
lemma Sinh_eq : (2 : ℝ)⁻¹ • (Exp - Exp ⊙ (-Identity)) = Sinh := by
  apply Function.ext
  · funext x
    change (2 : ℝ)⁻¹ * (exp x - exp (-x)) = sinh x
    rw [Real.sinh_eq]
    ring
  · ext x
    change (x ∈ Iii ∧ (x ∈ Iii ∧ True)) ↔ x ∈ Iii
    simp

/-- Hyperbolic cosine written using exponentials. -/
lemma Cosh_eq : (2 : ℝ)⁻¹ • (Exp + Exp ⊙ (-Identity)) = Cosh := by
  apply Function.ext
  · funext x
    change (2 : ℝ)⁻¹ * (exp x + exp (-x)) = cosh x
    rw [Real.cosh_eq]
    ring
  · ext x
    change (x ∈ Iii ∧ (x ∈ Iii ∧ True)) ↔ x ∈ Iii
    simp

/-- Hyperbolic tangent written as hyperbolic sine divided by cosine. -/
lemma Tanh_eq : Sinh / Cosh = Tanh := by
  apply Function.ext
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
  apply Function.ext
  · rfl
  · ext x
    simp only [HDiv.hDiv, Div.div, Constant, Tanh, Coth, Set.mem_inter_iff,
      Set.mem_univ, true_and, Set.mem_setOf_eq]
    exact Tanh_ne_zero_iff

/-- Hyperbolic secant written as the reciprocal of hyperbolic cosine. -/
lemma Sech_eq : Constant 1 / Cosh = Sech := by
  apply Function.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | cosh x ≠ 0} ↔ x ∈ Iii
    simp [(Real.cosh_pos x).ne']

/-- Hyperbolic cosecant written as the reciprocal of hyperbolic sine. -/
lemma Csch_eq : Constant 1 / Sinh = Csch := by
  apply Function.ext
  · rfl
  · ext x
    change x ∈ Iii ∩ Iii ∩ {x | sinh x ≠ 0} ↔ x ≠ 0
    simp [Sinh_ne_zero_iff]

/-- Arccosine written using arcsine. -/
lemma Arccos_eq : Constant (π / 2) - Arcsin = Arccos := by
  apply Function.ext
  · funext x
    exact (Real.arccos_eq_pi_div_two_sub_arcsin x).symm
  · ext x
    change x ∈ Iii ∩ Icc (-1) 1 ↔ x ∈ Icc (-1) 1
    simp

/-- Arccotangent written using arctangent. -/
lemma Arccot_eq : Constant (π / 2) - Arctan = Arccot := by
  apply Function.ext
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
  apply Function.ext
  · rfl
  · ext x
    change ((x ∈ Iii ∩ {x | id x ≠ 0}) ∧ (id x)⁻¹ ∈ Icc (-1) 1) ↔
      x ∈ Iic (-1) ∪ Ici 1
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq, id_eq]
    exact inv_mem_Icc_iff

/-- Arccosecant written as arcsine composed with the reciprocal function. -/
lemma Arccsc_eq : Arcsin ⊙ Identity⁻¹ = Arccsc := by
  apply Function.ext
  · rfl
  · ext x
    change ((x ∈ Iii ∩ {x | id x ≠ 0}) ∧ (id x)⁻¹ ∈ Icc (-1) 1) ↔
      x ∈ Iic (-1) ∪ Ici 1
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq, id_eq]
    exact inv_mem_Icc_iff

page_end
