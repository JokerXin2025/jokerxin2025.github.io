/-
    «Calculus_21».Limit.Expr.GCongr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false


/-! # Monotone abstract transformers -/

open Expr

private instance : BinaryTransformer (fun A B : LimitValue => A + B) where
  monotone_left := by
    intro A A' B hA
    change LimitValue.precision A A' at hA
    change LimitValue.precision (A + B) (A' + B)
    cases A <;> cases A' <;> cases B <;>
      simp_all [LimitValue.precision]
  monotone_right := by
    intro A B B' hB
    change LimitValue.precision B B' at hB
    change LimitValue.precision (A + B) (A + B')
    cases A <;> cases B <;> cases B' <;>
      simp_all [LimitValue.precision]

private instance : UnaryTransformer (fun A : LimitValue => -A) where
  monotone := by
    intro A B h
    change LimitValue.precision A B at h
    change LimitValue.precision (-A) (-B)
    cases A <;> cases B <;> simp_all [LimitValue.precision]

private noncomputable instance limitMulTransformer :
    BinaryTransformer (fun A B : LimitValue => A * B) where
  monotone_left := by
    intro A A' B hA
    apply LimitValue.polyEqual_to_precision
    apply PolyEqual.map (· * B)
    · intro X Y h
      cases h <;> cases B <;> simp only [HMul.hMul, Mul.mul]
      all_goals repeat' split
      all_goals first | apply LimitValue.unknown_always | grind | poly_fallback
    · exact LimitValue.precision_to_polyEqual hA
  monotone_right := by
    intro A B B' hB
    apply LimitValue.polyEqual_to_precision
    apply PolyEqual.map (A * ·)
    · intro X Y h
      cases h <;> cases A <;> simp only [HMul.hMul, Mul.mul]
      all_goals repeat' split
      all_goals first | apply LimitValue.unknown_always | grind | poly_fallback
    · exact LimitValue.precision_to_polyEqual hB

private noncomputable instance limitInvTransformer :
    UnaryTransformer (fun A : LimitValue => A⁻¹) where
  monotone := by
    intro A B h
    change LimitValue.precision A B at h
    change LimitValue.precision A⁻¹ B⁻¹
    cases A <;> cases B <;> simp only [LimitValue.precision, Inv.inv] at *
    all_goals repeat' split <;> simp_all

private noncomputable instance limitPowTransformer :
    BinaryTransformer (fun A B : LimitValue => A ^ B) where
  monotone_left := by
    intro A A' B hA
    apply LimitValue.polyEqual_to_precision
    apply PolyEqual.map (· ^ B)
    · intro X Y h
      cases h <;> cases B <;> simp only [HPow.hPow, Pow.pow]
      all_goals repeat' split
      all_goals apply LimitValue.unknown_always
    · exact LimitValue.precision_to_polyEqual hA
  monotone_right := by
    intro A B B' hB
    apply LimitValue.polyEqual_to_precision
    apply PolyEqual.map (A ^ ·)
    · intro X Y h
      cases h <;> cases A <;> simp only [HPow.hPow, Pow.pow]
      all_goals repeat' split
      all_goals apply LimitValue.unknown_always
    · exact LimitValue.precision_to_polyEqual hB


/-! # Concrete soundness -/

private theorem outcome_add_sound {x y z : LimitValue.Outcome}
    (h : LimitValue.Outcome.Add x y z) :
    LimitValue.precision z.toAbstract (x.toAbstract + y.toAbstract) := by
  cases x <;> cases y <;> cases z <;>
    simp_all [LimitValue.Outcome.Add, LimitValue.Outcome.toAbstract,
      LimitValue.precision]

private theorem outcome_neg_sound {x y : LimitValue.Outcome}
    (h : LimitValue.Outcome.Neg x y) :
    LimitValue.precision y.toAbstract (-x.toAbstract) := by
  cases x <;> cases y <;>
    simp_all [LimitValue.Outcome.Neg, LimitValue.Outcome.toAbstract,
      LimitValue.precision]

private theorem outcome_sub_sound {x y z : LimitValue.Outcome}
    (h : LimitValue.Outcome.Sub x y z) :
    LimitValue.precision z.toAbstract (x.toAbstract - y.toAbstract) := by
  rcases h with ⟨ny, hny, hadd⟩
  exact Precision.le_trans (outcome_add_sound hadd) <|
    Transformer.binary (op := fun A B : LimitValue => A + B)
      (Precision.le_refl _) (outcome_neg_sound hny)

private theorem outcome_mul_sound {x y z : LimitValue.Outcome}
    (h : LimitValue.Outcome.Mul x y z) :
    LimitValue.precision z.toAbstract (x.toAbstract * y.toAbstract) := by
  cases x <;> cases y <;> cases z <;>
    simp_all [LimitValue.Outcome.Mul, LimitValue.Outcome.toAbstract,
      LimitValue.precision]
  all_goals repeat' split <;> simp_all [LimitValue.precision]

private theorem outcome_inv_sound {x y : LimitValue.Outcome}
    (h : LimitValue.Outcome.Inv x y) :
    LimitValue.precision y.toAbstract x.toAbstract⁻¹ := by
  cases x <;> cases y <;>
    simp_all [LimitValue.Outcome.Inv, LimitValue.Outcome.toAbstract,
      LimitValue.precision]
  all_goals repeat' split <;> simp_all [LimitValue.precision]

private theorem outcome_div_sound {x y z : LimitValue.Outcome}
    (h : LimitValue.Outcome.Div x y z) :
    LimitValue.precision z.toAbstract (x.toAbstract / y.toAbstract) := by
  rcases h with ⟨iy, hiy, hmul⟩
  exact Precision.le_trans (outcome_mul_sound hmul) <|
    limitMulTransformer.monotone_right (outcome_inv_sound hiy)

private theorem outcome_pow_sound {x y z : LimitValue.Outcome}
    (h : LimitValue.Outcome.Pow x y z) :
    LimitValue.precision z.toAbstract (x.toAbstract ^ y.toAbstract) := by
  cases x <;> cases y <;> cases z <;>
    simp_all [LimitValue.Outcome.Pow, LimitValue.Outcome.toAbstract,
      LimitValue.precision]
  all_goals repeat' split <;> simp_all [LimitValue.precision]

instance : BinaryTransformer.Sound (fun A B : LimitValue => A + B)
    LimitValue.Outcome.Add where
  sound hx hy hxyz := by
    change _ ∈ LimitValue.gamma _ at hx hy ⊢
    rw [LimitValue.mem_gamma_iff] at hx hy ⊢
    exact Precision.le_trans (outcome_add_sound hxyz) <|
      Transformer.binary (op := fun X Y : LimitValue => X + Y) hx hy

instance : UnaryTransformer.Sound (fun A : LimitValue => -A)
    LimitValue.Outcome.Neg where
  sound hx hxy := by
    change _ ∈ LimitValue.gamma _ at hx ⊢
    rw [LimitValue.mem_gamma_iff] at hx ⊢
    exact Precision.le_trans (outcome_neg_sound hxy) <|
      Transformer.unary (op := fun X : LimitValue => -X) hx

instance : BinaryTransformer.Sound (fun A B : LimitValue => A - B)
    LimitValue.Outcome.Sub where
  sound hx hy hxyz := by
    change _ ∈ LimitValue.gamma _ at hx hy ⊢
    rw [LimitValue.mem_gamma_iff] at hx hy ⊢
    exact Precision.le_trans (outcome_sub_sound hxyz) <|
      Transformer.binary (op := fun X Y : LimitValue => X + Y) hx
        (Transformer.unary (op := fun X : LimitValue => -X) hy)

noncomputable instance : BinaryTransformer.Sound (fun A B : LimitValue => A * B)
    LimitValue.Outcome.Mul where
  sound hx hy hxyz := by
    change _ ∈ LimitValue.gamma _ at hx hy ⊢
    rw [LimitValue.mem_gamma_iff] at hx hy ⊢
    exact Precision.le_trans (outcome_mul_sound hxyz) <|
      Precision.le_trans (limitMulTransformer.monotone_left hx)
        (limitMulTransformer.monotone_right hy)

noncomputable instance : UnaryTransformer.Sound (fun A : LimitValue => A⁻¹)
    LimitValue.Outcome.Inv where
  sound hx hxy := by
    change _ ∈ LimitValue.gamma _ at hx ⊢
    rw [LimitValue.mem_gamma_iff] at hx ⊢
    exact Precision.le_trans (outcome_inv_sound hxy) (limitInvTransformer.monotone hx)

noncomputable instance : BinaryTransformer.Sound (fun A B : LimitValue => A / B)
    LimitValue.Outcome.Div where
  sound hx hy hxyz := by
    change _ ∈ LimitValue.gamma _ at hx hy ⊢
    rw [LimitValue.mem_gamma_iff] at hx hy ⊢
    exact Precision.le_trans (outcome_div_sound hxyz) <|
      Precision.le_trans (limitMulTransformer.monotone_left hx)
        (limitMulTransformer.monotone_right (limitInvTransformer.monotone hy))

noncomputable instance : BinaryTransformer.Sound (fun A B : LimitValue => A ^ B)
    LimitValue.Outcome.Pow where
  sound hx hy hxyz := by
    change _ ∈ LimitValue.gamma _ at hx hy ⊢
    rw [LimitValue.mem_gamma_iff] at hx hy ⊢
    exact Precision.le_trans (outcome_pow_sound hxyz) <|
      Precision.le_trans (limitPowTransformer.monotone_left hx)
        (limitPowTransformer.monotone_right hy)


/-! # Public congruence API -/

@[gcongr]
theorem add_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A + B =. A' + B' :=
  LimitValue.precision_to_polyEqual <|
    Transformer.binary (op := fun X Y : LimitValue => X + Y)
      (LimitValue.polyEqual_to_precision hA)
      (LimitValue.polyEqual_to_precision hB)

@[gcongr]
theorem neg_congr {A B : LimitValue} (h : A =. B) : -A =. -B :=
  LimitValue.precision_to_polyEqual <|
    Transformer.unary (op := fun X : LimitValue => -X)
      (LimitValue.polyEqual_to_precision h)

@[gcongr]
theorem sub_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A - B =. A' - B' :=
  add_congr hA (neg_congr hB)

@[gcongr]
theorem mul_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A * B =. A' * B' :=
  LimitValue.precision_to_polyEqual <|
    Precision.le_trans
      (limitMulTransformer.monotone_left (LimitValue.polyEqual_to_precision hA))
      (limitMulTransformer.monotone_right (LimitValue.polyEqual_to_precision hB))

@[gcongr]
theorem inv_congr {A B : LimitValue} (h : A =. B) : A⁻¹ =. B⁻¹ :=
  LimitValue.precision_to_polyEqual <|
    limitInvTransformer.monotone (LimitValue.polyEqual_to_precision h)

@[gcongr]
theorem div_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A / B =. A' / B' :=
  mul_congr hA (inv_congr hB)

@[gcongr]
theorem pow_congr {A A' B B' : LimitValue}
    (hA : A =. A') (hB : B =. B') : A ^ B =. A' ^ B' :=
  LimitValue.precision_to_polyEqual <|
    Precision.le_trans
      (limitPowTransformer.monotone_left (LimitValue.polyEqual_to_precision hA))
      (limitPowTransformer.monotone_right (LimitValue.polyEqual_to_precision hB))
