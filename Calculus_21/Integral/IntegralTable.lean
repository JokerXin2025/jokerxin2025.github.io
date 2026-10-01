import «Calculus_21».Integral.Tactics.Table


namespace IntegralTable
variable {a C : ℝ}

theorem Constant
  : ∫ (const C) =. prim fun x ↦ C * x
:= by int_table

theorem Identity
  : ∫ id =. prim fun x ↦ x ^ 2 / 2
:= by int_table

theorem Power_ℕ {n : ℕ}
  : ∫ x ^ n d x =. prim fun x ↦ x ^ (n + 1) / (n + 1)
:= by int_table

theorem Exp
  : ∫ exp =. prim exp
:= by int_table

theorem Ln
  : ∫ ln x d x =. prim fun x ↦ x * ln x - x
:= by int_table except {0}

theorem Log (ha : a > 0) (ha₁ : a ≠ 1)
  : ∫ (log a) =. prim fun x ↦ (x * ln |x| - x) / ln a
:= by
  int_table except {0}
  rw [Real.log_abs]
  have hn : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha ha₁
  field_simp
  ring

theorem Sin
  : ∫ sin =. prim (-cos)
:= by int_table

theorem Cos
  : ∫ cos =. prim sin
:= by int_table

theorem Sinh
  : ∫ sinh =. prim cosh
:= by int_table

theorem Cosh
  : ∫ cosh =. prim sinh
:= by int_table

theorem toConstant
  : ∫ 0 d _x =. prim (const C)
:= by int_table

theorem toIdentity
  : ∫ 1 d _x =. prim id
:= by int_table

theorem toExp
  : ∫ exp x d x =. prim exp
:= by int_table

theorem toSin
  : ∫ cos x d x =. prim sin
:= by int_table

theorem toCos
  : ∫ - sin x d x =. prim cos
:= by int_table

theorem toArctan
  : ∫ (1 + x ^ 2)⁻¹ d x =. prim arctan
:= by int_table

theorem Reciprocal
  : ∫ x⁻¹ d x =. prim (ln |·|)
:= by int_table

theorem ReciprocalLogSquare
  : ∫ x⁻¹ d x =. prim fun x ↦ ln (x ^ 2) / 2
:= by int_table

theorem IntPow (m : ℤ) (hm : m ≠ -1)
  : ∫ x ^ m d x =. prim fun x ↦ x ^ (m + 1) / (m + 1)
:= by int_table

theorem InverseSquare
  : ∫ 1 / x ^ 2 d x =. prim (-·⁻¹)
:= by int_table

theorem toTanh
  : ∫ sech x ^ 2 d x =. prim tanh
:= by int_table

theorem toCoth
  : ∫ - csch x ^ 2 d x =. prim coth
:= by int_table

theorem toSech
  : ∫ - tanh x * sech x d x =. prim sech
:= by int_table

theorem toCsch
  : ∫ - coth x * csch x d x =. prim csch
:= by int_table

theorem Arctan
  : ∫ arctan x d x =. prim fun x ↦ x * arctan x - ln (1 + x ^ 2) / 2
:= by int_table

theorem Arccot
  : ∫ arccot x d x =. prim fun x ↦ x * arccot x + ln (1 + x ^ 2) / 2
:= by int_table

theorem toArccot
  : ∫ -1 / (1 + x ^ 2) d x =. prim arccot
:= by int_table

theorem Abs
  : ∫ |x| d x =. prim fun x ↦ x * |x| / 2
:= by
  int_table except {0}
  rw [sq_abs]
  rename_i x hx
  have hx' : x ≠ 0 := by simpa using hx
  field_simp
  nlinarith [sq_abs x]

theorem toAbs
  : ∫ x / |x| d x =. prim abs
:= by int_table

theorem ReciprocalQuadratic {a : ℝ} (ha : a > 0)
  : ∫ 1 / (a ^ 2 + x ^ 2) d x =. prim fun x ↦ arctan (x / a) / a
:= by int_table

theorem SinSquare
  : ∫ sin x ^ 2 d x =. prim fun x ↦ (x - sin x * cos x) / 2
:= by
  int_table
  rename_i x hx
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem CosSquare
  : ∫ cos x ^ 2 d x =. prim fun x ↦ (x + sin x * cos x) / 2
:= by
  int_table
  rename_i x hx
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem Tanh
  : ∫ tanh x d x =. prim fun x ↦ ln (cosh x)
:= by
  int_table
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem Coth
  : ∫ coth x d x =. prim fun x ↦ ln |sinh x|
:= by
  int_table
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [one_div, inv_div]

theorem SechSquare
  : ∫ sech x ^ 2 d x =. prim tanh
:= by int_table

theorem CschSquare
  : ∫ csch x ^ 2 d x =. prim (-coth)
:= by int_table

theorem Sech
  : ∫ sech x d x =. prim fun x ↦ arctan (sinh x)
:= by int_table; exact Real.cosh_sq' _

theorem Csch
  : ∫ csch x d x =. prim fun x ↦ ln |tanh (x / 2)|
:= by
  int_table
  rw [Real.tanh_eq_sinh_div_cosh]
  rename_i x hx
  have heq : sinh x = 2 * sinh (x / 2) * cosh (x / 2) := by
    convert Real.sinh_two_mul (x / 2) using 1
    congr 1
    ring
  rw [heq]
  field_simp
  ring

end IntegralTable
