import «Calculus_21».Limit.Tactics
import «Calculus_21».Differential.Tactics


/-! # Tests for `lim_cont` -/

section
variable {x a b C : ℝ} {n : ℤ}

example
  : lim x (const C) = the C
:= by lim_cont

example
  : (lim x fun _ ↦ 5) = the 5
:= by lim_cont

example
  : lim x id = the x
:= by lim_cont

example
  : lim x (·) = the x
:= by lim_cont

example
  : lim x (-·) = the (-x)
:= by lim_cont

example (_ : x ≠ 0)
  : lim x (·⁻¹) = the (x⁻¹)
:= by lim_cont

example
  : lim x abs = the |x|
:= by lim_cont

example (_ : x > 0)
  : lim x sqrt = the √x
:= by lim_cont

example (_ : n > 0)
  : lim x (· ^ n) = the (x ^ n)
:= by lim_cont

example (_ : x > 0)
  : lim x (· ^ a) = the (x ^ a)
:= by lim_cont

example
  : lim x exp = the (exp x)
:= by lim_cont

example (_ : a > 0)
  : lim x (a ^ ·) = the (a ^ x)
:= by lim_cont

example (_ : x > 0)
  : lim x ln = the (ln x)
:= by lim_cont

example (_ : a > 0 ∧ a ≠ 1) (_ : x > 0)
  : lim x (log a) = the (log a x)
:= by lim_cont

example
  : lim x sin = the (sin x)
:= by lim_cont

example
  : lim x cos = the (cos x)
:= by lim_cont

example (_ : cos x ≠ 0)
  : lim x tan = the (tan x)
:= by lim_cont

example (_ : sin x ≠ 0)
  : lim x cot = the (cot x)
:= by lim_cont

example (_ : cos x ≠ 0)
  : lim x sec = the (sec x)
:= by lim_cont

example (_ : sin x ≠ 0)
  : lim x csc = the (csc x)
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : lim x arcsin = the (arcsin x)
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : lim x arccos = the (arccos x)
:= by lim_cont

example
  : lim x arctan = the (arctan x)
:= by lim_cont

example
  : lim x arccot = the (arccot x)
:= by lim_cont

example (_ : x < -1 ∨ x > 1)
  : lim x arcsec = the (arcsec x)
:= by lim_cont

example (_ : x < -1 ∨ x > 1)
  : lim x arccsc = the (arccsc x)
:= by lim_cont

example
  : lim x sinh = the (sinh x)
:= by lim_cont

example
  : lim x cosh = the (cosh x)
:= by lim_cont

example
  : lim x tanh = the (tanh x)
:= by lim_cont

example (_ : x ≠ 0)
  : lim x coth = the (coth x)
:= by lim_cont

example
  : lim x sech = the (sech x)
:= by lim_cont

example (_ : x ≠ 0)
  : lim x csch = the (csch x)
:= by lim_cont

example
  : (lim x fun t ↦ sinh t) = the (sinh x)
:= by lim_cont

example
  : (lim x fun t ↦ cosh t) = the (cosh x)
:= by lim_cont

example
  : (lim x fun t ↦ tanh t) = the (tanh x)
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : (lim x fun t ↦ arcsin t) = the (arcsin x)
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : (lim x fun t ↦ arccos t) = the (arccos x)
:= by lim_cont

example
  : (lim x fun t ↦ arctan t) = the (arctan x)
:= by lim_cont

example
  : (lim x fun t ↦ |t|) = the |x|
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ √t) = the √x
:= by lim_cont

example (_ : x ≠ 0)
  : (lim x fun t ↦ t⁻¹) = the (x⁻¹)
:= by lim_cont

example
  : (lim x fun t ↦ exp t) = the (exp x)
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ ln t) = the (ln x)
:= by lim_cont

example (_ : a > 0)
  : (lim x fun t ↦ a ^ t) = the (a ^ x)
:= by lim_cont

example
  : lim x (sin + cos) = the (sin x + cos x)
:= by lim_cont

example
  : lim x (exp - id) = the (exp x - x)
:= by lim_cont

example (_ : x > 0)
  : lim x (id * ln) = the (x * ln x)
:= by lim_cont

example (_ : x ≠ 0 ∧ cos x ≠ 0)
  : lim x (tan / id) = the (tan x / x)
:= by lim_cont

example
  : (lim x fun t ↦ t + 3) = the (x + 3)
:= by lim_cont

example
  : (lim x fun t ↦ 2 * t) = the (2 * x)
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ t - √t) = the (x - √x)
:= by lim_cont

example
  : (lim x fun t ↦ exp t * sin t) = the (exp x * sin x)
:= by lim_cont

example
  : (lim 1 fun t ↦ ln t / t) = the 0
:= by lim_cont

example
  : (lim x fun t ↦ t^2 + 5*t + 6) = the (x ^ 2 + 5*x + 6)
:= by lim_cont

example (_ : x - 1 ≠ 0)
  : (lim x fun t ↦ (t + 1) / (t - 1)) = the ((x + 1) / (x - 1))
:= by lim_cont

example
  : (lim x fun t ↦ a * sin t + C * cos t) = the (a * sin x + C * cos x)
:= by lim_cont

example
  : (lim x fun t ↦ |t| + t) = the (|x| + x)
:= by lim_cont

example
  : (lim x fun t ↦ t^3 - 2*t^2 + t) = the (x ^ 3 - 2*x ^ 2 + x)
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : (lim x fun t ↦ arcsin t + arccos t) = the (arcsin x + arccos x)
:= by lim_cont

example
  : (lim x fun t ↦ sinh t + cosh t) = the (exp x)
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ exp t + 2 ^ t) = the (exp x + 2 ^ x)
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ log 10 t * ln t) = the (log 10 x * ln x)
:= by lim_cont

example (_ : x ≠ 0)
  : (lim x fun t ↦ t⁻¹ + t) = the ((x ^ 2 + 1) / x)
:= by lim_cont

example (_ : cos x ≠ 0) (_ : sin x ≠ 0)
  : (lim x fun t ↦ sec t * csc t) = the (sec x * csc x)
:= by lim_cont

example
  : lim x (exp ∘ sin) = the (exp (sin x))
:= by lim_cont

example (_ : cos x > 0)
  : lim x (ln ∘ cos) = the (ln (cos x))
:= by lim_cont

example
  : lim x (sqrt ∘ exp) = the (√(exp x))
:= by lim_cont

example (_ : x > 0)
  : lim x (abs ∘ ln) = the (|ln x|)
:= by lim_cont

example
  : lim x (sin ∘ id) = the (sin x)
:= by lim_cont

example
  : lim x (cos ∘ (· ^ 2)) = the (cos (x ^ 2))
:= by lim_cont

example (_ : x > 0 ∧ cos √x ≠ 0)
  : lim x (tan ∘ sqrt) = the (tan √x)
:= by lim_cont

example (_ : exp x > -1 ∧ exp x < 1)
  : lim x (arcsin ∘ exp) = the (arcsin (exp x))
:= by lim_cont

example (_ : x > 0 ∧ ln x > -1 ∧ ln x < 1)
  : lim x (arccos ∘ ln) = the (arccos (ln x))
:= by lim_cont

example
  : lim x (arctan ∘ id) = the (arctan x)
:= by lim_cont

example
  : lim x (sinh ∘ cosh) = the (sinh (cosh x))
:= by lim_cont

example (_ : x ≠ 0)
  : lim x (log 2 ∘ abs) = the (log 2 |x|)
:= by lim_cont

example
  : lim x ((3 ^ ·) ∘ sin) = the (3 ^ sin x)
:= by lim_cont

example (_ : cos x ≠ 0)
  : lim x ((· ^ 3) ∘ tan) = the (tan x ^ 3)
:= by lim_cont

example
  : lim x ((C + ·) ∘ cos) = the (C + cos x)
:= by lim_cont

example
  : lim x ((-·) ∘ cos) = the (-cos x)
:= by lim_cont

example
  : lim x ((·⁻¹) ∘ sin) = the ((sin x)⁻¹)
:= by lim_cont

example (_ : cos x ≠ 0 ∧ cos (tan x) ≠ 0)
  : lim x (sec ∘ tan) = the (sec (tan x))
:= by lim_cont

example (_ : sin x ≠ 0 ∧ sin (cot x) ≠ 0)
  : lim x (csc ∘ cot) = the (csc (cot x))
:= by lim_cont

example (_ : x > 0)
  : lim x (sqrt ∘ sqrt) = the (√(√x))
:= by lim_cont

example
  : lim x (exp ∘ exp) = the (exp (exp x))
:= by lim_cont

example
  : (lim x fun t ↦ exp (sin t + cos t)) = the (exp (sin x + cos x))
:= by lim_cont

example
  : (lim x fun t ↦ ln (t^2 + 1)) = the (ln (x ^ 2 + 1))
:= by lim_cont

example (_ : x > -1 ∧ x < 1)
  : (lim x fun t ↦ √(1 - t^2)) = the (√(1 - x ^ 2))
:= by lim_cont

example (_ : n > 0)
  : (lim x fun t ↦ (sin t)^n * (cos t)^n) = the ((sin x)^n * (cos x)^n)
:= by lim_cont

example
  : (lim x fun t ↦ t * exp (-t)) = the (x * exp (-x))
:= by lim_cont

example (_ : sin x ≠ 0)
  : (lim x fun t ↦ log 2 (abs (sin t))) = the (log 2 (|sin x|))
:= by lim_cont

example
  : (lim x fun t ↦ (t + a) ^ 5) = the ((x + a) ^ 5)
:= by lim_cont

example (_ : a ≠ 0) (_ : x / a > -1 ∧ x / a < 1)
  : (lim x fun t ↦ arcsin (t / a)) = the (arcsin (x / a))
:= by lim_cont

example
  : (lim x fun t ↦ arctan (exp t)) = the (arctan (exp x))
:= by lim_cont

example (_ : x > 0)
  : (lim x fun t ↦ cosh (ln t)) = the (cosh (ln x))
:= by lim_cont

example (_ : a > 0)
  : (lim x fun t ↦ a ^ (b * t)) = the (a ^ (b * x))
:= by lim_cont

example (_ : π > 0)
  : (lim x fun t ↦ 1 / √(2 * π) * exp (-t^2 / 2)) = the (1 / √(2 * π) * exp (-x ^ 2 / 2))
:= by lim_cont
example (_ : x > 0)
  : (lim x fun t ↦ (ln t) / (t ^ a)) = the ((ln x) / (x ^ a))
:= by lim_cont

example (_ : cos x ≠ 0)
  : (lim x fun t ↦ sin (cos (tan t))) = the (sin (cos (tan x)))
:= by lim_cont

example
  : (lim x fun t ↦ |t ^ 3 - t| / (t ^ 2 + 1)) = the (|x ^ 3 - x| / (x ^ 2 + 1))
:= by lim_cont

end


/-! # Tests for `deriv_calc` -/

section
variable {x a b C : ℝ} {n : ℤ}

example
  : D (const C) x = the 0
:= by deriv_calc

example
  : D (fun _ ↦ 5) x = the 0
:= by deriv_calc

example
  : D id x = the 1
:= by deriv_calc

example
  : D (·) x = the 1
:= by deriv_calc

example
  : D (-·) x = the (-1)
:= by deriv_calc

example
  : D (fun t ↦ -t) x = the (-1)
:= by deriv_calc

example (_ : x ≠ 0)
  : D (·⁻¹) x = the (-1 / x ^ 2)
:= by deriv_calc

example (_ : x ≠ 0)
  : D abs x = the (x / |x|)
:= by deriv_calc

example (_ : x > 0)
  : D sqrt x = the (1 / (2 * √x))
:= by deriv_calc

example (_ : n > 0)
  : D (· ^ n) x = the (n * x ^ (n - 1))
:= by deriv_calc

example (_ : x > 0)
  : D (· ^ a) x = the (a * x ^ (a - 1))
:= by deriv_calc

example
  : D exp x = the (exp x)
:= by deriv_calc

example (_ : a > 0)
  : D (a ^ ·) x = the (a ^ x * ln a)
:= by deriv_calc

example (_ : x > 0)
  : D ln x = the (1 / x)
:= by deriv_calc

example (_ : a > 0 ∧ a ≠ 1) (_ : x > 0)
  : D (log a) x = the (1 / (x * ln a))
:= by deriv_calc

example
  : D sin x = the (cos x)
:= by deriv_calc

example
  : D cos x = the (-sin x)
:= by deriv_calc

example (_ : cos x ≠ 0)
  : D tan x = the (sec x ^2)
:= by deriv_calc

example (_ : sin x ≠ 0)
  : D cot x = the (- csc x ^2)
:= by deriv_calc

example (_ : cos x ≠ 0)
  : D sec x = the (sec x * tan x)
:= by deriv_calc

example (_ : sin x ≠ 0)
  : D csc x = the (-csc x * cot x)
:= by deriv_calc

example
  : D sinh x = the (cosh x)
:= by deriv_calc

example
  : D cosh x = the (sinh x)
:= by deriv_calc

example
  : D tanh x = the (sech x ^2)
:= by deriv_calc

example (_ : x ≠ 0)
  : D coth x = the (- csch x ^2)
:= by deriv_calc

example
  : D sech x = the (-sech x * tanh x)
:= by deriv_calc

example (_ : x ≠ 0)
  : D csch x = the (-csch x * coth x)
:= by deriv_calc

example
  : D (fun t ↦ sinh t) x = the (cosh x)
:= by deriv_calc

example
  : D (fun t ↦ cosh t) x = the (sinh x)
:= by deriv_calc

example
  : D (fun t ↦ tanh t) x = the (sech x ^2)
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D arcsin x = the (1 / √(1 - x ^ 2))
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D arccos x = the (-1 / √(1 - x ^ 2))
:= by deriv_calc

example
  : D arctan x = the (1 / (1 + x ^ 2))
:= by deriv_calc

example
  : D arccot x = the (-1 / (1 + x ^ 2))
:= by deriv_calc

example (_ : x < -1 ∨ x > 1)
  : D arcsec x = the (1 / (|x| * √(x ^ 2 - 1)))
:= by deriv_calc

example (_ : x < -1 ∨ x > 1)
  : D arccsc x = the (-1 / (|x| * √(x ^ 2 - 1)))
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t) x = the (1 / √(1 - x ^ 2))
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arccos t) x = the (-1 / √(1 - x ^ 2))
:= by deriv_calc

example (_ : x > -1) : D (fun x ↦ ln (x + 1)) x = the (1 / (x + 1)) := by deriv_calc

example (_ : x > -1) : x + 1 > 0 := by linarith

example
  : D (fun t ↦ arctan t) x = the (1 / (1 + x ^ 2))
:= by deriv_calc

example (_ : x ≠ 0)
  : D (fun t ↦ |t|) x = the (x / |x|)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ √t) x = the (1 / (2 * √x))
:= by deriv_calc

example (_ : x ≠ 0)
  : D (fun t ↦ t⁻¹) x = the (-1 / x ^ 2)
:= by deriv_calc

example
  : D (fun t ↦ exp t) x = the (exp x)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ ln t) x = the (1 / x)
:= by deriv_calc

example (_ : a > 0)
  : D (fun t ↦ a ^ t) x = the (a ^ x * ln a)
:= by deriv_calc

example
  : D (sin + cos) x = the (cos x - sin x)
:= by deriv_calc

example
  : D (exp - id) x = the (exp x - 1)
:= by deriv_calc

example
  : D (fun t ↦ 3 * t) x = the 3
:= by deriv_calc

example
  : D (fun t ↦ t + 5) x = the 1
:= by deriv_calc

example
  : D (fun t ↦ 4 * t^3) x = the (12 * x ^ 2)
:= by deriv_calc

example
  : D (fun t ↦ t^2 + 2 * t + 1) x = the (2 * x + 2)
:= by deriv_calc

example
  : D (fun t ↦ a * sin t + C * cos t) x = the (a * cos x - C * sin x)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ 5 * exp t - 2 * ln t) x = the (5 * exp x - 2 / x)
:= by deriv_calc

example
  : D (fun t ↦ t^4 - t^3 + t^2 - t) x = the (4*x ^ 3 - 3*x ^ 2 + 2*x - 1)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ 2 * √t + 3 * t⁻¹) x = the (1 / √x - 3 / x ^ 2)
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t + arccos t) x = the 0
:= by deriv_calc

example
  : D (fun t ↦ arctan t + arccot t) x = the 0
:= by deriv_calc

example
  : D (fun t ↦ sinh t + cosh t) x = the (cosh x + sinh x)
:= by deriv_calc

example (_ : a > 0) (_ : x > 0)
  : D (fun t ↦ 7 * a^t + 8 * log 10 t) x = the (7 * a^x * ln a + 8 / (x * ln 10))
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ |t| + t) x = the (x / |x| + 1)
:= by deriv_calc

example (_ : cos x ≠ 0 ∧ sin x ≠ 0)
  : D (fun t ↦ sec t - csc t) x = the (sec x * tan x + csc x * cot x)
:= by deriv_calc

example (_ : n > 0) (_ : x > 0)
  : D (fun t ↦ t^n + t^a) x = the (n * x^(n-1) + a * x^(a-1))
:= by deriv_calc

example
  : D (fun t ↦ t - 2 * arctan t) x = the (1 - 2 / (1 + x ^ 2))
:= by deriv_calc

example
  : D (fun t ↦ 4 * tanh t) x = the (4 * sech x ^ 2)
:= by deriv_calc

example
  : D (fun t ↦ exp t + t) x = the (exp x + 1)
:= by deriv_calc

example (_ : x > 0)
  : D (id * ln) x = the (ln x + 1)
:= by deriv_calc

example (_ : x ≠ 0) (_ : cos x ≠ 0)
  : D (tan / id) x = the ((x * sec x ^2 - tan x) / x ^ 2)
:= by deriv_calc

example
  : D (fun t ↦ t * exp t) x = the (exp x + x * exp x)
:= by deriv_calc

example
  : D (fun t ↦ sin t * cos t) x = the (cos x * cos x - sin x * sin x)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ t^2 * ln t) x = the (2 * x * ln x + x)
:= by deriv_calc

example
  : D (fun t ↦ exp t * sin t) x = the (exp x * sin x + exp x * cos x)
:= by deriv_calc

example (_ : x ≠ 1)
  : D (fun t ↦ (t + 1) / (t - 1)) x = the (-2 / (x - 1)^2)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ ln t / t) x = the ((1 - ln x) / x ^ 2)
:= by deriv_calc

example (_ : x ≠ 0)
  : D (fun t ↦ sin t / t) x = the ((x * cos x - sin x) / x ^ 2)
:= by deriv_calc

example (_ : x ≠ 0)
  : D (fun t ↦ exp t / t^2) x = the ((x * exp x - 2 * exp x) / x ^ 3)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ t * √t) x = the (√x + (x * (√x)⁻¹ / 2))
:= by deriv_calc

example
  : D (fun t ↦ (t^2 + 1) * arctan t) x = the (2 * x * arctan x + 1)
:= by deriv_calc

example (_ : cos x ≠ 0)
  : D (fun t ↦ sec t * tan t) x = the (sec x * tan x * tan x + sec x * sec x ^ 2)
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ exp t * ln t) x = the (exp x * ln x + exp x / x)
:= by deriv_calc

example
  : D (fun t ↦ t / (t^2 + 1)) x = the ((1 - x ^ 2) / (x ^ 2 + 1)^2)
:= by deriv_calc

example
  : D (fun t ↦ sinh t * cosh t) x = the (cosh x ^ 2 + sinh x ^ 2)
:= by deriv_calc

example (_ : n > 0)
  : D (fun t ↦ t ^ n * exp t) x = the (n * x^(n-1) * exp x + x^n * exp x)
:= by deriv_calc

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t * arccos t) x = the (arccos x / √(1 - x ^ 2) - arcsin x / √(1 - x ^ 2))
:= by deriv_calc

example (_ : a > 0)
  : D (fun t ↦ t * a^t) x = the (a^x + x * a^x * ln a)
:= by deriv_calc

example (_ : sin x ≠ 0)
  : D (fun t ↦ 1 / (sin t)) x = the (-cos x / (sin x)^2)
:= by deriv_calc

example
  : D (exp ∘ sin) x = the (exp (sin x) * cos x)
:= by deriv_calc

example (_ : cos x > 0)
  : D (ln ∘ cos) x = the (-sin x / cos x)
:= by deriv_calc

example
  : D (sqrt ∘ exp) x = the (exp x / (2 * √(exp x)))
:= by deriv_calc

example
  : D (sin ∘ id) x = the (cos x)
:= by deriv_calc

example
  : D (cos ∘ (· ^ 2)) x = the (-2 * x * sin (x ^ 2))
:= by deriv_calc

example
  : D (fun t ↦ exp (-t^2)) x = the (-2 * x * exp (-x ^ 2))
:= by deriv_calc

example
  : D (fun t ↦ ln (t^2 + 1)) x = the (2 * x / (x ^ 2 + 1))
:= by deriv_calc

example
  : D (fun t ↦ √(1 + t^2)) x = the (x / √(1 + x ^ 2))
:= by deriv_calc

example
  : D (fun t ↦ sin (3 * t)) x = the (3 * cos (3 * x))
:= by deriv_calc

example
  : D (fun t ↦ (2 * t + 1)^5) x = the (10 * (2 * x + 1)^4)
:= by deriv_calc

example (_ : a ≠ 0) (_ : x / a > -1 ∧ x / a < 1)
  : D (fun t ↦ arcsin (t / a)) x = the (1 / (a * √(1 - (x/a)^2)))
:= by deriv_calc

example
  : D (fun t ↦ arctan (exp t)) x = the (exp x / (1 + (exp x)^2))
:= by deriv_calc

example (_ : x > 0)
  : D (fun t ↦ cosh (ln t)) x = the (sinh (ln x) / x)
:= by deriv_calc

example
  : D (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x) * (cos x - sin x))
:= by deriv_calc

example (_ : x ≠ 0)
  : D (fun t ↦ log 2 (abs t)) x = the (1 / (x * ln 2))
:= by deriv_calc

end


/-! # Tests for `lim_equiv` -/

section
variable {a : ℝ}

example
  : (lim 0 fun x ↦ sin x / x) = lim 0 fun x ↦ x / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ tan (2 * x) / x) = lim 0 fun x ↦ (2 * x) / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ x / (exp x - 1)) = lim 0 fun x ↦ x / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ ln (1 + 3 * x) / x) = lim 0 fun x ↦ (3 * x) / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ arcsin x / x) = lim 0 fun x ↦ x / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ (sin x * (exp (2 * x) - 1)) / (x * x))
    = lim 0 fun x ↦ (x * (2 * x)) / (x * x)
:= by lim_equiv

example
  : (lim 0 fun x ↦ x / (tan x * arcsin x)) = lim 0 fun x ↦ x / (x * x)
:= by lim_equiv

example
  : (lim 0 fun x ↦ (ln (1 + x) * arctan x) / (sin x * (exp x - 1)))
    = lim 0 fun x ↦ (x * x) / (x * x)
:= by lim_equiv

example (_ : a > 0 ∧ a ≠ 1)
  : (lim 0 fun x ↦ ((1 + x) ^ a - 1) / sin x) = lim 0 fun x ↦ (a * x) / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ (sin x * tan x * (exp x - 1)) / (x * x * x))
    = lim 0 fun x ↦ (x * x * x) / (x * x * x)
:= by lim_equiv

example
  : (lim 0 fun x ↦ (sin x * cos x) / x) = lim 0 fun x ↦ (x * cos x) / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ (exp x - 1) / (x * (x + 2)))
    = lim 0 fun x ↦ x / (x * (x + 2))
:= by lim_equiv

example
  : (lim 0 fun x ↦ (ln (1 + x) * (x ^ 2 + 1)) / (tan x * exp x))
    = lim 0 fun x ↦ (x * (x ^ 2 + 1)) / (x * exp x)
:= by lim_equiv

example
  : (lim 0 fun x ↦ sin (sin x) / x) = lim 0 fun x ↦ x / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ (exp (tan x) - 1) / x) = lim 0 fun x ↦ tan x / x
:= by lim_equiv

example
  : (lim 0 fun x ↦ ln (1 + x * sin x) / (x * x))
    = lim 0 fun x ↦ (x * sin x) / (x * x)
:= by lim_equiv

example
  : (lim 1 fun x ↦ sin (x - 1) / (x - 1)) = lim 1 fun x ↦ (x - 1) / (x - 1)
:= by lim_equiv

example
  : (lim 0 fun x ↦  (sin (2 * x) * (exp (3 * x) - 1))
                  / (tan (4 * x) * arcsin (5 * x)))
    = lim 0 fun x ↦ (2 * x * (3 * x)) / (4 * x * (5 * x))
:= by lim_equiv

example
  : (lim 0 fun x ↦ (ln (1 + 7 * x) * arctan (2 * x)) / (sin (3 * x) * (exp x - 1)))
    = lim 0 fun x ↦ (7 * x * (2 * x)) / (3 * x * x)
:= by lim_equiv

example
  : (lim 0 fun x ↦ (sin x * (x ^ 2 + 1)) / (tan x * cos x))
    = lim 0 fun x ↦ (x * (x ^ 2 + 1)) / (x * cos x)
:= by lim_equiv

example
  : (lim 0 fun x ↦  (x * (exp (2 * x) - 1) * (x + 3))
                  / (arcsin x * ln (1 + 3 * x) * (x + 4)))
    = lim 0 fun x ↦ (x * (2 * x) * (x + 3)) / (x * (3 * x) * (x + 4))
:= by lim_equiv

example
  : (lim 0 fun x ↦  (sin (x ^ 2 + x) * (exp (sin x) - 1))
                  / (ln (1 + x ^ 2) * tan x))
    =  lim 0 fun x ↦ ((x ^ 2 + x) * x) / (x ^ 2 * x)
:= by lim_equiv

example
  : (lim 0 fun x ↦  (arctan (exp x - 1) * sin (tan x))
                  / (sin x * arcsin (x ^ 2) * (exp (arcsin x) - 1)))
    = lim 0 fun x ↦ 1 / x ^ 2
:= by lim_equiv

example
  : (lim 0 fun x ↦  (ln (1 + sin x) * sin (x * cos x))
                  / (tan (ln (1 + x)) * (exp x - 1)))
    = lim 0 fun x ↦ (sin x * (x * cos x)) / (ln (1 + x) * x)
:= by lim_equiv

example
  : (lim 1 fun x ↦ (sin (x - 1) * (exp (x - 1) - 1)) / (tan (x - 1) * (x ^ 2 + 1)))
    = lim 1 fun x ↦ ((x - 1) * (x - 1)) / ((x - 1) * (x ^ 2 + 1))
:= by lim_equiv

example
  : (lim π fun x ↦ (ln (1 + (x - π)) * arcsin (x - π)) / (sin (x - π) * cos x))
    = lim π fun x ↦ ((x - π) * (x - π)) / ((x - π) * cos x)
:= by lim_equiv

example
  : (lim 0 fun x ↦  (sin x * tan (2 * x) * (exp (3 * x) - 1) * (x + 1))
                  / (x * ln (1 + x) * arcsin (2 * x) * cos x))
    = lim 0 fun x ↦ (x * (2 * x) * (3 * x) * (x + 1)) /
                    (x * x * (2 * x) * cos x)
:= by lim_equiv

end


/-! # Tests for `lim_rational` -/

section

example
  : (lim 1 fun x ↦ (x ^ 2 - 1) / (x - 1)) = the 2
:= by lim_rational

example
  : (lim 2 fun x ↦ (x ^ 3 - 8) / (x ^ 2 - 4)) = the 3
:= by lim_rational

example
  : (lim 0 fun x ↦ (x + 1) / x ^ 2) =. diverg
:= by lim_rational

example
  : (lim 0 fun x ↦ (x ^ 2 + 3 * x) / x) = the 3
:= by lim_rational

example
  : (lim 2 fun x ↦ (x ^ 2 - 4 * x + 4) / (x ^ 2 - 4)) = the 0
:= by lim_rational

example
  : (lim 1 fun x ↦ (x ^ 4 - 1) / (x - 1)) = the 4
:= by lim_rational

example
  : (lim 0 fun x ↦ (x ^ 4 - x ^ 3) / x ^ 3) = the (-1)
:= by lim_rational

example
  : (lim (-1) fun x ↦ (x ^ 2 - 1) / (x ^ 2 + 2 * x + 1)) =. diverg
:= by lim_rational

example
  : (lim 0 fun x ↦ (x ^ 2 + x) / x ^ 4) =. diverg
:= by lim_rational

example
  : (lim 3 fun x ↦ (2 * x ^ 2 - 18) / (x - 3)) = the 12
:= by lim_rational

end


/-! # Tests for `lim_luo` -/

section

example
  : (lim 0 fun x ↦ sin x / x) =? lim 0 fun x ↦ cos x / 1
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp x - 1) / x) =? lim 0 fun x ↦ exp x / 1
:= by lim_luo

example
  : (lim 0 fun x ↦ ln (x + 1) / x) =? lim 0 fun x ↦ (1 / (x + 1)) / 1
:= by lim_luo

example
  : (lim 0 fun x ↦ arctan x / x) =? lim 0 fun x ↦ (1 / (1 + x ^ 2)) / 1
:= by lim_luo

example
  : (lim 1 fun x ↦ (x ^ 2 - 1) / (x - 1)) =? lim 1 fun x ↦ (2 * x) / 1
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp (2 * x) - 1) / sin x) =? lim 0 fun x ↦ (exp (2 * x) * 2) / cos x
:= by lim_luo

example
  : (lim 0 fun x ↦ (1 - cos x) / x ^ 2) =? lim 0 fun x ↦ sin x / (2 * x)
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp x - x - 1) / x ^ 2)
    =? lim 0 fun x ↦ (exp x - 1) / (2 * x)
:= by lim_luo

example
  : (lim 0 fun x ↦ (cosh x - 1) / x ^ 2) =? lim 0 fun x ↦ sinh x / (2 * x)
:= by lim_luo

example
  : (lim 1 fun x ↦ (x ^ 4 - 4 * x + 3) / (x - 1)^2)
    =? lim 1 fun x ↦ (4 * x ^ 3 - 4) / (2 * (x - 1))
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp (x ^ 2) - 1) / (1 - cos x))
    =? lim 0 fun x ↦ (exp (x ^ 2) * (2 * x)) / sin x
:= by lim_luo

example
  : (lim 0 fun x ↦ (x - sin x) / x ^ 3)
    =? lim 0 fun x ↦ (1 - cos x) / (3 * x ^ 2)
:= by lim_luo

/-
example
  : (lim 0 fun x ↦ (tan x - x) / x ^ 3)
    =? lim 0 fun x ↦ (sec x ^ 2 - 1) / (3 * x ^ 2)
:= by lim_luo
-/

example
  : (lim 0 fun x ↦ (sinh x - x) / x ^ 3)
    =? lim 0 fun x ↦ (cosh x - 1) / (3 * x ^ 2)
:= by lim_luo

example
  : (lim 0 fun x ↦ (arcsin x - x) / x ^ 3)
    =? lim 0 fun x ↦ (1 / √(1 - x ^ 2) - 1) / (3 * x ^ 2)
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp x - 1 - x - x ^ 2 / 2) / x ^ 3)
    =? lim 0 fun x ↦ (exp x - 1 - x) / (3 * x ^ 2)
:= by lim_luo

example
  : (lim 0 fun x ↦ (cos x - 1 + x ^ 2 / 2) / x ^ 4)
    =? lim 0 fun x ↦ (- sin x + x) / (4 * x ^ 3)
:= by lim_luo

example
  : (lim 0 fun x ↦ (exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6) / x ^ 4)
    =? lim 0 fun x ↦ (exp x - 1 - x - x ^ 2 / 2) / (4 * x ^ 3)
:= by lim_luo

example
  : (lim 0 fun x ↦ (sin x - x + x ^ 3 / 6) / x ^ 5)
    =? lim 0 fun x ↦ (cos x - 1 + x ^ 2 / 2) / (5 * x ^ 4)
:= by lim_luo

example
  : (lim 0 fun x ↦ (sinh x - x - x ^ 3 / 6) / x ^ 5)
    =? lim 0 fun x ↦ (cosh x - 1 - x ^ 2 / 2) / (5 * x ^ 4)
:= by lim_luo

end


/-! # Overall Tests -/

example :
  (lim 1 fun x ↦ (arcsin (x^2 - 1) * (x^3 - 1)) / (tan (x - 1) * (x^4 - 1))) = the (3 / 2)
:= calc
        (lim 1 fun x ↦ (arcsin (x^2 - 1) * (x^3 - 1)) / (tan (x - 1) * (x^4 - 1)))
     =  lim 1 fun x ↦ ((x^2 - 1) * (x^3 - 1)) / ((x - 1) * (x^4 - 1))
        := by lim_equiv
  _  =  lim 1 fun x ↦ ((x - 1) * (x + 1) * (x^3 - 1)) / ((x - 1) * (x^4 - 1))
        := by lim_congr 1; ring
  _  =  lim 1 fun x ↦ ((x + 1) * (x^3 - 1)) / (x^4 - 1)
        := by lim_congr 1; field
  _  =  lim 1 fun x ↦ (x^4 + x^3 - x - 1) / (x^4 - 1)
        := by lim_congr 1; ring
  _  =  the (3 / 2)
        := by lim_rational

example :
  (lim 0 fun x ↦ (exp (x^2) - cos x) / (x * sin x)) = the (3 / 2)
:= calc
        (lim 0 fun x ↦ (exp (x^2) - cos x) / (x * sin x))
     =  lim 0 fun x ↦ (exp (x^2) - cos x) / (x * x)
        := by lim_equiv
  _  =  lim 0 fun x ↦ (exp (x^2) - cos x) / x^2
        := by lim_congr 1; ring
  _  =? lim 0 fun x ↦ (exp (x^2) * (2 * x) - (-sin x)) / (2 * x)
        := by lim_luo
  _  =  lim 0 fun x ↦ (exp (x^2) * (2 * x) + sin x) / (2 * x)
        := by lim_congr 1; ring
  _  =? lim 0 fun x ↦ (exp (x^2) * (4 * x^2) + 2 * exp (x^2) + cos x) / 2
        := by lim_luo
  _  =  the (3 / 2)
        := by lim_cont

example :
  (lim 1 fun x ↦ (arcsin (x^2 - 1) * (exp (x - 1) - 1)) / ((x - 1) * ln x)) = the 2
:= calc
        (lim 1 fun x ↦ (arcsin (x^2 - 1) * (exp (x - 1) - 1)) / ((x - 1) * ln x))
     =  lim 1 fun x ↦ ((x^2 - 1) * (x - 1)) / ((x - 1) * ln x)
        := by lim_equiv
  _  =  lim 1 fun x ↦ (x^2 - 1) / ln x
        := by lim_congr 1; field
  _  =? lim 1 fun x ↦ (2 * x) / x⁻¹
        := by lim_luo
  _  =  lim 1 fun x ↦ 2 * x^2
        := by lim_congr 1; field
  _  =  the 2
        := by lim_cont
