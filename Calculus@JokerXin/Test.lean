import «Calculus_21»


/-! # Tests for `deriv` -/

variable {x a b C : ℝ} {n : ℤ}

example
  : D (const C) x = the 0
:= by deriv

example
  : D (fun _ ↦ 5) x = the 0
:= by deriv

example
  : D id x = the 1
:= by deriv

example
  : D (·) x = the 1
:= by deriv

example
  : D (-·) x = the (-1)
:= by deriv

example
  : D (fun t ↦ -t) x = the (-1)
:= by deriv

example (_ : x ≠ 0)
  : D (·⁻¹) x = the (-1 / x^2)
:= by deriv

example (_ : x ≠ 0)
  : D abs x = the (x / |x|)
:= by deriv

example (_ : x > 0)
  : D sqrt x = the (1 / (2 * √x))
:= by deriv

example (_ : n > 0)
  : D (· ^ n) x = the (n * x ^ (n - 1))
:= by deriv

example (_ : x > 0)
  : D (· ^ a) x = the (a * x ^ (a - 1))
:= by deriv

example
  : D exp x = the (exp x)
:= by deriv

example (_ : a > 0)
  : D (a ^ ·) x = the (a ^ x * ln a)
:= by deriv

example (_ : x > 0)
  : D ln x = the (1 / x)
:= by deriv

example (_ : a > 0 ∧ a ≠ 1) (_ : x > 0)
  : D (log a) x = the (1 / (x * ln a))
:= by deriv

example
  : D sin x = the (cos x)
:= by deriv

example
  : D cos x = the (-sin x)
:= by deriv

example (_ : cos x ≠ 0)
  : D tan x = the (sec x ^2)
:= by deriv

example (_ : sin x ≠ 0)
  : D cot x = the (- csc x ^2)
:= by deriv

example (_ : cos x ≠ 0)
  : D sec x = the (sec x * tan x)
:= by deriv

example (_ : sin x ≠ 0)
  : D csc x = the (-csc x * cot x)
:= by deriv

example
  : D sinh x = the (cosh x)
:= by deriv

example
  : D cosh x = the (sinh x)
:= by deriv

example
  : D tanh x = the (sech x ^2)
:= by deriv

example (_ : x ≠ 0)
  : D coth x = the (- csch x ^2)
:= by deriv

example
  : D sech x = the (-sech x * tanh x)
:= by deriv

example (_ : x ≠ 0)
  : D csch x = the (-csch x * coth x)
:= by deriv

example
  : D (fun t ↦ sinh t) x = the (cosh x)
:= by deriv

example
  : D (fun t ↦ cosh t) x = the (sinh x)
:= by deriv

example
  : D (fun t ↦ tanh t) x = the (sech x ^2)
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D arcsin x = the (1 / √(1 - x^2))
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D arccos x = the (-1 / √(1 - x^2))
:= by deriv

example
  : D arctan x = the (1 / (1 + x^2))
:= by deriv

example
  : D arccot x = the (-1 / (1 + x^2))
:= by deriv

example (_ : x < -1 ∨ x > 1)
  : D arcsec x = the (1 / (|x| * √(x^2 - 1)))
:= by deriv

example (_ : x < -1 ∨ x > 1)
  : D arccsc x = the (-1 / (|x| * √(x^2 - 1)))
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t) x = the (1 / √(1 - x^2))
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arccos t) x = the (-1 / √(1 - x^2))
:= by deriv

example (_ : x > -1) : D (fun x ↦ ln (x + 1)) x = the (1 / (x + 1)) := by deriv

example (_ : x > -1) : x + 1 > 0 := by linarith

example
  : D (fun t ↦ arctan t) x = the (1 / (1 + x^2))
:= by deriv

example (_ : x ≠ 0)
  : D (fun t ↦ |t|) x = the (x / |x|)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ √t) x = the (1 / (2 * √x))
:= by deriv

example (_ : x ≠ 0)
  : D (fun t ↦ t⁻¹) x = the (-1 / x^2)
:= by deriv

example
  : D (fun t ↦ exp t) x = the (exp x)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ ln t) x = the (1 / x)
:= by deriv

example (_ : a > 0)
  : D (fun t ↦ a ^ t) x = the (a ^ x * ln a)
:= by deriv

example
  : D (sin + cos) x = the (cos x - sin x)
:= by deriv

example
  : D (exp - id) x = the (exp x - 1)
:= by deriv

example
  : D (fun t ↦ 3 * t) x = the 3
:= by deriv

example
  : D (fun t ↦ t + 5) x = the 1
:= by deriv

example
  : D (fun t ↦ 4 * t^3) x = the (12 * x^2)
:= by deriv

example
  : D (fun t ↦ t^2 + 2 * t + 1) x = the (2 * x + 2)
:= by deriv

example
  : D (fun t ↦ a * sin t + C * cos t) x = the (a * cos x - C * sin x)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ 5 * exp t - 2 * ln t) x = the (5 * exp x - 2 / x)
:= by deriv

example
  : D (fun t ↦ t^4 - t^3 + t^2 - t) x = the (4*x^3 - 3*x^2 + 2*x - 1)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ 2 * √t + 3 * t⁻¹) x = the (1 / √x - 3 / x^2)
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t + arccos t) x = the 0
:= by deriv

example
  : D (fun t ↦ arctan t + arccot t) x = the 0
:= by deriv

example
  : D (fun t ↦ sinh t + cosh t) x = the (cosh x + sinh x)
:= by deriv

example (_ : a > 0) (_ : x > 0)
  : D (fun t ↦ 7 * a^t + 8 * log 10 t) x = the (7 * a^x * ln a + 8 / (x * ln 10))
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ |t| + t) x = the (x / |x| + 1)
:= by deriv

example (_ : cos x ≠ 0 ∧ sin x ≠ 0)
  : D (fun t ↦ sec t - csc t) x = the (sec x * tan x + csc x * cot x)
:= by deriv

example (_ : n > 0) (_ : x > 0)
  : D (fun t ↦ t^n + t^a) x = the (n * x^(n-1) + a * x^(a-1))
:= by deriv

example
  : D (fun t ↦ t - 2 * arctan t) x = the (1 - 2 / (1 + x^2))
:= by deriv

example
  : D (fun t ↦ 4 * tanh t) x = the (4 * sech x ^ 2)
:= by deriv

example
  : D (fun t ↦ exp t + t) x = the (exp x + 1)
:= by deriv

example (_ : x > 0)
  : D (id * ln) x = the (ln x + 1)
:= by deriv

example (_ : x ≠ 0) (_ : cos x ≠ 0)
  : D (tan / id) x = the ((x * sec x ^2 - tan x) / x^2)
:= by deriv

example
  : D (fun t ↦ t * exp t) x = the (exp x + x * exp x)
:= by deriv

example
  : D (fun t ↦ sin t * cos t) x = the (cos x * cos x - sin x * sin x)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ t^2 * ln t) x = the (2 * x * ln x + x)
:= by deriv

example
  : D (fun t ↦ exp t * sin t) x = the (exp x * sin x + exp x * cos x)
:= by deriv

example (_ : x ≠ 1)
  : D (fun t ↦ (t + 1) / (t - 1)) x = the (-2 / (x - 1)^2)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ ln t / t) x = the ((1 - ln x) / x^2)
:= by deriv

example (_ : x ≠ 0)
  : D (fun t ↦ sin t / t) x = the ((x * cos x - sin x) / x^2)
:= by deriv

example (_ : x ≠ 0)
  : D (fun t ↦ exp t / t^2) x = the ((x * exp x - 2 * exp x) / x^3)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ t * √t) x = the (√x + (x * (√x)⁻¹ / 2))
:= by deriv

example
  : D (fun t ↦ (t^2 + 1) * arctan t) x = the (2 * x * arctan x + 1)
:= by deriv

example (_ : cos x ≠ 0)
  : D (fun t ↦ sec t * tan t) x = the (sec x * tan x * tan x + sec x * sec x ^ 2)
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ exp t * ln t) x = the (exp x * ln x + exp x / x)
:= by deriv

example
  : D (fun t ↦ t / (t^2 + 1)) x = the ((1 - x^2) / (x^2 + 1)^2)
:= by deriv

example
  : D (fun t ↦ sinh t * cosh t) x = the (cosh x ^ 2 + sinh x ^ 2)
:= by deriv

example (_ : n > 0)
  : D (fun t ↦ t ^ n * exp t) x = the (n * x^(n-1) * exp x + x^n * exp x)
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D (fun t ↦ arcsin t * arccos t) x = the (arccos x / √(1 - x^2) - arcsin x / √(1 - x^2))
:= by deriv

example (_ : a > 0)
  : D (fun t ↦ t * a^t) x = the (a^x + x * a^x * ln a)
:= by deriv

example (_ : sin x ≠ 0)
  : D (fun t ↦ 1 / (sin t)) x = the (-cos x / (sin x)^2)
:= by deriv

example
  : D (exp ∘ sin) x = the (exp (sin x) * cos x)
:= by deriv

example (_ : cos x > 0)
  : D (ln ∘ cos) x = the (-sin x / cos x)
:= by deriv

example
  : D (sqrt ∘ exp) x = the (exp x / (2 * √(exp x)))
:= by deriv

example
  : D (sin ∘ id) x = the (cos x)
:= by deriv

example
  : D (cos ∘ (· ^ 2)) x = the (-2 * x * sin (x^2))
:= by deriv

example
  : D (fun t ↦ exp (-t^2)) x = the (-2 * x * exp (-x^2))
:= by deriv

example
  : D (fun t ↦ ln (t^2 + 1)) x = the (2 * x / (x^2 + 1))
:= by deriv

example
  : D (fun t ↦ √(1 + t^2)) x = the (x / √(1 + x^2))
:= by deriv

example
  : D (fun t ↦ sin (3 * t)) x = the (3 * cos (3 * x))
:= by deriv

example
  : D (fun t ↦ (2 * t + 1)^5) x = the (10 * (2 * x + 1)^4)
:= by deriv

example (_ : a ≠ 0) (_ : x / a > -1 ∧ x / a < 1)
  : D (fun t ↦ arcsin (t / a)) x = the (1 / (a * √(1 - (x/a)^2)))
:= by deriv

example
  : D (fun t ↦ arctan (exp t)) x = the (exp x / (1 + (exp x)^2))
:= by deriv

example (_ : x > 0)
  : D (fun t ↦ cosh (ln t)) x = the (sinh (ln x) / x)
:= by deriv

example
  : D (fun t ↦ exp (sin t + cos t)) x = the (exp (sin x + cos x) * (cos x - sin x))
:= by deriv

example (_ : x ≠ 0)
  : D (fun t ↦ log 2 (abs t)) x = the (1 / (x * ln 2))
:= by deriv


/-! # Tests for `lim_luo` -/

example
  : lim (fun x ↦ sin x / x) 0 =? lim (fun x ↦ cos x / 1) 0
:= by lim_luo

example
  : lim (fun x ↦ (exp x - 1) / x) 0 =? lim (fun x ↦ exp x / 1) 0
:= by lim_luo

example
  : lim (fun x ↦ ln (x + 1) / x) 0 =? lim (fun x ↦ (1 / (x + 1)) / 1) 0
:= by lim_luo

example
  : lim (fun x ↦ arctan x / x) 0 =? lim (fun x ↦ (1 / (1 + x^2)) / 1) 0
:= by lim_luo

example
  : lim (fun x ↦ (x^2 - 1) / (x - 1)) 1 =? lim (fun x ↦ (2 * x) / 1) 1
:= by lim_luo

example
  : lim (fun x ↦ (exp (2 * x) - 1) / sin x) 0 =? lim (fun x ↦ (exp (2 * x) * 2) / cos x) 0
:= by lim_luo

example
  : lim (fun x ↦ (1 - cos x) / x^2) 0 =? lim (fun x ↦ sin x / (2 * x)) 0
:= by lim_luo

example
  : lim (fun x ↦ (exp x - x - 1) / x^2) 0 =? lim (fun x ↦ (exp x - 1) / (2 * x)) 0
:= by lim_luo

example
  : lim (fun x ↦ (cosh x - 1) / x^2) 0 =? lim (fun x ↦ sinh x / (2 * x)) 0
:= by lim_luo

example
  : lim (fun x ↦ (x^4 - 4 * x + 3) / (x - 1)^2) 1 =? lim (fun x ↦ (4 * x^3 - 4) / (2 * (x - 1))) 1
:= by lim_luo

example
  : lim (fun x ↦ (exp (x^2) - 1) / (1 - cos x)) 0 =? lim (fun x ↦ (exp (x^2) * (2 * x)) / sin x) 0
:= by lim_luo

example
  : lim (fun x ↦ (x - sin x) / x^3) 0 =? lim (fun x ↦ (1 - cos x) / (3 * x^2)) 0
:= by lim_luo

example
  : lim (fun x ↦ (tan x - x) / x^3) 0 =? lim (fun x ↦ (sec x ^ 2 - 1) / (3 * x^2)) 0
:= by lim_luo

example
  : lim (fun x ↦ (sinh x - x) / x^3) 0 =? lim (fun x ↦ (cosh x - 1) / (3 * x^2)) 0
:= by lim_luo

example
  : lim (fun x ↦ (arcsin x - x) / x^3) 0 =? lim (fun x ↦ (1 / √(1 - x^2) - 1) / (3 * x^2)) 0
:= by lim_luo

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2) / x^3) 0 =? lim (fun x ↦ (exp x - 1 - x) / (3 * x^2)) 0
:= by lim_luo

example
  : lim (fun x ↦ (cos x - 1 + x^2 / 2) / x^4) 0 =? lim (fun x ↦ (- sin x + x) / (4 * x^3)) 0
:= by lim_luo

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2 - x^3 / 6) / x^4) 0 =? lim (fun x ↦ (exp x - 1 - x - x^2 / 2) / (4 * x^3)) 0
:= by lim_luo

example
  : lim (fun x ↦ (sin x - x + x^3 / 6) / x^5) 0 =? lim (fun x ↦ (cos x - 1 + x^2 / 2) / (5 * x^4)) 0
:= by lim_luo

example
  : lim (fun x ↦ (sinh x - x - x^3 / 6) / x^5) 0 =? lim (fun x ↦ (cosh x - 1 - x^2 / 2) / (5 * x^4)) 0
:= by lim_luo

/-
example
  : lim (fun x ↦ sin x / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ (exp x - 1) / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ ln (x + 1) / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ arctan x / x) 0 = the 1
:= by lim_luo

example
  : lim (fun x ↦ (x^2 - 1) / (x - 1)) 1 = the 2
:= by lim_luo

example
  : lim (fun x ↦ (exp (2 * x) - 1) / sin x) 0 = the 2
:= by lim_luo

example
  : lim (fun x ↦ (1 - cos x) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - x - 1) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (cosh x - 1) / x^2) 0 = the (1 / 2)
:= by lim_luo!

example
  : lim (fun x ↦ (x^4 - 4 * x + 3) / (x - 1)^2) 1 = the 6
:= by lim_luo!

example
  : lim (fun x ↦ (exp (x^2) - 1) / (1 - cos x)) 0 = the 2
:= by lim_luo!

example
  : lim (fun x ↦ (x - sin x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (tan x - x) / x^3) 0 = the (1 / 3)
:= by lim_luo!

example
  : lim (fun x ↦ (sinh x - x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (arcsin x - x) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2) / x^3) 0 = the (1 / 6)
:= by lim_luo!

example
  : lim (fun x ↦ (cos x - 1 + x^2 / 2) / x^4) 0 = the (1 / 24)
:= by lim_luo!

example
  : lim (fun x ↦ (exp x - 1 - x - x^2 / 2 - x^3 / 6) / x^4) 0 = the (1 / 24)
:= by lim_luo!

example
  : lim (fun x ↦ (sin x - x + x^3 / 6) / x^5) 0 = the (1 / 120)
:= by lim_luo!

example
  : lim (fun x ↦ (sinh x - x - x^3 / 6) / x^5) 0 = the (1 / 120)
:= by lim_luo!
-/
