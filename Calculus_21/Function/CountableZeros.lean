import Calculus_21.Function.Defs

/-- The zero set of a real function is countable. -/
def Function.CountableZeros (f : ℝ → ℝ) : Prop := {x | f x = 0}.Countable

namespace Function.CountableZeros

theorem of_ne {f : ℝ → ℝ} (h : ∀ x, f x ≠ 0) : Function.CountableZeros f := by
  have he : {x | f x = 0} = ∅ := by ext x; simp [h x]
  simpa only [Function.CountableZeros, he] using (Set.countable_empty : (∅ : Set ℝ).Countable)

theorem of_injective {f : ℝ → ℝ} (h : Function.Injective f) : Function.CountableZeros f :=
  (Set.countable_singleton (0 : ℝ)).preimage h

theorem neg {f : ℝ → ℝ} (h : Function.CountableZeros f) :
    Function.CountableZeros (fun x ↦ -f x) := by
  simpa only [Function.CountableZeros, neg_eq_zero] using h

theorem inv {f : ℝ → ℝ} (h : Function.CountableZeros f) :
    Function.CountableZeros (fun x ↦ (f x)⁻¹) := by
  simpa only [Function.CountableZeros, inv_eq_zero] using h

theorem mul {f g : ℝ → ℝ} (hf : Function.CountableZeros f) (hg : Function.CountableZeros g) :
    Function.CountableZeros (fun x ↦ f x * g x) := by
  simpa only [Function.CountableZeros, mul_eq_zero, Set.setOf_or] using hf.union hg

theorem div {f g : ℝ → ℝ} (hf : Function.CountableZeros f) (hg : Function.CountableZeros g) :
    Function.CountableZeros (fun x ↦ f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem abs {f : ℝ → ℝ} (h : Function.CountableZeros f) :
    Function.CountableZeros (fun x ↦ |f x|) := by
  simpa only [Function.CountableZeros, abs_eq_zero] using h

theorem natPow {f : ℝ → ℝ} (h : Function.CountableZeros f) (n : ℕ) :
    Function.CountableZeros (fun x ↦ f x ^ n) :=
  h.mono (fun _ hx => by
    by_contra hn
    exact (pow_ne_zero _ hn) hx)

end Function.CountableZeros
