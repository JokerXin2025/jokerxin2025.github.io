import «Calculus_21».Limit.Tactics.Subst

set_option linter.style.header false

section Concrete
variable (f : ℝ → ℝ) (a b k : ℝ)

-- The exact requested substitution does not need a nonzero assumption on a.
example : (lim a fun x => ln (1 + (x-a)/a) / (x-a)) =?
    Lim (lim a fun x => x-a) (fun u => ln (1+u/a)/u) := by
  lim_subst

example : (lim a fun x => ln (1 + (x - a) / a) / (x - a)) =?
    (lim 0 fun u => ln (1 + u / a) / u) := by
  calc
    _ =? Lim (lim a fun x => x - a) (fun u => ln (1 + u / a) / u) := by
      lim_subst
    _ = lim 0 (fun u => ln (1 + u / a) / u) := by
      have hinner : (lim a fun x => x - a) = the 0 := by lim_cont
      rw [hinner, LimitAtExpr.finite]

example (ha : a ≠ 0) : (lim a fun x => ln (1 + (x-a)/a) / ((x-a)/a)) =?
    Lim (lim a fun x => (x-a)/a) (fun u => ln (1+u)/u) := by
  lim_subst

example (n : ℕ) (hn : 0 < n) :
    (lim a fun x => f ((x-a)^n)) =? Lim (lim a fun x => (x-a)^n) f := by
  lim_subst

-- Arbitrary approach points exercise separation from a nonzero inner limit.
example (n : ℕ) (hn : 0 < n) :
    (lim b fun x => f ((x-a)^n)) =? Lim (lim b fun x => (x-a)^n) f := by
  lim_subst

example : (lim b fun x => f ((x-a)^2)) =? Lim (lim b fun x => (x-a)^2) f := by
  lim_subst

example : (lim a fun x => f |x-a|) =? Lim (lim a fun x => |x-a|) f := by
  lim_subst

example : (lim b fun x => f |x-a|) =? Lim (lim b fun x => |x-a|) f := by
  lim_subst

example (ha : a ≠ 0) (hk : k ≠ 0) :
    (lim a fun x => f (k / x)) =? Lim (lim a fun x => k / x) f := by
  lim_subst

example (ha : a ≠ 0) :
    (lim a fun x => f x⁻¹) =? Lim (lim a fun x => x⁻¹) f := by
  lim_subst

example (hk : k ≠ 0) :
    (lim a fun x => f (-(k * (x-a)^4 + b) / k)) =?
      Lim (lim a fun x => -(k * (x-a)^4 + b) / k) f := by
  lim_subst

end Concrete

section Abstract
variable (f g : ℝ → ℝ) (a k L : ℝ) {c d : Prop}
    [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] (hc : c) (hd : d)

example : (lim a fun x => f (g x + k)) =? Lim (lim a fun x => g x + k) f := by
  lim_subst

example : (lim a fun x => f (k + g x)) =? Lim (lim a fun x => k + g x) f := by
  lim_subst

example : (lim a fun x => f (g x - k)) =? Lim (lim a fun x => g x - k) f := by
  lim_subst

example : (lim a fun x => f (k - g x)) =? Lim (lim a fun x => k - g x) f := by
  lim_subst

example : (lim a fun x => f (-g x)) =? Lim (lim a fun x => -g x) f := by
  lim_subst

example (hk : k ≠ 0) :
    (lim a fun x => f (k * g x)) =? Lim (lim a fun x => k * g x) f := by
  lim_subst

example (hk : k ≠ 0) :
    (lim a fun x => f (g x * k)) =? Lim (lim a fun x => g x * k) f := by
  lim_subst

example (hk : k ≠ 0) :
    (lim a fun x => f (g x / k)) =? Lim (lim a fun x => g x / k) f := by
  lim_subst

example (hk : k ≠ 0) (hL : L ≠ 0) :
    (lim a fun x => f (k / g x)) =? Lim (lim a fun x => k / g x) f := by
  lim_subst

example (hL : L ≠ 0) :
    (lim a fun x => f (g x)⁻¹) =? Lim (lim a fun x => (g x)⁻¹) f := by
  lim_subst

example (n : ℕ) (hn : 0 < n) :
    (lim a fun x => f (g x ^ n)) =? Lim (lim a fun x => g x ^ n) f := by
  lim_subst

example : (lim a fun x => f |g x|) =? Lim (lim a fun x => |g x|) f := by
  lim_subst

end Abstract

-- Failure tests require the tactic to close the goal, not merely make progress.
section Rejected
variable (f g h : ℝ → ℝ) (a k : ℝ)

example : True := by
  fail_if_success
    have : (lim a fun x => f (k * (x-a))) =?
        Lim (lim a fun x => k * (x-a)) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f ((x-a) * k)) =?
        Lim (lim a fun x => (x-a) * k) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f ((x-a) / k)) =?
        Lim (lim a fun x => (x-a) / k) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f (k / (x-a))) =?
        Lim (lim a fun x => k / (x-a)) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f (x-a)⁻¹) =?
        Lim (lim a fun x => (x-a)⁻¹) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f ((x-a)^0)) =?
        Lim (lim a fun x => (x-a)^0) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f (0 / (x+1))) =?
        Lim (lim a fun x => 0 / (x+1)) f := by lim_subst
  trivial

example {L M : ℝ} [AutoLimit g a L True] [AutoLimit h a M True]
    [AutoAvoidsFiniteLimit g a True] [AutoAvoidsFiniteLimit h a True] : True := by
  fail_if_success
    have : (lim a fun x => f (g x + h x)) =?
        Lim (lim a fun x => g x + h x) f := by lim_subst
  fail_if_success
    have : (lim a fun x => f (g x * h x)) =?
        Lim (lim a fun x => g x * h x) f := by lim_subst
  trivial

example {L : ℝ} [AutoLimit g a L True] : True := by
  fail_if_success
    have : (lim a fun x => f (g x + k)) =?
        Lim (lim a fun x => g x + k) f := by lim_subst
  trivial

example [AutoAvoidsFiniteLimit g a True] : True := by
  fail_if_success
    have : (lim a fun x => f (g x + k)) =?
        Lim (lim a fun x => g x + k) f := by lim_subst
  trivial

end Rejected
