import Calculus_21.Differential.Rules

section
variable {m n : ℕ} {F : RFunction} {x d : ℝ}

-- A derivative of the operator alone cannot bypass a missing lower order.
example (hmissing : ¬ isNthDerivableAt n F x) :
    ¬ NthDeriv (n + 1) F x d :=
  fun h => hmissing h.lower

example (h : NthDeriv n F x d) (hmn : m ≤ n) :
    ∃ v, NthDeriv m F x v :=
  h.lower_order hmn

example (h : NthDeriv n F x d) : x ∈ F.domain :=
  h.mem_domain (Nat.zero_le n)

example (h : NthDeriv n F x d) (hmn : m ≤ n) :
    x ∈ (NthDiff m F).domain :=
  h.mem_domain hmn

example (h : NthDeriv n F x d) : NthDeriv n ((0 : ℝ) • F) x 0 := by
  simpa only [zero_mul] using h.SMul (k := 0)

example (h : NthDeriv n F x d) : NthDeriv n (-F) x (-d) :=
  h.Neg

example {f : ℝ → ℝ} :
    NthDeriv n ⟨f, Iii⟩ x d ↔ Dₙ n f x =. the d :=
  ⟨NthDeriv.toNthDerivExpr, NthDeriv.fromNthDerivExpr⟩

end
