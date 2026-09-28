import «Calculus_21».Limit.Tactics.Subst

section
variable (f g : ℝ → ℝ) (a k d : ℝ)

example : lim a (f ∘ id) =? Lim (lim a id) f := by
  lim_subst

example : lim a (fun x => f x) =? Lim (lim a id) f := by
  lim_subst

example (hk : k ≠ 0) :
    lim a (f ∘ (fun x => k * x + d)) =? Lim (lim a (fun x => k * x + d)) f := by
  lim_subst

example : lim a (f ∘ (fun x => 3 * x + 2)) =?
    Lim (lim a (fun x => 3 * x + 2)) f := by
  lim_subst

example : lim a (f ∘ (fun x => x ^ 2)) =? Lim (lim a (fun x => x ^ 2)) f := by
  lim_subst

example : lim 0 (f ∘ (fun x => x ^ 2)) =? Lim (lim 0 (fun x => x ^ 2)) f := by
  lim_subst

example (h : AvoidsFiniteLimit g a) : lim a (f ∘ g) =? Lim (lim a g) f := by
  lim_subst using h

example : Lim (the a) f = lim a f := by simp

example : Lim pos_infty f = PosInftyLimitExpr f := rfl

example : Lim pos_infty f = lim pos_infty f := by simp

example : Lim neg_infty f = NegInftyLimitExpr f := rfl

example : Lim neg_infty f = lim neg_infty f := by simp

example : Lim infty f = InftyLimitExpr f := rfl

example : Lim infty f = lim infty f := by simp

example (L : ℝ) (hg : lim a g =. pos_infty) (hf : lim pos_infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  exact FuncLimitExpr.CompPosInfty hg hf

example (L : ℝ) (hg : lim a g =. neg_infty) (hf : lim neg_infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  exact FuncLimitExpr.CompNegInfty hg hf

example (L : ℝ) (hg : lim a g =. infty) (hf : lim infty f =. the L) :
    lim a (f ∘ g) =. the L := by
  exact FuncLimitExpr.CompInfty hg hf

example : Lim diverg f = unknown := by simp [LimitAtExpr]

example : Lim unknown f = unknown := by simp [LimitAtExpr]

-- Unavailable automation leaves the genuine avoidance obligation for the caller.
example (h : AvoidsFiniteLimit g a) : lim a (f ∘ g) =? Lim (lim a g) f := by
  lim_subst
  exact h

example : ¬ AvoidsFiniteLimit (fun _ : ℝ => d) a := by
  intro h
  obtain ⟨δ, hδ, hlocal⟩ := h d FuncLimitExpr.Constant
  have hx : a + δ / 2 ∈ Nbhd a δ := by
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  exact hlocal _ hx rfl

-- A constant map must not be discharged by avoidance automation.
example : True := by
  fail_if_success
    have : AvoidsFiniteLimit (fun _ : ℝ => d) a := by
      apply AutoAvoidsFiniteLimit.avoids (cond := True)
  trivial

end

-- Compute the inner limit only after the substitution step.
example (f : ℝ → ℝ) (L : ℝ) (hf : lim 0 f =. the L) :
    (lim 0 fun x => f (x ^ 2)) = the L := by
  apply LimitValue.finite_iff.mp
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _  =? Lim (lim 0 fun x ↦ x ^ 2) f
          := by lim_subst
    _  =  lim 0 f
          := by
            have hg : (lim 0 fun x : ℝ => x ^ 2) = the 0 := by lim_cont
            rw [hg, LimitAtExpr.finite]
    _  =. the L
          := hf

-- Rewrite an arbitrary inner limit only after substitution, then use the outer proof.
example (f g : ℝ → ℝ) (a L : ℝ) (havoid : AvoidsFiniteLimit g a)
    (hg : lim a g = pos_infty) (hf : lim pos_infty f =. the L) :
    (lim a fun x => f (g x)) = the L := by
  apply LimitValue.finite_iff.mp
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _  =? Lim (lim a g) f
          := by lim_subst using havoid
    _  =  lim pos_infty f
          := by rw [hg, LimitAtExpr.posInfty]
    _  =. the L
          := hf

example (f g : ℝ → ℝ) (a L : ℝ) (havoid : AvoidsFiniteLimit g a)
    (hg : lim a g = neg_infty) (hf : lim neg_infty f =. the L) :
    (lim a fun x => f (g x)) = the L := by
  apply LimitValue.finite_iff.mp
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _  =? Lim (lim a g) f
          := by lim_subst using havoid
    _  =  lim neg_infty f
          := by rw [hg, LimitAtExpr.negInfty]
    _  =. the L
          := hf

example (f g : ℝ → ℝ) (a L : ℝ) (havoid : AvoidsFiniteLimit g a)
    (hg : lim a g = infty) (hf : lim infty f =. the L) :
    (lim a fun x => f (g x)) = the L := by
  apply LimitValue.finite_iff.mp
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _  =? Lim (lim a g) f
          := by lim_subst using havoid
    _  =  lim infty f
          := by rw [hg, LimitAtExpr.unsignedInfty]
    _  =. the L
          := hf

-- A stronger relation cannot be obtained merely by applying the substitution tactic.
example (_f : ℝ → ℝ) : True := by
  fail_if_success
    have : (lim 0 fun x => _f (x ^ 2)) =. Lim (lim 0 fun x => x ^ 2) _f := by
      lim_subst
  trivial
