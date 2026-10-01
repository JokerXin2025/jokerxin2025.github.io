import «Calculus_21».Limit.Tactics.Cont
import «Calculus_21».Limit.Expr.Subst
set_option linter.style.header false


/-- Sufficient side conditions for sound punctured-neighborhood substitution. -/
class AutoAvoidsFiniteLimit (g : ℝ → ℝ) (a : ℝ) (cond : outParam Prop) where
  avoids : cond → AvoidsFiniteLimit g a

/-- Identify the finite value only after limit automation has supplied it. -/
theorem avoidsFiniteLimit_of_autoLimit {g : ℝ → ℝ} {a L : ℝ} {cond : Prop}
    [AutoLimit g a L cond] (hc : cond) (hlocal : LocallyAvoids g a L)
  : AvoidsFiniteLimit g a
:= by
  intro b hb
  have heq : the L = the b :=
    (LimitValue.finite_iff.mp (AutoLimit.eq hc)).symm.trans
      (LimitValue.finite_iff.mp hb)
  have hLb : L = b := by injection heq
  simpa only [← hLb] using hlocal

instance autoAvoidsFiniteLimit_id (a : ℝ)
  : AutoAvoidsFiniteLimit id a True where
  avoids hc := avoidsFiniteLimit_of_autoLimit hc
    ⟨1, zero_lt_one, fun _ hx ↦ hx.2.2⟩

instance autoAvoidsFiniteLimit_identity (a : ℝ)
  : AutoAvoidsFiniteLimit (fun x ↦ x) a True := autoAvoidsFiniteLimit_id a

instance autoAvoidsFiniteLimit_affine (k d a : ℝ) {cond : Prop}
    [AutoLimit (fun x ↦ k * x + d) a (k * a + d) cond]
  : AutoAvoidsFiniteLimit (fun x ↦ k * x + d) a (cond ∧ k ≠ 0) where
  avoids := by
    rintro ⟨hc, hk⟩
    apply avoidsFiniteLimit_of_autoLimit hc
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx heq
    apply hx.2.2
    exact (mul_left_cancel₀ hk) (add_right_cancel heq)

instance autoAvoidsFiniteLimit_square (a : ℝ) {cond : Prop}
    [AutoLimit (fun x ↦ x ^ 2) a (a ^ 2) cond]
  : AutoAvoidsFiniteLimit (fun x ↦ x ^ 2) a cond where
  avoids := by
    intro hc
    apply avoidsFiniteLimit_of_autoLimit hc
    by_cases ha : a = 0
    · subst a
      refine ⟨1, zero_lt_one, ?_⟩
      intro x hx heq
      apply hx.2.2
      nlinarith [sq_nonneg x]
    · refine ⟨|a|, abs_pos.mpr ha, ?_⟩
      intro x hx heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
      · exact hx.2.2 h
      · rcases lt_or_gt_of_ne ha with ha | ha
        · rw [abs_of_neg ha] at hx
          linarith [hx.2.1]
        · rw [abs_of_pos ha] at hx
          linarith [hx.1]

/-- Injective outer maps preserve avoidance of the inner finite limit. -/
theorem locallyAvoids_comp_injective {f g : ℝ → ℝ} {a L : ℝ}
    (hg : LocallyAvoids g a L) (hf : Function.Injective f) :
    LocallyAvoids (fun x => f (g x)) a (f L) := by
  obtain ⟨δ, hδ, hne⟩ := hg
  exact ⟨δ, hδ, fun x hx heq => hne x hx (hf heq)⟩

/-- Convergence excludes the second preimage `-L` when `L` is nonzero. -/
theorem locallyAvoids_comp_eq_or_eq_neg {f g : ℝ → ℝ} {a L : ℝ} {c : Prop}
    [AutoLimit g a L c] (hc : c) (hg : LocallyAvoids g a L)
    (hf : ∀ y, f y = f L → y = L ∨ y = -L) :
    LocallyAvoids (fun x => f (g x)) a (f L) := by
  obtain ⟨s, hs, hne⟩ := hg
  by_cases hL : L = 0
  · refine ⟨s, hs, ?_⟩
    intro x hx heq
    rcases hf (g x) heq with h | h
    · exact hne x hx h
    · exact hne x hx (by simpa [hL] using h)
  · have hlim := FuncLimit.fromFuncLimitExpr (dom := Set.univ)
      ⟨1, zero_lt_one, by simp⟩ (AutoLimit.eq (f := g) (x₀ := a) hc)
    obtain ⟨δ, hδ, hbound⟩ := hlim.2 |L| (abs_pos.mpr hL)
    refine ⟨min δ s, lt_min hδ hs, ?_⟩
    intro x hx heq
    have hxδ : x ∈ Nbhd a δ :=
      ⟨by linarith [hx.1, min_le_left δ s],
        by linarith [hx.2.1, min_le_left δ s], hx.2.2⟩
    have hxs : x ∈ Nbhd a s :=
      ⟨by linarith [hx.1, min_le_right δ s],
        by linarith [hx.2.1, min_le_right δ s], hx.2.2⟩
    rcases hf (g x) heq with h | h
    · exact hne x hxs h
    · have hb : g x ∈ Nbho L |L| := hbound x hxδ
      rw [h] at hb
      rcases lt_or_gt_of_ne hL with hL | hL
      · rw [abs_of_neg hL] at hb
        linarith [hb.2]
      · rw [abs_of_pos hL] at hb
        linarith [hb.1]

section Algebra
variable (g : ℝ → ℝ) (a k : ℝ) {L : ℝ} {c d e : Prop}
    [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d]

instance autoAvoidsFiniteLimit_add_const
    [AutoLimit (fun x => g x + k) a (L + k) e] :
    AutoAvoidsFiniteLimit (fun x => g x + k) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => add_right_cancel h)

instance autoAvoidsFiniteLimit_const_add
    [AutoLimit (fun x => k + g x) a (k + L) e] :
    AutoAvoidsFiniteLimit (fun x => k + g x) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => add_left_cancel h)

instance autoAvoidsFiniteLimit_sub_const
    [AutoLimit (fun x => g x - k) a (L - k) e] :
    AutoAvoidsFiniteLimit (fun x => g x - k) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => sub_left_inj.mp h)

instance autoAvoidsFiniteLimit_const_sub
    [AutoLimit (fun x => k - g x) a (k - L) e] :
    AutoAvoidsFiniteLimit (fun x => k - g x) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => sub_right_inj.mp h)

instance autoAvoidsFiniteLimit_neg
    [AutoLimit (fun x => -g x) a (-L) e] :
    AutoAvoidsFiniteLimit (fun x => -g x) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc)) neg_injective

instance autoAvoidsFiniteLimit_const_mul
    [AutoLimit (fun x => k * g x) a (k * L) e] :
    AutoAvoidsFiniteLimit (fun x => k * g x) a (c ∧ d ∧ e ∧ k ≠ 0) where
  avoids := by
    rintro ⟨hc, hd, he, hk⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => mul_left_cancel₀ hk h)

instance autoAvoidsFiniteLimit_mul_const
    [AutoLimit (fun x => g x * k) a (L * k) e] :
    AutoAvoidsFiniteLimit (fun x => g x * k) a (c ∧ d ∧ e ∧ k ≠ 0) where
  avoids := by
    rintro ⟨hc, hd, he, hk⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => mul_right_cancel₀ hk h)

instance autoAvoidsFiniteLimit_div_const
    [AutoLimit (fun x => g x / k) a (L / k) e] :
    AutoAvoidsFiniteLimit (fun x => g x / k) a (c ∧ d ∧ e ∧ k ≠ 0) where
  avoids := by
    rintro ⟨hc, hd, he, hk⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
      (fun _ _ h => (div_left_inj' hk).mp h)

instance autoAvoidsFiniteLimit_const_div
    [AutoLimit (fun x => k / g x) a (k / L) e] :
    AutoAvoidsFiniteLimit (fun x => k / g x) a (c ∧ d ∧ e ∧ k ≠ 0 ∧ L ≠ 0) where
  avoids := by
    rintro ⟨hc, hd, he, hk, _⟩
    apply avoidsFiniteLimit_of_autoLimit he
    apply locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    intro y z h
    exact inv_injective (mul_left_cancel₀ hk (by simpa only [div_eq_mul_inv] using h))

instance autoAvoidsFiniteLimit_inv
    [AutoLimit (fun x => (g x)⁻¹) a L⁻¹ e] :
    AutoAvoidsFiniteLimit (fun x => (g x)⁻¹) a (c ∧ d ∧ e ∧ L ≠ 0) where
  avoids := by
    rintro ⟨hc, hd, he, _⟩
    apply avoidsFiniteLimit_of_autoLimit he
    exact locallyAvoids_comp_injective
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc)) inv_injective

instance autoAvoidsFiniteLimit_pow (n : ℕ)
    [AutoLimit (fun x => g x ^ n) a (L ^ n) e] :
    AutoAvoidsFiniteLimit (fun x => g x ^ n) a (c ∧ d ∧ e ∧ 0 < n) where
  avoids := by
    rintro ⟨hc, hd, he, hn⟩
    apply avoidsFiniteLimit_of_autoLimit he
    apply locallyAvoids_comp_eq_or_eq_neg hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    intro y h
    exact ((pow_eq_pow_iff_of_ne_zero (Nat.ne_of_gt hn)).mp h).imp_right And.left

instance autoAvoidsFiniteLimit_abs
    [AutoLimit (fun x => |g x|) a |L| e] :
    AutoAvoidsFiniteLimit (fun x => |g x|) a (c ∧ d ∧ e) where
  avoids := by
    rintro ⟨hc, hd, he⟩
    apply avoidsFiniteLimit_of_autoLimit he
    apply locallyAvoids_comp_eq_or_eq_neg hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    exact fun _ h => abs_eq_abs.mp h

end Algebra

-- Bare operators do not expose an inner function for compositional inference.
instance autoAvoidsFiniteLimit_reciprocal (k a : ℝ) :
    AutoAvoidsFiniteLimit (k / ·) a (k ≠ 0 ∧ a ≠ 0) where
  avoids := by
    rintro ⟨hk, ha⟩
    exact (autoAvoidsFiniteLimit_const_div id a k).avoids (by
      repeat' constructor <;> first | assumption | trivial)

instance autoAvoidsFiniteLimit_inverse (a : ℝ) :
    AutoAvoidsFiniteLimit Inv.inv a (a ≠ 0) where
  avoids ha := (autoAvoidsFiniteLimit_inv id a).avoids (by
    repeat' constructor <;> first | assumption | trivial)

/-! # Elementary function avoidance -/

/-- Transfer avoidance through a function that separates its value locally.
The inner limit, rather than the value at the approach point, controls the domain. -/
theorem locallyAvoids_comp_of_autoLimit {f g : ℝ → ℝ} {a L : ℝ} {c : Prop}
    [AutoLimit g a L c] (hc : c) (hg : LocallyAvoids g a L)
    (hf : ∃ r > 0, ∀ y ∈ Nbho L r, f y = f L → y = L) :
    LocallyAvoids (fun x => f (g x)) a (f L) := by
  obtain ⟨r, hr, hf⟩ := hf
  have hlim := FuncLimit.fromFuncLimitExpr (dom := Set.univ)
    ⟨1, zero_lt_one, by simp⟩ (AutoLimit.eq (f := g) (x₀ := a) hc)
  obtain ⟨δ, hδ, hbound⟩ := hlim.2 r hr
  obtain ⟨s, hs, hne⟩ := hg
  refine ⟨min δ s, lt_min hδ hs, ?_⟩
  intro x hx heq
  have hxδ : x ∈ Nbhd a δ :=
    ⟨by linarith [hx.1, min_le_left δ s],
      by linarith [hx.2.1, min_le_left δ s], hx.2.2⟩
  have hxs : x ∈ Nbhd a s :=
    ⟨by linarith [hx.1, min_le_right δ s],
      by linarith [hx.2.1, min_le_right δ s], hx.2.2⟩
  exact hne x hxs (hf (g x) (hbound x hxδ) heq)

instance autoAvoidsFiniteLimit_compExp (g : ℝ → ℝ) (a : ℝ)
    {L : ℝ} {c d : Prop} [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] :
    AutoAvoidsFiniteLimit (fun x => exp (g x)) a (c ∧ d) where
  avoids := by
    rintro ⟨hc, hd⟩
    apply avoidsFiniteLimit_of_autoLimit hc
    apply locallyAvoids_comp_of_autoLimit hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    exact ⟨1, zero_lt_one, fun _ _ h => Real.exp_injective h⟩

instance autoAvoidsFiniteLimit_exp (a : ℝ) : AutoAvoidsFiniteLimit exp a True where
  avoids hc := avoidsFiniteLimit_of_autoLimit hc
    ⟨1, zero_lt_one, fun _ hx h => hx.2.2 (Real.exp_injective h)⟩

instance autoAvoidsFiniteLimit_compLn (g : ℝ → ℝ) (a : ℝ)
    {L : ℝ} {c d : Prop} [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] :
    AutoAvoidsFiniteLimit (fun x => ln (g x)) a ((c ∧ d) ∧ 0 < L) where
  avoids := by
    rintro ⟨⟨hc, hd⟩, hL⟩
    apply avoidsFiniteLimit_of_autoLimit (show c ∧ 0 < L from ⟨hc, hL⟩)
    apply locallyAvoids_comp_of_autoLimit hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    refine ⟨L, hL, ?_⟩
    intro y hy heq
    exact Real.log_injOn_pos (show 0 < y by linarith [hy.1]) hL heq

instance autoAvoidsFiniteLimit_ln (a : ℝ) : AutoAvoidsFiniteLimit ln a (0 < a) where
  avoids ha := by
    apply avoidsFiniteLimit_of_autoLimit ha
    refine ⟨a, ha, ?_⟩
    intro x hx heq
    exact hx.2.2 (Real.log_injOn_pos (show 0 < x by linarith [hx.1]) ha heq)

instance autoAvoidsFiniteLimit_compSqrt (g : ℝ → ℝ) (a : ℝ)
    {L : ℝ} {c d : Prop} [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] :
    AutoAvoidsFiniteLimit (fun x => sqrt (g x)) a ((c ∧ d) ∧ 0 < L) where
  avoids := by
    rintro ⟨⟨hc, hd⟩, hL⟩
    apply avoidsFiniteLimit_of_autoLimit (show c ∧ 0 < L from ⟨hc, hL⟩)
    apply locallyAvoids_comp_of_autoLimit hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    refine ⟨L, hL, ?_⟩
    intro y hy heq
    exact (Real.sqrt_inj (by linarith [hy.1]) hL.le).mp heq

instance autoAvoidsFiniteLimit_sqrt (a : ℝ) : AutoAvoidsFiniteLimit sqrt a (0 < a) where
  avoids ha := by
    apply avoidsFiniteLimit_of_autoLimit ha
    refine ⟨a, ha, ?_⟩
    intro x hx heq
    exact hx.2.2 ((Real.sqrt_inj (by linarith [hx.1]) ha.le).mp heq)

/-- The zero branch lets the condition solver avoid proving inequalities involving pi. -/
instance autoAvoidsFiniteLimit_compSin (g : ℝ → ℝ) (a : ℝ)
    {L : ℝ} {c d : Prop} [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] :
    AutoAvoidsFiniteLimit (fun x => sin (g x)) a
      ((c ∧ d) ∧ (L = 0 ∨ (-(Real.pi / 2) < L ∧ L < Real.pi / 2))) where
  avoids := by
    rintro ⟨⟨hc, hd⟩, hL⟩
    have hbounds : -(Real.pi / 2) < L ∧ L < Real.pi / 2 := by
      rcases hL with hL | hL
      · subst L
        constructor <;> linarith [Real.pi_pos]
      · exact hL
    obtain ⟨hL, hL'⟩ := hbounds
    apply avoidsFiniteLimit_of_autoLimit hc
    apply locallyAvoids_comp_of_autoLimit hc
      (AutoAvoidsFiniteLimit.avoids hd L (AutoLimit.eq hc))
    refine ⟨min (L + Real.pi / 2) (Real.pi / 2 - L),
      lt_min (by linarith) (by linarith), ?_⟩
    intro y hy heq
    apply Real.strictMonoOn_sin.injOn _ ⟨hL.le, hL'.le⟩ heq
    constructor
    · linarith [hy.1, min_le_left (L + Real.pi / 2) (Real.pi / 2 - L)]
    · linarith [hy.2, min_le_right (L + Real.pi / 2) (Real.pi / 2 - L)]

instance autoAvoidsFiniteLimit_compCos (g : ℝ → ℝ) (a : ℝ)
    {L : ℝ} {c d : Prop} [AutoLimit g a L c] [AutoAvoidsFiniteLimit g a d] :
    AutoAvoidsFiniteLimit (fun x => cos (g x)) a ((c ∧ d) ∧ L = 0) where
  avoids := by
    rintro ⟨⟨hc, hd⟩, hL⟩
    subst L
    apply avoidsFiniteLimit_of_autoLimit hc
    apply locallyAvoids_comp_of_autoLimit hc
      (AutoAvoidsFiniteLimit.avoids hd 0 (AutoLimit.eq hc))
    refine ⟨2 * Real.pi, mul_pos (by norm_num) Real.pi_pos, ?_⟩
    intro y hy heq
    apply (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hy.1])
      (by linarith [hy.2])).mp
    simpa using heq

/-- Sine is injective on its central monotonicity interval. -/
instance autoAvoidsFiniteLimit_sin (a : ℝ) :
    AutoAvoidsFiniteLimit sin a (-(Real.pi / 2) < a ∧ a < Real.pi / 2) where
  avoids := by
    rintro ⟨ha, ha'⟩
    apply avoidsFiniteLimit_of_autoLimit (show True from trivial)
    refine ⟨min (a + Real.pi / 2) (Real.pi / 2 - a),
      lt_min (by linarith) (by linarith), ?_⟩
    intro x hx heq
    apply hx.2.2
    apply Real.strictMonoOn_sin.injOn _ ⟨ha.le, ha'.le⟩ heq
    constructor
    · linarith [hx.1, min_le_left (a + Real.pi / 2) (Real.pi / 2 - a)]
    · linarith [hx.2.1, min_le_right (a + Real.pi / 2) (Real.pi / 2 - a)]

instance autoAvoidsFiniteLimit_sin_zero : AutoAvoidsFiniteLimit sin 0 True where
  avoids _ := autoAvoidsFiniteLimit_sin 0 |>.avoids
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- At zero cosine is not locally injective, but still avoids its limiting value. -/
instance autoAvoidsFiniteLimit_cos_zero : AutoAvoidsFiniteLimit cos 0 True where
  avoids hc := by
    apply avoidsFiniteLimit_of_autoLimit hc
    refine ⟨2 * Real.pi, mul_pos (by norm_num) Real.pi_pos, ?_⟩
    intro x hx heq
    apply hx.2.2
    apply (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hx.1])
      (by linarith [hx.2.1])).mp
    simpa using heq

instance autoAvoidsFiniteLimit_cos_sub_one_zero :
    AutoAvoidsFiniteLimit (fun x => cos x - 1) 0 True where
  avoids hc := by
    apply avoidsFiniteLimit_of_autoLimit (show True ∧ True from ⟨hc, hc⟩)
    obtain ⟨δ, hδ, hne⟩ := autoAvoidsFiniteLimit_cos_zero.avoids hc
      (cos 0) (AutoLimit.eq hc)
    exact ⟨δ, hδ, fun x hx heq => hne x hx (by linarith)⟩

/-- Prove `lim a (f ∘ g) =? Lim (lim a g) f` without rewriting the inner limit.
Infer `g` from the target. Use `lim_subst using h` with
`h : AvoidsFiniteLimit g a` to bypass instances. Unsolved side conditions
remain as goals. This is not an `=` or `=.` rewrite. -/
macro
"lim_subst" "using" h:term
: tactic => `(tactic|
  exact FuncLimitExpr.SubstNested $h
)

macro
"lim_subst"
: tactic => `(tactic| (
  refine FuncLimitExpr.SubstNested ?_
  try (refine AutoAvoidsFiniteLimit.avoids ?_; try auto_side_condition)
))
