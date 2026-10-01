import Calculus_21.Function.CountableZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option linter.style.header false

/-- Synthesize a sufficient condition, rather than asserting that every elementary
function has countably many zeros (constants, differences and sqrt need not). -/
class AutoCountableZeros (f : ℝ → ℝ) (cond : outParam Prop) where
  countable : cond → Function.CountableZeros f

private instance (priority := low) zeros_of_ne {f : ℝ → ℝ} :
    AutoCountableZeros f (∀ x, f x ≠ 0) := ⟨Function.CountableZeros.of_ne⟩

private instance zeros_constant {k : ℝ} : AutoCountableZeros (fun _ ↦ k) (k ≠ 0) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun _ => h)⟩

private instance zeros_const {k : ℝ} : AutoCountableZeros (const k) (k ≠ 0) := zeros_constant

private instance zeros_id : AutoCountableZeros (id : ℝ → ℝ) True :=
  ⟨fun _ => Function.CountableZeros.of_injective Function.injective_id⟩

private instance zeros_identity : AutoCountableZeros (fun x : ℝ ↦ x) True := zeros_id

private instance zeros_add_const {k : ℝ} : AutoCountableZeros (k + ·) True :=
  ⟨fun _ => Function.CountableZeros.of_injective (fun _ _ h => add_left_cancel h)⟩

private instance zeros_sub_const {k : ℝ} : AutoCountableZeros (k - ·) True :=
  ⟨fun _ => Function.CountableZeros.of_injective (fun _ _ h => sub_right_injective h)⟩

private instance zeros_neg {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ -f x) c := ⟨fun h => (AutoCountableZeros.countable h).neg⟩

private instance zeros_neg' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (-f) c := zeros_neg

private instance zeros_inv {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ (f x)⁻¹) c := ⟨fun h => (AutoCountableZeros.countable h).inv⟩

private instance zeros_inv' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros f⁻¹ c := zeros_inv

private instance zeros_mul {f g : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoCountableZeros f c₁] [AutoCountableZeros g c₂] :
    AutoCountableZeros (fun x ↦ f x * g x) (c₁ ∧ c₂) :=
  ⟨fun h => (AutoCountableZeros.countable h.1).mul (AutoCountableZeros.countable h.2)⟩

private instance zeros_mul' {f g : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoCountableZeros f c₁] [AutoCountableZeros g c₂] :
    AutoCountableZeros (f * g) (c₁ ∧ c₂) := zeros_mul

private instance zeros_smul {f : ℝ → ℝ} {k : ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (k • f) (k ≠ 0 ∧ c) := zeros_mul

private instance zeros_div {f g : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoCountableZeros f c₁] [AutoCountableZeros g c₂] :
    AutoCountableZeros (fun x ↦ f x / g x) (c₁ ∧ c₂) :=
  ⟨fun h => (AutoCountableZeros.countable h.1).div (AutoCountableZeros.countable h.2)⟩

private instance zeros_div' {f g : ℝ → ℝ} {c₁ c₂ : Prop}
    [AutoCountableZeros f c₁] [AutoCountableZeros g c₂] :
    AutoCountableZeros (f / g) (c₁ ∧ c₂) := zeros_div

private instance zeros_abs {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ |f x|) c := ⟨fun h => (AutoCountableZeros.countable h).abs⟩

private instance zeros_abs' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (abs ∘ f) c := zeros_abs

private instance zeros_abs_basic : AutoCountableZeros abs True := zeros_abs (f := id)

private instance zeros_natPow {f : ℝ → ℝ} {n : ℕ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ f x ^ n) c :=
  ⟨fun h => (AutoCountableZeros.countable h).natPow n⟩

private instance zeros_natPow' {f : ℝ → ℝ} {n : ℕ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros ((· ^ n) ∘ f) c := zeros_natPow

private instance zeros_natPow_basic {n : ℕ} : AutoCountableZeros (fun x : ℝ ↦ x ^ n) True :=
  zeros_natPow (f := id)

private instance zeros_intPow {f : ℝ → ℝ} {n : ℤ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ f x ^ n) c where
  countable h := (AutoCountableZeros.countable h).mono (fun _ hx => by
    by_contra hn
    exact (zpow_ne_zero _ hn) hx)

private instance zeros_intPow' {f : ℝ → ℝ} {n : ℤ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros ((· ^ n) ∘ f) c := zeros_intPow

private instance zeros_intPow_basic {n : ℤ} : AutoCountableZeros (fun x : ℝ ↦ x ^ n) True :=
  zeros_intPow (f := id)

private instance zeros_npow {n : ℤ} : AutoCountableZeros (npow n) True := zeros_intPow_basic

private instance zeros_compNpow {f : ℝ → ℝ} {n : ℤ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (npow n ∘ f) c := zeros_intPow

private instance zeros_exp {f : ℝ → ℝ} : AutoCountableZeros (fun x ↦ exp (f x)) True :=
  ⟨fun _ => Function.CountableZeros.of_ne (fun _ => Real.exp_ne_zero _)⟩

private instance zeros_exp' {f : ℝ → ℝ} : AutoCountableZeros (exp ∘ f) True := zeros_exp
private instance zeros_exp_basic : AutoCountableZeros exp True := zeros_exp (f := id)

private instance zeros_cosh {f : ℝ → ℝ} : AutoCountableZeros (fun x ↦ cosh (f x)) True :=
  ⟨fun _ => Function.CountableZeros.of_ne (fun _ => ne_of_gt (Real.cosh_pos _))⟩

private instance zeros_cosh' {f : ℝ → ℝ} : AutoCountableZeros (cosh ∘ f) True := zeros_cosh
private instance zeros_cosh_basic : AutoCountableZeros cosh True := zeros_cosh (f := id)

private instance zeros_sinh {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ sinh (f x)) c where
  countable h := by
    simpa only [Function.CountableZeros, Real.sinh_eq_zero] using
      AutoCountableZeros.countable (f := f) h

private instance zeros_sinh' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (sinh ∘ f) c := zeros_sinh
private instance zeros_sinh_basic : AutoCountableZeros sinh True := zeros_sinh (f := id)

private instance zeros_tanh {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ tanh (f x)) c where
  countable h := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (AutoCountableZeros.countable (f := fun x ↦ sinh (f x)) h).div
        (AutoCountableZeros.countable (f := fun x ↦ cosh (f x)) trivial)

private instance zeros_tanh' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (tanh ∘ f) c := zeros_tanh
private instance zeros_tanh_basic : AutoCountableZeros tanh True := zeros_tanh (f := id)

private instance zeros_sech {f : ℝ → ℝ} : AutoCountableZeros (fun x ↦ sech (f x)) True where
  countable _ := by
    simpa only [sech, one_div] using
      (AutoCountableZeros.countable (f := fun x ↦ cosh (f x)) trivial).inv

private instance zeros_sech' {f : ℝ → ℝ} : AutoCountableZeros (sech ∘ f) True := zeros_sech
private instance zeros_sech_basic : AutoCountableZeros sech True := zeros_sech (f := id)

private instance zeros_csch {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ csch (f x)) c where
  countable h := by
    simpa only [csch, one_div] using
      (AutoCountableZeros.countable (f := fun x ↦ sinh (f x)) h).inv

private instance zeros_csch' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (csch ∘ f) c := zeros_csch
private instance zeros_csch_basic : AutoCountableZeros csch True := zeros_csch (f := id)

private instance zeros_coth {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ coth (f x)) c where
  countable h := by
    simpa only [coth, one_div] using
      (AutoCountableZeros.countable (f := fun x ↦ tanh (f x)) h).inv

private instance zeros_coth' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (coth ∘ f) c := zeros_coth
private instance zeros_coth_basic : AutoCountableZeros coth True := zeros_coth (f := id)

private instance zeros_sin_basic : AutoCountableZeros sin True where
  countable _ := (Set.countable_range (fun n : ℤ ↦ (n : ℝ) * Real.pi)).mono (by
    intro x hx
    exact Real.sin_eq_zero_iff.mp hx)

private instance zeros_cos_basic : AutoCountableZeros cos True where
  countable _ := (Set.countable_range (fun n : ℤ ↦ (2 * (n : ℝ) + 1) * Real.pi / 2)).mono (by
    intro x hx
    obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp hx
    exact ⟨n, hn.symm⟩)

private instance zeros_tan_basic : AutoCountableZeros tan True where
  countable _ := by
    simpa only [Function.CountableZeros, Real.tan_eq_sin_div_cos] using
      (zeros_sin_basic.countable trivial).div (zeros_cos_basic.countable trivial)

private instance zeros_cot_basic : AutoCountableZeros cot True where
  countable _ := by
    simpa only [Function.CountableZeros, Real.cot_eq_cos_div_sin] using
      (zeros_cos_basic.countable trivial).div (zeros_sin_basic.countable trivial)

private instance zeros_sec_basic : AutoCountableZeros sec True where
  countable _ := by
    simpa only [Function.CountableZeros, sec, one_div] using (zeros_cos_basic.countable trivial).inv

private instance zeros_csc_basic : AutoCountableZeros csc True where
  countable _ := by
    simpa only [Function.CountableZeros, csc, one_div] using (zeros_sin_basic.countable trivial).inv

/- A countable zero set in the outer variable does not suffice for composition.
Injectivity is a sufficient, explicit preimage condition for these rules. -/
private theorem zeros_comp_of_injective {f g : ℝ → ℝ}
    (hf : Function.CountableZeros f) (hg : Function.Injective g) :
    Function.CountableZeros (f ∘ g) := hf.preimage hg

private instance zeros_sin {f : ℝ → ℝ} :
    AutoCountableZeros (sin ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_sin_basic.countable trivial)⟩
private instance zeros_sin' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ sin (f x)) (Function.Injective f) := zeros_sin

private instance zeros_cos {f : ℝ → ℝ} :
    AutoCountableZeros (cos ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_cos_basic.countable trivial)⟩
private instance zeros_cos' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ cos (f x)) (Function.Injective f) := zeros_cos

private instance zeros_tan {f : ℝ → ℝ} :
    AutoCountableZeros (tan ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_tan_basic.countable trivial)⟩
private instance zeros_tan' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ tan (f x)) (Function.Injective f) := zeros_tan

private instance zeros_cot {f : ℝ → ℝ} :
    AutoCountableZeros (cot ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_cot_basic.countable trivial)⟩
private instance zeros_cot' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ cot (f x)) (Function.Injective f) := zeros_cot

private instance zeros_sec {f : ℝ → ℝ} :
    AutoCountableZeros (sec ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_sec_basic.countable trivial)⟩
private instance zeros_sec' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ sec (f x)) (Function.Injective f) := zeros_sec

private instance zeros_csc {f : ℝ → ℝ} :
    AutoCountableZeros (csc ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_csc_basic.countable trivial)⟩
private instance zeros_csc' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ csc (f x)) (Function.Injective f) := zeros_csc

lemma autoCountableZeros {f : ℝ → ℝ} {cond : Prop} [AutoCountableZeros f cond]
    (h : cond) : Function.CountableZeros f := AutoCountableZeros.countable h

private instance zeros_ln_basic : AutoCountableZeros ln True where
  countable _ := by
    simpa only [Function.CountableZeros, ln, Real.log_eq_zero, Set.setOf_or,
      Set.setOf_eq_eq_singleton] using
      (Set.countable_singleton (0 : ℝ)).union
        ((Set.countable_singleton (1 : ℝ)).union (Set.countable_singleton (-1 : ℝ)))

private instance zeros_ln {f : ℝ → ℝ} :
    AutoCountableZeros (ln ∘ f) (Function.Injective f) :=
  ⟨zeros_comp_of_injective (zeros_ln_basic.countable trivial)⟩
private instance zeros_ln' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ ln (f x)) (Function.Injective f) := zeros_ln

private instance zeros_log_basic {a : ℝ} : AutoCountableZeros (log a) (ln a ≠ 0) where
  countable h := by
    simpa only [Function.CountableZeros, log, ln] using
      (zeros_ln_basic.countable trivial).div
        (Function.CountableZeros.of_ne (fun _ => h))

private instance zeros_log {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros (log a ∘ f) (ln a ≠ 0 ∧ Function.Injective f) :=
  ⟨fun h => zeros_comp_of_injective (zeros_log_basic.countable h.1) h.2⟩
private instance zeros_log' {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ log a (f x)) (ln a ≠ 0 ∧ Function.Injective f) := zeros_log

-- sqrt is zero on the entire negative half-line; positivity is necessary for
-- this sufficient rule, unlike abs or integer powers.
private instance zeros_sqrt {f : ℝ → ℝ} :
    AutoCountableZeros (sqrt ∘ f) (∀ x, 0 < f x) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun x => ne_of_gt (Real.sqrt_pos.mpr (h x)))⟩
private instance zeros_sqrt' {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ √(f x)) (∀ x, 0 < f x) := zeros_sqrt

private instance zeros_rpow {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ f x ^ a) (∀ x, 0 < f x) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun x => ne_of_gt (Real.rpow_pos_of_pos (h x) a))⟩
private instance zeros_rpow' {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros ((· ^ a) ∘ f) (∀ x, 0 < f x) := zeros_rpow
private instance zeros_compPow {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros (pow a ∘ f) (∀ x, 0 < f x) := zeros_rpow

private instance zeros_expow {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ a ^ f x) (0 < a) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun x => ne_of_gt (Real.rpow_pos_of_pos h (f x)))⟩
private instance zeros_expow' {a : ℝ} {f : ℝ → ℝ} :
    AutoCountableZeros ((a ^ ·) ∘ f) (0 < a) := zeros_expow
private instance zeros_expow_basic {a : ℝ} : AutoCountableZeros (a ^ ·) (0 < a) :=
  zeros_expow (f := id)

private instance zeros_arcsin {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ arcsin (f x)) c where
  countable h := by
    simpa only [Function.CountableZeros, Real.arcsin_eq_zero_iff] using
      AutoCountableZeros.countable (f := f) h
private instance zeros_arcsin' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (arcsin ∘ f) c := zeros_arcsin
private instance zeros_arcsin_basic : AutoCountableZeros arcsin True := zeros_arcsin (f := id)

private instance zeros_arctan {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ arctan (f x)) c where
  countable h := by
    simpa only [Function.CountableZeros, Real.arctan_eq_zero_iff] using
      AutoCountableZeros.countable (f := f) h
private instance zeros_arctan' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (arctan ∘ f) c := zeros_arctan
private instance zeros_arctan_basic : AutoCountableZeros arctan True := zeros_arctan (f := id)

private instance zeros_arccot {f : ℝ → ℝ} : AutoCountableZeros (fun x ↦ arccot (f x)) True :=
  ⟨fun _ => Function.CountableZeros.of_ne (fun x => by
    exact ne_of_gt (sub_pos.mpr (Real.arctan_lt_pi_div_two (f x))))⟩
private instance zeros_arccot' {f : ℝ → ℝ} : AutoCountableZeros (arccot ∘ f) True := zeros_arccot
private instance zeros_arccot_basic : AutoCountableZeros arccot True := zeros_arccot (f := id)

private instance zeros_arccsc {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (fun x ↦ arccsc (f x)) c where
  countable h := by
    simpa only [Function.CountableZeros, arccsc, Real.arcsin_eq_zero_iff, inv_eq_zero] using
      AutoCountableZeros.countable (f := f) h
private instance zeros_arccsc' {f : ℝ → ℝ} {c : Prop} [AutoCountableZeros f c] :
    AutoCountableZeros (arccsc ∘ f) c := zeros_arccsc
private instance zeros_arccsc_basic : AutoCountableZeros arccsc True := zeros_arccsc (f := id)

-- arccos vanishes on [1, ∞); arcsec vanishes on (0, 1]. They must not
-- receive unconditional countability instances under the totalized definitions.
private instance zeros_arccos {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ arccos (f x)) (∀ x, f x < 1) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun x => ne_of_gt (Real.arccos_pos.mpr (h x)))⟩
private instance zeros_arccos' {f : ℝ → ℝ} :
    AutoCountableZeros (arccos ∘ f) (∀ x, f x < 1) := zeros_arccos
private instance zeros_arcsec {f : ℝ → ℝ} :
    AutoCountableZeros (fun x ↦ arcsec (f x)) (∀ x, (f x)⁻¹ < 1) :=
  ⟨fun h => Function.CountableZeros.of_ne (fun x => ne_of_gt (Real.arccos_pos.mpr (h x)))⟩
private instance zeros_arcsec' {f : ℝ → ℝ} :
    AutoCountableZeros (arcsec ∘ f) (∀ x, (f x)⁻¹ < 1) := zeros_arcsec

/-- Prove countability by structural synthesis; leave unsolved sufficient
conditions visible. In particular this never assumes a sum is nonzero. -/
macro "countable_zeros" : tactic => `(tactic|
  solve
  | apply autoCountableZeros
    try auto_side_condition
    all_goals try (solve
      | simp only [ln, Real.log_ne_zero]; auto_side_condition
      | norm_cast; first | omega | (auto_side_condition; done))
    all_goals try (solve | intro x; try dsimp; auto_side_condition)
    all_goals try (solve | intro x; nlinarith [sq_nonneg x])
    all_goals try auto_side_condition
)
