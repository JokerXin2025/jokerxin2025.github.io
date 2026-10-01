import «Calculus_21».Integral.Expr.Init
import Calculus_21.Function.CountableZeros
import «Calculus_21».Differential.Elementary
import «Calculus_21».Differential.Tactics.Calc


def IndefiniteEquivalent (f g : ℝ → ℝ) : Prop :=
  ∃ A : Set ℝ, A.Countable ∧ ∀ x ∉ A, D (f - g) x =. the 0

namespace IndefiniteEquivalent
variable {k : ℝ} {f g h f' g' : ℝ → ℝ}
local infix:50 "~" => IndefiniteEquivalent

theorem of_sub_const {C : ℝ}
  : (∀ x, f x - g x = C) → f ~ g
:= by
  intro h_diff
  refine ⟨∅, Set.countable_empty, fun x _ => ?_⟩
  have heq : (f - g) = const C := by
    funext t
    exact h_diff t
  rw [heq]
  poly_rw [DerivExpr.Constant]

@[refl]
private theorem refl
  : f ~ f
:= of_sub_const (fun _ => sub_self _)

@[symm]
private theorem symm
  : f ~ g → g ~ f
:= by
  intro h
  obtain ⟨s, hsc, hs⟩ := h
  refine ⟨s, hsc, ?_⟩
  intro x hx
  have heq : (g - f) = - (f - g) := by rw [neg_sub]
  calc
    _  =  D (- (f - g)) x
          := congrArg (D · x) heq
    _  =. - D (f - g) x
          := DerivExpr.Neg
    _  =  the 0
          := by poly_rw [hs x hx]; simp only [LimitValue.finite_neg, neg_zero]

@[trans]
private theorem trans
  : f ~ g → g ~ h → f ~ h
:= by
  intro h₁ h₂
  obtain ⟨s, hsc, hs⟩ := h₁
  obtain ⟨t, htc, ht⟩ := h₂
  refine ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
  have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
  have heq : (fun u ↦ f u - h u) = (f - g) + (g - h) := by
    funext u; simp
  calc
    _  =  D ((f - g) + (g - h)) x
          := congrArg (D · x) heq
    _  =. D (f - g) x + D (g - h) x
          := DerivExpr.Add
    _  =  the 0
          := by poly_rw [hs x hx'.1, ht x hx'.2]; simp

@[gcongr]
private theorem add_gcongr
  : f ~ f' → g ~ g' → f + g ~ f' + g'
:= by
  rintro ⟨s, hsc, hs⟩ ⟨t, htc, ht⟩
  refine ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
  have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
  have heq : (f + g) - (f' + g') = (f - f') + (g - g') := by
    funext u; simp only [Pi.add_apply, Pi.sub_apply]; ring
  calc
    _ = D ((f - f') + (g - g')) x := congrArg (D · x) heq
    _ =. D (f - f') x + D (g - g') x := DerivExpr.Add
    _ = the 0 := by poly_rw [hs x hx'.1, ht x hx'.2]; simp

@[gcongr]
private theorem neg_gcongr
  : f ~ f' → -f ~ -f'
:= by
  rintro ⟨s, hsc, hs⟩
  refine ⟨s, hsc, fun x hx => ?_⟩
  have heq : -f - -f' = -(f - f') := by
    funext u; simp only [Pi.neg_apply, Pi.sub_apply]; ring
  calc
    _ = D (-(f - f')) x := congrArg (D · x) heq
    _ =. -D (f - f') x := DerivExpr.Neg
    _ = the 0 := by poly_rw [hs x hx]; simp

@[gcongr]
private theorem sub_gcongr
  : f ~ f' → g ~ g' → f - g ~ f' - g'
:= by
  intro hf hg
  simpa only [sub_eq_add_neg] using hf.add_gcongr hg.neg_gcongr

@[gcongr]
private theorem smul_gcongr
  : f ~ f' → k • f ~ k • f'
:= by
  rintro ⟨s, hsc, hs⟩
  refine ⟨s, hsc, fun x hx => ?_⟩
  calc
    _ = D (k • (f - f')) x := congrArg (D · x) (smul_sub k f f').symm
    _ =. the k * D (f - f') x := DerivExpr.SMul
    _ = the 0 := by poly_rw [hs x hx]; simp

end IndefiniteEquivalent

inductive IndefiniteValue
| primitive (f : ℝ → ℝ)
| unknown

instance : PolyCalc IndefiniteValue where
  fallbackCore
  | .primitive F, .primitive G => IndefiniteEquivalent F G
  | _, _ => False
  «unknown» := .unknown

macro "prim" : term => `(IndefiniteValue.primitive)

namespace IndefiniteValue

instance : Add IndefiniteValue where
  add
  | prim F, prim G  => prim (F + G)
  | _, _            => .unknown

instance : Neg IndefiniteValue where
  neg
  | prim F    => prim (-F)
  | .unknown  => .unknown

instance : Sub IndefiniteValue where
  sub A A' := A + -A'

/-- Even zero scalar multiplication propagates unknown information. -/
instance : SMul ℝ IndefiniteValue where
  smul k
  | prim F    => prim (k • F)
  | .unknown  => .unknown

lemma primitive_polyEq_iff {F G : ℝ → ℝ}
  : prim F =. prim G ↔ IndefiniteEquivalent F G
:= by
  constructor
  · intro h
    generalize hG : prim G = B at h
    induction h generalizing G with
    | refl =>
      cases hG
      rfl
    | @tail A B _ step ih =>
      cases step with
      | core hc =>
        cases hG
        cases A with
        | primitive H => exact (ih rfl).trans hc
        | «unknown» => exact False.elim hc
      | «unknown» => cases hG
  · exact fun h => PolyCalc.pe_of_fallbackCore h

theorem unknown_not_polyEq_primitive (F : ℝ → ℝ) : ¬ .unknown =. prim F := by
  intro h
  have h_unknown : ∀ {B : IndefiniteValue}, .unknown =. B → B = .unknown := by
    intro B h
    induction h with
    | refl => rfl
    | tail _ step ih =>
      cases step with
      | core hc =>
        subst_vars
        exact False.elim hc
      | «unknown» => rfl
  cases h_unknown h

end IndefiniteValue

namespace IndefiniteValue
variable {k : ℝ} {A A' B B' : IndefiniteValue}

@[gcongr]
private theorem neg_congr
  : A =. A' → -A =. -A'
:= by
  intro h
  cases A <;> cases A'
  all_goals first
  | exact (unknown_not_polyEq_primitive _ h).elim
  | exact PolyCalc.pe_unknown _
  | exact primitive_polyEq_iff.mpr (primitive_polyEq_iff.mp h).neg_gcongr

@[gcongr]
private theorem smul_congr
  : A =. A' → k • A =. k • A'
:= by
  intro h
  cases A <;> cases A'
  all_goals first
  | exact (unknown_not_polyEq_primitive _ h).elim
  | exact PolyCalc.pe_unknown _
  | exact primitive_polyEq_iff.mpr (primitive_polyEq_iff.mp h).smul_gcongr

@[gcongr]
private theorem add_congr
  : A =. A' → B =. B' → A + B =. A' + B'
:= by
  intro h₁ h₂
  cases A <;> cases A' <;> cases B <;> cases B'
  all_goals first
  | exact (unknown_not_polyEq_primitive _ h₁).elim
  | exact (unknown_not_polyEq_primitive _ h₂).elim
  | exact PolyCalc.pe_unknown _
  | exact primitive_polyEq_iff.mpr
          ((primitive_polyEq_iff.mp h₁).add_gcongr (primitive_polyEq_iff.mp h₂))

@[gcongr]
private theorem sub_congr
  : A =. A' → B =. B' → A - B =. A' - B'
:= fun h₁ h₂ => add_congr h₁ (neg_congr h₂)

end IndefiniteValue

open Classical in
noncomputable def IndefiniteExpr (f' : ℝ → ℝ) : IndefiniteValue :=
  if h : ∃ f : ℝ → ℝ, ∃ A : Set ℝ, A.Countable ∧ ∀ x ∉ A, D f x =. the (f' x)
    then prim (choose h)
  else .unknown

macro "∫" : term => `(IndefiniteExpr)

syntax:max atomic("∫" term "d" ident) : term
macro_rules
| `(∫ $body:term d $x:ident) => `(
  IndefiniteExpr (fun $x : ℝ => $body)
)

namespace IndefiniteExpr

open Classical in
theorem spec {f' f : ℝ → ℝ} :
    ∫ f' =. prim f ↔ ∃ A : Set ℝ, A.Countable ∧ ∀ x ∉ A, D f x =. the (f' x)
:= by
  unfold IndefiniteExpr
  split
  · rename_i h
    obtain ⟨s, hsc, hs⟩ := choose_spec h
    rw [IndefiniteValue.primitive_polyEq_iff]
    constructor
    · rintro ⟨t, htc, ht⟩
      refine ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
      have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
      calc
        _ = D (choose h - (choose h - f)) x := congrArg (D · x) (by ring_nf)
        _ =. D (choose h) x - D (choose h - f) x := DerivExpr.Sub
        _ = the (f' x) := by poly_rw [hs x hx'.1]; poly_rw [ht x hx'.2]; simp
    · rintro ⟨t, htc, ht⟩
      refine ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
      have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
      calc
        _ =. D (choose h) x - D f x := DerivExpr.Sub
        _ = the 0 := by poly_rw [hs x hx'.1, ht x hx'.2]; simp
  · rename_i h
    constructor
    · intro hp
      exact (IndefiniteValue.unknown_not_polyEq_primitive f hp).elim
    · intro hs
      exact (h ⟨f, hs⟩).elim

/-- Compatibility with proofs using finitely many exceptions. -/
theorem of_finite {f F : ℝ → ℝ} {s : Finset ℝ}
    (h : ∀ x ∉ s, D F x =. the (f x)) : ∫ f =. prim F :=
  spec.mpr ⟨s, s.countable_toSet, h⟩

/-- A sufficient condition for reciprocal and quotient rules. -/
abbrev CountableZeros := Function.CountableZeros

/-- Composition must control the preimage of actual derivative failures,
not merely the size of the exceptional set in the outer variable. -/
def CountableDerivativePreimage (F f G : ℝ → ℝ) : Prop :=
  {x | ¬ (D F (G x) =. the (f (G x)))}.Countable

theorem countableZeros_of_ne {F : ℝ → ℝ} (h : ∀ x, F x ≠ 0) : CountableZeros F := by
  have he : {x | F x = 0} = ∅ := by ext x; simp [h x]
  simpa only [CountableZeros, Function.CountableZeros, he] using
    (Set.countable_empty : (∅ : Set ℝ).Countable)

theorem countableZeros_of_injective {F : ℝ → ℝ} (h : Function.Injective F) :
    CountableZeros F := (Set.countable_singleton (0 : ℝ)).preimage h

theorem countableDerivativePreimage_of_deriv {F f G : ℝ → ℝ}
    (h : ∀ x, D F (G x) =. the (f (G x))) : CountableDerivativePreimage F f G := by
  have he : {x | ¬ (D F (G x) =. the (f (G x)))} = ∅ := by ext x; simp [h x]
  simpa only [CountableDerivativePreimage, he] using
    (Set.countable_empty : (∅ : Set ℝ).Countable)

theorem countableDerivativePreimage_of_injective {F f G : ℝ → ℝ}
    (hF : ∫ f =. prim F) (hG : Function.Injective G) :
    CountableDerivativePreimage F f G := by
  classical
  obtain ⟨s, hsc, hs⟩ := spec.mp hF
  apply (hsc.preimage hG).mono
  intro x hx
  by_contra hn
  exact hx (hs (G x) hn)

theorem CongrOutside {f g F : ℝ → ℝ} {s : Set ℝ} (hsc : s.Countable)
    (hfg : ∀ x ∉ s, f x = g x) (hg : ∫ g =. prim F) : ∫ f =. prim F := by
  obtain ⟨t, htc, ht⟩ := spec.mp hg
  refine spec.mpr ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
  have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
  rw [hfg x hx'.1]
  exact ht x hx'.2

theorem Inv {f F : ℝ → ℝ} (hF : ∫ f =. prim F) (hzero : CountableZeros F) :
    ∫ (fun x ↦ -f x / F x ^ 2) =. prim (fun x ↦ (F x)⁻¹) := by
  obtain ⟨s, hsc, hs⟩ := spec.mp hF
  refine spec.mpr ⟨s ∪ {x | F x = 0}, hsc.union hzero, fun x hx => ?_⟩
  have hx' : x ∉ s ∧ F x ≠ 0 := by simpa only [Set.mem_union, Set.mem_setOf_eq, not_or] using hx
  have hd : D F x = the (f x) := LimitValue.finite_iff.mp (hs x hx'.1)
  have hz := hx'.2
  have hn : F x ^ 2 ≠ 0 := pow_ne_zero _ hz
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _ =? -D F x / the (F x ^ 2) := DerivExpr.Inv
    _ = the (-f x / F x ^ 2) := by
      rw [hd]
      exact LimitValue.finite_iff.mp (LimitValue.finite_div hn)

theorem Comp {f g F G : ℝ → ℝ} (hG : ∫ g =. prim G)
    (hpre : CountableDerivativePreimage F f G) :
    ∫ (fun x ↦ f (G x) * g x) =. prim (F ∘ G) := by
  classical
  obtain ⟨s, hsc, hs⟩ := spec.mp hG
  refine spec.mpr ⟨s ∪ {x | ¬ (D F (G x) =. the (f (G x)))},
    hsc.union hpre, fun x hx => ?_⟩
  have hx' : x ∉ s ∧ D F (G x) =. the (f (G x)) := by
    simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using hx
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _ =? D F (G x) * D G x := DerivExpr.Comp
    _ = the (f (G x) * g x) := by poly_rw [hx'.2, hs x hx'.1]

theorem Div {f g F G : ℝ → ℝ} (hF : ∫ f =. prim F) (hG : ∫ g =. prim G)
    (hzero : CountableZeros G) :
    ∫ (fun x ↦ (f x * G x - F x * g x) / G x ^ 2) =.
      prim (fun x ↦ F x / G x) := by
  obtain ⟨s, hsc, hs⟩ := spec.mp hF
  obtain ⟨t, htc, ht⟩ := spec.mp hG
  refine spec.mpr ⟨(s ∪ t) ∪ {x | G x = 0}, (hsc.union htc).union hzero,
    fun x hx => ?_⟩
  have hx' : (x ∉ s ∧ x ∉ t) ∧ G x ≠ 0 := by
    simpa only [Set.mem_union, Set.mem_setOf_eq, not_or] using hx
  have hn : G x ^ 2 ≠ 0 := pow_ne_zero _ hx'.2
  apply EqualIfProper.reintroduce (by trivial)
  calc
    _ =? (D F x * the (G x) - D G x * the (F x)) / the (G x ^ 2) := DerivExpr.Div
    _ = the ((f x * G x - F x * g x) / G x ^ 2) := by
      poly_rw [hs x hx'.1.1, ht x hx'.1.2]
      change the (f x * G x - g x * F x) / the (G x ^ 2) =
        the ((f x * G x - F x * g x) / G x ^ 2)
      poly_rw [LimitValue.finite_div hn]
      congr 1
      ring

end IndefiniteExpr

namespace IndefiniteExpr
variable {C k : ℝ} {f g : ℝ → ℝ}

theorem AddConstant
  : prim f =. prim (f · + C)
:= sorry

theorem Neg
  : ∫ (-f) =. - ∫ f
:= by
  cases hf : ∫ f with
  | «unknown» => exact PolyCalc.pe_unknown _
  | primitive F =>
    obtain ⟨s, hsc, hs⟩ := spec.mp (PolyCalc.pe_of_eq hf)
    refine spec.mpr ⟨s, hsc, fun x hx => ?_⟩
    calc
      _ =. -D F x := DerivExpr.Neg
      _ = the ((-f) x) := by poly_rw [hs x hx]

theorem SMul
  : ∫ (k • f) =. k • ∫ f
:= by
  cases hf : ∫ f with
  | «unknown» => exact PolyCalc.pe_unknown _
  | primitive F =>
    obtain ⟨s, hsc, hs⟩ := spec.mp (PolyCalc.pe_of_eq hf)
    refine spec.mpr ⟨s, hsc, fun x hx => ?_⟩
    calc
      _ =. the k * D F x := DerivExpr.SMul
      _ = the ((k • f) x) := by poly_rw [hs x hx]

theorem Add
  : ∫ (f + g) =. ∫ f + ∫ g
:= by
  cases hf : ∫ f with
  | «unknown» => exact PolyCalc.pe_unknown _
  | primitive F =>
    cases hg : ∫ g with
    | «unknown» => exact PolyCalc.pe_unknown _
    | primitive G =>
      obtain ⟨s, hsc, hs⟩ := spec.mp (PolyCalc.pe_of_eq hf)
      obtain ⟨t, htc, ht⟩ := spec.mp (PolyCalc.pe_of_eq hg)
      refine spec.mpr ⟨s ∪ t, hsc.union htc, fun x hx => ?_⟩
      have hx' : x ∉ s ∧ x ∉ t := by simpa only [Set.mem_union, not_or] using hx
      calc
        _ =. D F x + D G x := DerivExpr.Add
        _ = the ((f + g) x) := by poly_rw [hs x hx'.1, ht x hx'.2]

theorem Sub
  : ∫ (f - g) =. ∫ f - ∫ g
:= by
  calc
    _  =  ∫ (f + -g)
          := by rw [sub_eq_add_neg]
    _  =. ∫ f + ∫ (-g)
          := Add
    _  =. ∫ f - ∫ g
          := IndefiniteValue.add_congr (by rfl) Neg

end IndefiniteExpr
