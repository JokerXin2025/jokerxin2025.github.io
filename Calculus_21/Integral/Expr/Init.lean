import «Calculus_21».Integral.Defs
import «Calculus_21».Limit.Expr.Init


open Classical in
noncomputable def IntegralExpr (f : ℝ → ℝ) (a b : ℝ) : LimitValue :=
  if h : (total f).isIntegrableOn a b then the (choose h)
  else unknown

notation "∫" "_[" a "," b "]" => (IntegralExpr · a b)

-- The binder scopes over the body only; both bounds retain their outer scope.
-- Backtrack to the function notation when there is no trailing differential.
syntax:max atomic("∫" "_[" term "," term "]" term "d" ident) : term
macro_rules
| `(∫_[$a,$b] $body:term d $x:ident) => `(
  IntegralExpr (fun $x : ℝ => $body) $a $b
)

section
variable {F : RFunction} {f g : ℝ → ℝ} {a b k : ℝ}

open Classical in
theorem IntegralExpr.finite_iff {value : ℝ}
  : ∫_[a,b] f = the value ↔ DefIntegral (total f) a b value
:= by
  beta_reduce
  unfold IntegralExpr
  split
  · rename_i h
    constructor
    · intro heq
      have hv := LimitValue.finite.inj heq
      exact hv ▸ choose_spec h
    · intro hv
      exact congrArg the ((choose_spec h).unique hv)
  · rename_i h
    constructor
    · intro heq
      cases heq
    · intro hv
      exact (h hv.isIntegrableOn).elim

theorem IntegralExpr.unknown_iff : ∫_[a,b] f = unknown ↔
    ¬ (total f).isIntegrableOn a b
:= by
  beta_reduce
  unfold IntegralExpr
  grind

theorem IntegralExpr.finite_iff_of_domain {value : ℝ}
    (hdom : Integral.interval a b ⊆ F.domain)
  : ∫_[a,b] F.map = the value ↔ DefIntegral F a b value
:= by
  rw [finite_iff]
  exact ⟨fun h => h.congr hdom (fun _ _ => rfl), fun h => h.total⟩

theorem IntegralExpr.emptyInternal
  : ∫_[a,a] f = the 0
:= finite_iff.mpr (DefIntegral.same trivial)

theorem IntegralExpr.Constant
  : ∫_[a,b] (fun _ ↦ k) = the (k * (b - a))
:= finite_iff.mpr (DefIntegral.const k a b)

theorem IntegralExpr.reverseInternal
  : ∫_[b,a] f = - ∫_[a,b] f
:= by
  classical
  by_cases h : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := h
    rw [finite_iff.mpr hv, finite_iff.mpr hv.reverse]
    rfl
  · have hr : ¬ (total f).isIntegrableOn b a := fun hr => h hr.reverse
    rw [unknown_iff.mpr h, unknown_iff.mpr hr]
    rfl

theorem IntegralExpr.SMul
  : ∫_[a,b] (k • f) =. the k * ∫_[a,b] f
:= by
  classical
  by_cases h : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := h
    rw [finite_iff.mpr hv]
    apply PolyCalc.pe_of_eq
    exact finite_iff.mpr (hv.smul k).total
  · rw [unknown_iff.mpr h]
    exact PolyCalc.pe_unknown _

theorem IntegralExpr.Neg
  : ∫_[a,b] (-f) =. - ∫_[a,b] f
:= by
  classical
  by_cases h : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := h
    rw [finite_iff.mpr hv]
    apply PolyCalc.pe_of_eq
    apply finite_iff.mpr
    have hn := (hv.smul (-1)).congr (G := total (-f))
      (fun _ _ => trivial) (fun x _ => by change -1 * f x = -f x; ring)
    simpa only [neg_one_mul] using hn
  · rw [unknown_iff.mpr h]
    exact PolyCalc.pe_unknown _

theorem IntegralExpr.Add
  : ∫_[a,b] (f + g) =. ∫_[a,b] f + ∫_[a,b] g
:= by
  classical
  by_cases hf : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := hf
    rw [finite_iff.mpr hv]
    by_cases hg : (total g).isIntegrableOn a b
    · obtain ⟨w, hw⟩ := hg
      rw [finite_iff.mpr hw]
      exact PolyCalc.pe_of_eq (finite_iff.mpr (hv.add hw).total)
    · rw [unknown_iff.mpr hg]
      exact PolyCalc.pe_unknown _
  · rw [unknown_iff.mpr hf]
    have h : unknown + IntegralExpr g a b = (unknown : LimitValue) := by
      cases IntegralExpr g a b <;> rfl
    rw [h]
    exact PolyCalc.pe_unknown _

theorem IntegralExpr.Sub
  : ∫_[a,b] (f - g) =. ∫_[a,b] f - ∫_[a,b] g
:= by
  classical
  by_cases hf : (total f).isIntegrableOn a b
  · obtain ⟨v, hv⟩ := hf
    rw [finite_iff.mpr hv]
    by_cases hg : (total g).isIntegrableOn a b
    · obtain ⟨w, hw⟩ := hg
      rw [finite_iff.mpr hw]
      apply PolyCalc.pe_of_eq
      apply finite_iff.mpr
      convert (hv.add (hw.smul (-1))).congr (G := total (f - g))
        (fun _ _ => trivial) (fun x _ => by change f x + -1 * g x = f x - g x; ring)
        using 1
      ring
    · rw [unknown_iff.mpr hg]
      exact PolyCalc.pe_unknown _
  · rw [unknown_iff.mpr hf]
    have h : unknown - IntegralExpr g a b = (unknown : LimitValue) := by
      cases IntegralExpr g a b <;> rfl
    rw [h]
    exact PolyCalc.pe_unknown _

theorem Integral.toIntegralExpr {value : ℝ}
  : DefIntegral F a b value → ∫_[a,b] F.map =. the value
:= fun h => LimitValue.finite_iff.mpr (IntegralExpr.finite_iff.mpr h.total)

theorem Integral.fromIntegralExpr {value : ℝ}
    (h_dom : Integral.interval a b ⊆ F.domain)
  : ∫_[a,b] F.map =. the value → DefIntegral F a b value
:= fun h => (IntegralExpr.finite_iff_of_domain h_dom).mp (LimitValue.finite_iff.mp h)

end
