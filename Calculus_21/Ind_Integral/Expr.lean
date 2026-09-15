/-
    «Calculus_21».Ind_Integral.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Differential.Expr
import «Calculus_21».Ind_Integral.Defs
set_option linter.style.header false


/-! # Differ-By-Constant Relation — derivative of difference is 0 a.e. -/

inductive IntegralError where
  | nonIntegrable
  | undefined
  deriving Repr, DecidableEq

instance : ExprError IntegralError where
  divZero := .undefined
  invalidPow := .undefined

/-- Two functions `f, g : ℝ → ℝ` are "equivalent up to a constant" in the sense
    relevant for antiderivatives: the difference `f - g` has derivative zero
    everywhere except on a finite set `S`.

    Formally: `∃ S : Finset ℝ, ∀ x ∉ S, D (f - g) x = the 0`.

    This generalises the classical "differ by a constant" because a function
    whose derivative is 0 a.e. is constant on each connected component.
    The `PrimFunc` quotient uses this relation. -/
def DifferByConst (f g : ℝ → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ x ∉ S, D (f - g) x = the 0

@[refl]
lemma DifferByConst_refl (f : ℝ → ℝ)
  : DifferByConst f f := by
  refine ⟨∅, fun x _ => ?_⟩
  -- D (f - f) x = the 0, i.e. D 0 x = the 0
  sorry

@[symm]
lemma DifferByConst_symm {f g : ℝ → ℝ}
    (h : DifferByConst f g)
  : DifferByConst g f := by
  rcases h with ⟨S, h⟩
  refine ⟨S, fun x h_x => ?_⟩
  -- h x h_x : D (f - g) x = the 0, need D (g - f) x = the 0
  sorry

@[trans]
lemma DifferByConst_trans {f g h : ℝ → ℝ}
    (h₁ : DifferByConst f g) (h₂ : DifferByConst g h)
  : DifferByConst f h := by
  rcases h₁ with ⟨S₁, h₁⟩
  rcases h₂ with ⟨S₂, h₂⟩
  refine ⟨S₁ ∪ S₂, fun x h_x => ?_⟩
  sorry


/-! # Preparations for `PrimFunc` -/

/-- Antiderivatives of the same function on the same domain differ by a function
    whose derivative is 0 almost everywhere (the `DifferByConst` relation). -/
lemma HasAntideriv.differ_by_const {f F G : Function}
    (h_F : HasAntideriv f F) (h_G : HasAntideriv f G)
    (h_dom : F.domain = G.domain)
  : DifferByConst F.map G.map
:= by sorry


/-! # Raw `ℝ → ℝ` convenience wrapper -/

/-- Convenience wrapper: `HasAntiderivRaw f F` =
    `HasAntideriv ⟨f, Iii⟩ ⟨F, Iii⟩`. -/
def HasAntiderivRaw (f F : ℝ → ℝ) : Prop :=
  HasAntideriv ⟨f, Iii⟩ ⟨F, Iii⟩

/-- `f` has an antiderivative (raw ℝ → ℝ version) -/
abbrev isIntegrableRaw (f : ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ, HasAntiderivRaw f F


/-! # Bridges: `HasAntideriv` (Function) ↔ `HasAntiderivRaw` (ℝ → ℝ) -/

theorem HasAntiderivRaw.to_Function {f F : ℝ → ℝ}
    (h : HasAntiderivRaw f F)
  : HasAntideriv ⟨f, Iii⟩ ⟨F, Iii⟩ := h

theorem HasAntideriv.to_Raw {f F : Function}
    (h_dom : F.domain = Iii) (h : HasAntideriv f F)
  : HasAntiderivRaw f.map F.map := by
  intro x
  intro h_xI
  intro d hDeriv
  have h_x : x ∈ F.domain := by rw [h_dom]; exact h_xI
  have hF_eq : ⟨F.map, Iii⟩ = F := by
    apply Function.ext <;> simp [h_dom]
  rw [hF_eq] at hDeriv
  exact h x h_x d hDeriv

theorem HasAntideriv.mono {f F G : Function}
    (h : HasAntideriv f F) (h_map_F : G.map = F.map)
    (h_dom : G.domain ⊆ F.domain)
  : HasAntideriv f G := by
  intro x h_xG d hDerivG
  -- hDerivG : Deriv G x d
  -- h gives: ∀ x ∈ F.domain, ∀ d, Deriv F x d → d = f.map x
  -- Need to connect Deriv G x d and Deriv F x d
  -- Since G.map = F.map and G.domain ⊆ F.domain, Deriv G x d → Deriv F x d
  sorry


/-! # Properties of `HasAntiderivRaw` (ℝ → ℝ version) -/

lemma HasAntiderivRaw.comp_const {f F G : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F) (h_diff : DifferByConst F G)
  : HasAntiderivRaw f G
:= by sorry

lemma HasAntiderivRaw.differ_by_const {f F G : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F) (h_G : HasAntiderivRaw f G)
  : DifferByConst F G
:= by sorry

lemma HasAntiderivRaw.zero {F : ℝ → ℝ}
  : HasAntiderivRaw 0 F ↔ ∃ C : ℝ, ∀ x, F x = C
:= by sorry

lemma HasAntiderivRaw.smul {f F : ℝ → ℝ} {k : ℝ}
    (h_F : HasAntiderivRaw f F)
  : HasAntiderivRaw (k • f) (k • F)
:= by sorry

lemma HasAntiderivRaw.add {f g F G : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F) (h_G : HasAntiderivRaw g G)
  : HasAntiderivRaw (f + g) (F + G)
:= by sorry

lemma HasAntiderivRaw.neg {f F : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F)
  : HasAntiderivRaw (-f) (-F)
:= by sorry

lemma HasAntiderivRaw.sub {f g F G : ℝ → ℝ}
    (h_F : HasAntiderivRaw f F) (h_G : HasAntiderivRaw g G)
  : HasAntiderivRaw (f - g) (F - G)
:= by sorry


/-! # Definition of `PrimFunc` -/

def PrimFunc.Setoid : Setoid (ℝ → ℝ) :=
  ⟨DifferByConst, DifferByConst_refl, DifferByConst_symm, DifferByConst_trans⟩

abbrev PrimFunc := Quotient PrimFunc.Setoid


/-! # Algebraic Operations on PrimFunc -/

instance : Add PrimFunc where
  add := Quotient.map₂ (fun f g x ↦ f x + g x) (by
    rintro f₁ f₂ ⟨S₁, h₁⟩ g₁ g₂ ⟨S₂, h₂⟩
    refine ⟨S₁ ∪ S₂, fun x h_x => ?_⟩
    sorry
  )

instance : Sub PrimFunc where
  sub := Quotient.map₂ (fun f g x ↦ f x - g x) (by
    rintro f₁ f₂ ⟨S₁, h₁⟩ g₁ g₂ ⟨S₂, h₂⟩
    refine ⟨S₁ ∪ S₂, fun x h_x => ?_⟩
    sorry
  )

instance : Neg PrimFunc where
  neg := Quotient.map (fun f x ↦ - f x) (by
    rintro f₁ f₂ ⟨S, h⟩
    refine ⟨S, fun x h_x => ?_⟩
    sorry
  )

instance : HMul ℝ PrimFunc PrimFunc where
  hMul k := Quotient.map (fun f x ↦ k * f x) (by
    rintro f₁ f₂ ⟨S, h⟩
    refine ⟨S, fun x h_x => ?_⟩
    sorry
  )

instance : HMul (Except IntegralError ℝ) (Except IntegralError PrimFunc)
    (Except IntegralError PrimFunc) where
  hMul A B := match A, B with
              | Except.ok a, Except.ok b => Except.ok (a * b)
              | Except.error e, _ => Except.error e
              | _, Except.error e => Except.error e


/-! # Indefinite Integral Expression -/

noncomputable section

open Classical in
/-- Indefinite Integral Expression -/
def IndefIntegralExpr (f : ℝ → ℝ) : Except IntegralError PrimFunc :=
  if h : ∃ F : ℝ → ℝ, HasAntiderivRaw f F then
    the ⟦choose h⟧
   else .error .nonIntegrable

end

macro "∫" : term => `(IndefIntegralExpr)
macro:50 "fun" x:ident "↦" fx:term "+" "C" : term => `(⟦fun $x ↦ $fx⟧)


@[simp]
lemma except_bind_ok {ε α β : Type} (x : α) (f : α → Except ε β)
  : Bind.bind (Except.ok x) f = f x
:= rfl

@[simp]
lemma except_pure_ok {ε α : Type} (x : α)
  : (Pure.pure x : Except ε α) = Except.ok x
:= rfl

@[simp]
lemma addC_val (x : ℝ)
  : (AddC.addC x).val = x
:= rfl

@[simp]
lemma addC_func (f : ℝ → ℝ)
  : (AddC.addC f) = ⟦f⟧
:= rfl


/-! # Bridges between Antideriv & Integral Expression -/

open Classical in
/-- Expression → Relation -/
theorem IndefIntegralExpr_to_HasAntiderivRaw {f F : ℝ → ℝ}
    (h_int : ∫ f = the ⟦F⟧)
  : HasAntiderivRaw f F
:= by sorry

open Classical in
/-- Relation → Expression -/
theorem HasAntiderivRaw_to_IndefIntegralExpr {f F : ℝ → ℝ}
    (h_int : HasAntiderivRaw f F)
  : ∫ f = the ⟦F⟧
:= by sorry

page_end
