/-
    «Calculus_21».Limit.Expr.Init
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr
import «Calculus_21».Limit.Defs
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Limit Expression -/

inductive LimitValue where
| finite : ℝ → LimitValue
| unknown
| posInfty
| negInfty
| unsignedInfty
| divergence

inductive LimitFallbackCore : LimitValue → LimitValue → Prop where
| finite_unknown (a : ℝ) :
    LimitFallbackCore (.finite a) .unknown
| divergence_unknown :
    LimitFallbackCore .divergence .unknown
| infty_divergence :
    LimitFallbackCore .unsignedInfty .divergence
| pos_infty_infty :
    LimitFallbackCore .posInfty .unsignedInfty
| neg_infty_infty :
    LimitFallbackCore .negInfty .unsignedInfty

instance : PolyExpr LimitValue where
  fallbackCore := LimitFallbackCore

instance : ProperClass LimitValue PolyEqual where
  isProper
  | .finite _ => True
  | _         => False
  equal_refl := fun _ => PolyEqual_refl
  eq_of_proper := by
    intro A B h hB
    cases B <;> try contradiction
    rename_i b
    rcases h.cases_tail with rfl | ⟨C, _, hC⟩
    · rfl
    · rcases hC with ⟨hC⟩; cases hC

macro "the" : term => `(LimitValue.finite)
macro "pos_infty" : term => `(LimitValue.posInfty)
macro "neg_infty" : term => `(LimitValue.negInfty)
macro "infty" : term => `(LimitValue.unsignedInfty)
macro "diverg" : term => `(LimitValue.divergence)
macro "unknown" : term => `(LimitValue.unknown)


/-! # Limit expression operations -/

instance : Add LimitValue where
  add A B :=  match A, B with
              | the a, the b => the (a + b)
              | the _, pos_infty => pos_infty
              | the _, neg_infty => neg_infty
              | the _, infty => infty
              | the _, diverg => diverg
              | pos_infty, the _ => pos_infty
              | pos_infty, pos_infty => pos_infty
              | neg_infty, the _ => neg_infty
              | neg_infty, neg_infty => neg_infty
              | infty, the _ => infty
              | diverg, the _ => diverg
              | _, _ => unknown

instance : Neg LimitValue where
  neg A :=  match A with
            | the a => the (-a)
            | pos_infty => neg_infty
            | neg_infty => pos_infty
            | infty => infty
            | diverg => diverg
            | _ => unknown

instance : Sub LimitValue where
  sub A B := A + -B

noncomputable instance : Mul LimitValue where
  mul A B :=  match A, B with
              | the a, the b => the (a * b)
              | the a, pos_infty =>
                  if a > 0 then pos_infty
                  else if a < 0 then neg_infty
                  else unknown
              | the a, neg_infty =>
                  if a > 0 then neg_infty
                  else if a < 0 then pos_infty
                  else unknown
              | the a, infty =>
                  if a ≠ 0 then infty
                  else unknown
              | the a, diverg =>
                  if a ≠ 0 then diverg
                  else unknown
              | pos_infty, the a =>
                  if a > 0 then pos_infty
                  else if a < 0 then neg_infty
                  else unknown
              | pos_infty, pos_infty => pos_infty
              | pos_infty, neg_infty => neg_infty
              | pos_infty, infty => infty
              | neg_infty, the a =>
                  if a > 0 then neg_infty
                  else if a < 0 then pos_infty
                  else unknown
              | neg_infty, pos_infty => neg_infty
              | neg_infty, neg_infty => pos_infty
              | neg_infty, infty => infty
              | infty, the a =>
                  if a ≠ 0 then infty
                  else unknown
              | infty, pos_infty => infty
              | infty, neg_infty => infty
              | infty, infty => infty
              | diverg, the a =>
                  if a ≠ 0 then diverg
                  else unknown
              | _, _ => unknown

noncomputable instance : Inv LimitValue where
  inv A :=  match A with
            | the a =>
                if a ≠ 0 then the a⁻¹
                else infty
            | pos_infty => the 0
            | neg_infty => the 0
            | infty => the 0
            | _ => unknown

noncomputable instance : Div LimitValue where
  div A B := A * B⁻¹

namespace ProperClass

open LimitValue in section

lemma isProper.getEqual {A : LimitValue} :
    isProper A → ∃ a : ℝ, A =. the a := by sorry

end
end ProperClass

instance AutoProperReflect_add_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A + B) target where
  reflect _ := h.reflect <| by cases A <;> cases B <;> trivial

instance AutoProperReflect_add_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A + B) target where
  reflect _ := h.reflect <| by cases A <;> cases B <;> trivial

instance AutoProperReflect_mul_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A * B) target where
  reflect hroot := sorry

instance AutoProperReflect_mul_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A * B) target where
  reflect hroot := sorry

instance AutoProperReflect_neg {A target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (-A) target where
  reflect _ := h.reflect <| by cases A <;> trivial

instance AutoProperReflect_sub_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A - B) target where
  reflect _ := h.reflect <| by cases A <;> cases B <;> trivial

instance AutoProperReflect_sub_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A - B) target where
  reflect _ := h.reflect <| by cases A <;> cases B <;> trivial

instance AutoProperReflect_div_finite {A target : LimitValue} {b : ℝ}
    [h : AutoProperReflect A target] : AutoProperReflect (A / the b) target where
  reflect hroot := sorry

open Classical in
noncomputable instance : Pow LimitValue LimitValue where
  pow A B :=  match A, B with
              | the a, the b =>
                  if a = 0 ∧ b > 0 then the 0
                  else if a > 0 then the (a ^ b)
                  else unknown
              | the a, pos_infty =>
                  if a > 1 then pos_infty
                  else if 0 < a ∧ a < 1 then the 0
                  else unknown
              | the a, neg_infty =>
                  if a > 1 then the 0
                  else if 0 < a ∧ a < 1 then pos_infty
                  else unknown
              | the _, infty => unknown
              | the _, diverg => unknown
              | pos_infty, the b =>
                  if b > 0 then pos_infty
                  else if b < 0 then the 0
                  else unknown
              | pos_infty, pos_infty => pos_infty
              | pos_infty, neg_infty => the 0
              | _, _ => unknown

def genericExpr (C P N U : Prop) (evC : C → ℝ)
    [Decidable C] [Decidable P] [Decidable N] [Decidable U]
    : LimitValue :=
  if h : C then the (evC h)
  else if P then pos_infty
  else if N then neg_infty
  else if U then infty
  else diverg

/-- Logical relationships among the cases classified by `genericExpr`. -/
class GenericExprLaws (C P N U : Prop) where
  finitePred : ℝ → Prop
  evC : C → ℝ
  evC_spec : ∀ hC, finitePred (evC hC)
  finite_exists : ∀ {L}, finitePred L → C
  finite_unique : ∀ {L₁ L₂}, finitePred L₁ → finitePred L₂ → L₁ = L₂
  pos_not_finite : P → ¬ C
  neg_not_finite : N → ¬ C
  infty_not_finite : U → ¬ C
  neg_not_pos : N → ¬ P
  pos_to_infty : P → U
  neg_to_infty : N → U

open Classical in section
noncomputable section

instance (A : Sequence) : GenericExprLaws
    (SeqConverges A)
    (SeqLimitPosInfty A)
    (SeqLimitNegInfty A)
    (SeqLimitInfty A)
:= {
  finitePred := SeqLimit A
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := SeqLimit_Unique
  pos_not_finite := SeqLimitPosInfty.notFinite
  neg_not_finite := SeqLimitNegInfty.notFinite
  infty_not_finite := SeqLimitInfty.notFinite
  neg_not_pos := SeqLimitNegInfty.notPosInfty
  pos_to_infty := SeqLimitPosInfty.toSeqLimitInfty
  neg_to_infty := SeqLimitNegInfty.toSeqLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (FuncConvergesAt F x₀)
    (FuncLimitPosInfty F x₀)
    (FuncLimitNegInfty F x₀)
    (FuncLimitInfty F x₀)
:= {
  finitePred := FuncLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := FuncLimit_Unique
  pos_not_finite := FuncLimitPosInfty.notFinite
  neg_not_finite := FuncLimitNegInfty.notFinite
  infty_not_finite := FuncLimitInfty.notFinite
  neg_not_pos := FuncLimitNegInfty.notPosInfty
  pos_to_infty := FuncLimitPosInfty.toFuncLimitInfty
  neg_to_infty := FuncLimitNegInfty.toFuncLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (LeftConvergesAt F x₀)
    (LeftLimitPosInfty F x₀)
    (LeftLimitNegInfty F x₀)
    (LeftLimitInfty F x₀)
:= {
  finitePred := LeftLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := LeftLimit_Unique
  pos_not_finite := LeftLimitPosInfty.notFinite
  neg_not_finite := LeftLimitNegInfty.notFinite
  infty_not_finite := LeftLimitInfty.notFinite
  neg_not_pos := LeftLimitNegInfty.notPosInfty
  pos_to_infty := LeftLimitPosInfty.toLeftLimitInfty
  neg_to_infty := LeftLimitNegInfty.toLeftLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (RightConvergesAt F x₀)
    (RightLimitPosInfty F x₀)
    (RightLimitNegInfty F x₀)
    (RightLimitInfty F x₀)
:= {
  finitePred := RightLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := RightLimit_Unique
  pos_not_finite := RightLimitPosInfty.notFinite
  neg_not_finite := RightLimitNegInfty.notFinite
  infty_not_finite := RightLimitInfty.notFinite
  neg_not_pos := RightLimitNegInfty.notPosInfty
  pos_to_infty := RightLimitPosInfty.toRightLimitInfty
  neg_to_infty := RightLimitNegInfty.toRightLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtPosInfty F)
    (PosInftyLimitPosInfty F)
    (PosInftyLimitNegInfty F)
    (PosInftyLimitInfty F)
:= {
  finitePred := PosInftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := PosInftyLimit_Unique
  pos_not_finite := PosInftyLimitPosInfty.notFinite
  neg_not_finite := PosInftyLimitNegInfty.notFinite
  infty_not_finite := PosInftyLimitInfty.notFinite
  neg_not_pos := PosInftyLimitNegInfty.notPosInfty
  pos_to_infty := PosInftyLimitPosInfty.toPosInftyLimitInfty
  neg_to_infty := PosInftyLimitNegInfty.toPosInftyLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtNegInfty F)
    (NegInftyLimitPosInfty F)
    (NegInftyLimitNegInfty F)
    (NegInftyLimitInfty F)
:= {
  finitePred := NegInftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := NegInftyLimit_Unique
  pos_not_finite := NegInftyLimitPosInfty.notFinite
  neg_not_finite := NegInftyLimitNegInfty.notFinite
  infty_not_finite := NegInftyLimitInfty.notFinite
  neg_not_pos := NegInftyLimitNegInfty.notPosInfty
  pos_to_infty := NegInftyLimitPosInfty.toNegInftyLimitInfty
  neg_to_infty := NegInftyLimitNegInfty.toNegInftyLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtInfty F)
    (InftyLimitPosInfty F)
    (InftyLimitNegInfty F)
    (InftyLimitInfty F)
:= {
  finitePred := InftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := fun h => ⟨_, h⟩
  finite_unique := InftyLimit_Unique
  pos_not_finite := InftyLimitPosInfty.notFinite
  neg_not_finite := InftyLimitNegInfty.notFinite
  infty_not_finite := InftyLimitInfty.notFinite
  neg_not_pos := InftyLimitNegInfty.notPosInfty
  pos_to_infty := InftyLimitPosInfty.toInftyLimitInfty
  neg_to_infty := InftyLimitNegInfty.toInftyLimitInfty
}

/-- Sequence Limit Expression -/
def SeqLimitExpr (a : ℕ → ℝ) : LimitValue :=
  let A : Sequence := ⟨a, 0, none⟩
  genericExpr (SeqConverges A) (SeqLimitPosInfty A)
    (SeqLimitNegInfty A) (SeqLimitInfty A) GenericExprLaws.evC

/-- Function Limit Expression -/
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (FuncConvergesAt F x₀) (FuncLimitPosInfty F x₀)
    (FuncLimitNegInfty F x₀) (FuncLimitInfty F x₀) GenericExprLaws.evC

/-- (Function's) Left Limit Expression -/
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (LeftConvergesAt F x₀) (LeftLimitPosInfty F x₀)
    (LeftLimitNegInfty F x₀) (LeftLimitInfty F x₀) GenericExprLaws.evC

/-- (Function's) Right Limit Expression -/
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (RightConvergesAt F x₀) (RightLimitPosInfty F x₀)
    (RightLimitNegInfty F x₀) (RightLimitInfty F x₀) GenericExprLaws.evC

/-- (Function's) Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (ConvergesAtNegInfty F) (NegInftyLimitPosInfty F)
    (NegInftyLimitNegInfty F) (NegInftyLimitInfty F) GenericExprLaws.evC

/-- (Function's) Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (ConvergesAtPosInfty F) (PosInftyLimitPosInfty F)
    (PosInftyLimitNegInfty F) (PosInftyLimitInfty F) GenericExprLaws.evC

/-- (Function's) Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : Function := ⟨f, Iii⟩
  genericExpr (ConvergesAtInfty F) (InftyLimitPosInfty F)
    (InftyLimitNegInfty F) (InftyLimitInfty F) GenericExprLaws.evC

end
end

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)
macro "lim" "pos_infty" : term => `(PosInftyLimitExpr)
macro "lim₊∞" : term => `(PosInftyLimitExpr)
macro "lim" "neg_infty" : term => `(NegInftyLimitExpr)
macro "lim₋∞" : term => `(NegInftyLimitExpr)
macro "lim" "infty" : term => `(InftyLimitExpr)
macro "lim∞" : term => `(InftyLimitExpr)


/-! # Classification interfaces -/

namespace LimitValue

lemma finite_div {a b : ℝ} (hb : b ≠ 0)
  : the a / the b =. the (a / b)
:= by
  change the a * (if b ≠ 0 then the b⁻¹ else infty) =. the (a / b)
  rw [if_pos hb]
  rfl

lemma finite_div_zero {a : ℝ} (ha : a ≠ 0)
  : the a / the 0 = infty
:= by
  change the a * (if (0 : ℝ) ≠ 0 then the 0⁻¹ else infty) = infty
  rw [if_neg (not_ne_iff.mpr rfl)]
  change (if a ≠ 0 then infty else unknown) = infty
  rw [if_pos ha]

section
variable {x : LimitValue}

lemma finite_classify {a : ℝ}
  : x =. the a → x = the a
:= by
  intro h
  rcases h.cases_tail with rfl | ⟨y, _, h_xy⟩
  · rfl
  · rcases h_xy with ⟨h_xy⟩
    change LimitFallbackCore y (the a) at h_xy
    cases h_xy

lemma posInfty_classify
  : x =. pos_infty → x = pos_infty
:= by
  intro h
  rcases h.cases_tail with rfl | ⟨y, _, h_xy⟩
  · rfl
  · rcases h_xy with ⟨h_xy⟩
    change LimitFallbackCore y pos_infty at h_xy
    cases h_xy

lemma negInfty_classify
  : x =. neg_infty → x = neg_infty
:= by
  intro h
  rcases h.cases_tail with rfl | ⟨y, _, h_xy⟩
  · rfl
  · rcases h_xy with ⟨h_xy⟩
    change LimitFallbackCore y neg_infty at h_xy
    cases h_xy

lemma unsignedInfty_classify
  : x =. infty → x = pos_infty ∨ x = neg_infty ∨ x = infty
:= by
  intro h
  rcases h.cases_tail with rfl | ⟨y, h, h_xy⟩
  · exact Or.inr (Or.inr rfl)
  · rcases h_xy with ⟨h_xy⟩
    change LimitFallbackCore y infty at h_xy
    cases h_xy with
    | pos_infty_infty => exact Or.inl (posInfty_classify h)
    | neg_infty_infty => exact Or.inr (Or.inl (negInfty_classify h))

lemma divergence_classify
  : x =. diverg → x = pos_infty ∨ x = neg_infty ∨ x = infty ∨ x = diverg
:= by
  intro h
  rcases h.cases_tail with rfl | ⟨y, h, h_xy⟩
  · exact Or.inr (Or.inr (Or.inr rfl))
  · rcases h_xy with ⟨h_xy⟩
    change LimitFallbackCore y diverg at h_xy
    cases h_xy with
    | infty_divergence =>
        rcases unsignedInfty_classify h with hp | hn | hi
        · exact Or.inl hp
        · exact Or.inr (Or.inl hn)
        · exact Or.inr (Or.inr (Or.inl hi))

end

lemma unknown_always
  : ∀ A, A =. unknown
:= by
  intro A
  cases A <;> poly_fallback

end LimitValue
open LimitValue

open Classical in section
variable {C P N U : Prop} {L : ℝ} {evC : C → ℝ}

lemma generic_pos_iff [GenericExprLaws C P N U]
  : genericExpr C P N U evC =. pos_infty ↔ P
:= by
  let laws := (inferInstance : GenericExprLaws C P N U)
  constructor
  · intro h
    have heq := posInfty_classify h
    by_cases hC : C
    · simp [genericExpr, hC] at heq
    · by_cases hP : P
      · exact hP
      · simp [genericExpr, hC, hP] at heq
        split at heq <;> simp_all
        split at heq <;> simp_all
  · intro hP
    simpa [genericExpr, laws.pos_not_finite hP, hP] using
      (by poly_fallback : pos_infty =. pos_infty)

lemma generic_neg_iff [GenericExprLaws C P N U]
  : genericExpr C P N U evC =. neg_infty ↔ N
:= by
  let laws := (inferInstance : GenericExprLaws C P N U)
  constructor
  · intro h
    have heq := negInfty_classify h
    by_cases hC : C
    · simp [genericExpr, hC] at heq
    · by_cases hP : P
      · simp [genericExpr, hC, hP] at heq
      · by_cases hN : N
        · exact hN
        · simp [genericExpr, hC, hP, hN] at heq
          split at heq <;> simp_all
  · intro hN
    simpa [genericExpr, laws.neg_not_finite hN, laws.neg_not_pos hN, hN] using
      (by poly_fallback : neg_infty =. neg_infty)

lemma generic_infty_iff [GenericExprLaws C P N U]
  : genericExpr C P N U evC =. infty ↔ U
:= by
  let laws := (inferInstance : GenericExprLaws C P N U)
  constructor
  · intro h
    rcases unsignedInfty_classify h with heq | heq | heq
    · by_cases hC : C
      · simp [genericExpr, hC] at heq
      · by_cases hP : P
        · exact laws.pos_to_infty hP
        · simp [genericExpr, hC, hP] at heq
          split at heq <;> simp_all
          split at heq <;> simp_all
    · by_cases hC : C
      · simp [genericExpr, hC] at heq
      · by_cases hP : P
        · simp [genericExpr, hC, hP] at heq
        · by_cases hN : N
          · exact laws.neg_to_infty hN
          · simp [genericExpr, hC, hP, hN] at heq
            split at heq <;> simp_all
    · by_cases hC : C
      · simp [genericExpr, hC] at heq
      · by_cases hP : P
        · exact laws.pos_to_infty hP
        · by_cases hN : N
          · exact laws.neg_to_infty hN
          · by_cases hU : U
            · exact hU
            · simp [genericExpr, hC, hP, hN, hU] at heq
  · intro hU
    by_cases hP : P
    · simpa [genericExpr, laws.pos_not_finite hP, hP] using
        (by poly_fallback : pos_infty =. infty)
    · by_cases hN : N
      · simpa [genericExpr, laws.neg_not_finite hN, hP, hN] using
          (by poly_fallback : neg_infty =. infty)
      · simpa [genericExpr, laws.infty_not_finite hU, hP, hN, hU] using
          (by poly_fallback : infty =. infty)

lemma generic_diverg_iff
  : genericExpr C P N U evC =. diverg ↔ ¬ C
:= by
  constructor
  · intro h hC
    rcases divergence_classify h with heq | heq | heq | heq <;>
      simp [genericExpr, hC] at heq
  · intro hC
    by_cases hP : P
    · simpa [genericExpr, hC, hP] using
        (by poly_fallback : pos_infty =. diverg)
    · by_cases hN : N
      · simpa [genericExpr, hC, hP, hN] using
          (by poly_fallback : neg_infty =. diverg)
      · by_cases hU : U
        · simpa [genericExpr, hC, hP, hN, hU] using
            (by poly_fallback : infty =. diverg)
        · simpa [genericExpr, hC, hP, hN, hU] using
            (by poly_fallback : diverg =. diverg)

lemma generic_eq_finite
    (h : genericExpr C P N U evC = the L) : ∃ hC : C, evC hC = L
:= by
  unfold genericExpr at h
  split at h
  · rename_i hC
    exact ⟨hC, LimitValue.finite.inj h⟩
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h <;> contradiction

lemma generic_finite_intro (hC : C) (h_unique : ∀ hC' : C, evC hC' = L)
  : genericExpr C P N U evC =. the L
:= by
  apply ProperClass.equal_of_eq
  simp only [genericExpr, dif_pos hC]
  exact congrArg LimitValue.finite (h_unique hC)

lemma generic_finite_elim
    (h : genericExpr C P N U evC =. the L) : ∃ hC : C, evC hC = L
:= generic_eq_finite (finite_classify h)

end

instance (A : Sequence) : GenericExprLaws
    (SeqConverges A)
    (SeqLimitPosInfty A)
    (SeqLimitNegInfty A)
    (SeqLimitInfty A)
:= {
  pos_not_finite := SeqLimitPosInfty.notFinite
  neg_not_finite := SeqLimitNegInfty.notFinite
  infty_not_finite := SeqLimitInfty.notFinite
  neg_not_pos := SeqLimitNegInfty.notPosInfty
  pos_to_infty := SeqLimitPosInfty.toSeqLimitInfty
  neg_to_infty := SeqLimitNegInfty.toSeqLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (FuncConvergesAt F x₀)
    (FuncLimitPosInfty F x₀)
    (FuncLimitNegInfty F x₀)
    (FuncLimitInfty F x₀)
:= {
  pos_not_finite := FuncLimitPosInfty.notFinite
  neg_not_finite := FuncLimitNegInfty.notFinite
  infty_not_finite := FuncLimitInfty.notFinite
  neg_not_pos := FuncLimitNegInfty.notPosInfty
  pos_to_infty := FuncLimitPosInfty.toFuncLimitInfty
  neg_to_infty := FuncLimitNegInfty.toFuncLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (LeftConvergesAt F x₀)
    (LeftLimitPosInfty F x₀)
    (LeftLimitNegInfty F x₀)
    (LeftLimitInfty F x₀)
:= {
  pos_not_finite := LeftLimitPosInfty.notFinite
  neg_not_finite := LeftLimitNegInfty.notFinite
  infty_not_finite := LeftLimitInfty.notFinite
  neg_not_pos := LeftLimitNegInfty.notPosInfty
  pos_to_infty := LeftLimitPosInfty.toLeftLimitInfty
  neg_to_infty := LeftLimitNegInfty.toLeftLimitInfty
}

instance (F : Function) (x₀ : ℝ) : GenericExprLaws
    (RightConvergesAt F x₀)
    (RightLimitPosInfty F x₀)
    (RightLimitNegInfty F x₀)
    (RightLimitInfty F x₀)
:= {
  pos_not_finite := RightLimitPosInfty.notFinite
  neg_not_finite := RightLimitNegInfty.notFinite
  infty_not_finite := RightLimitInfty.notFinite
  neg_not_pos := RightLimitNegInfty.notPosInfty
  pos_to_infty := RightLimitPosInfty.toRightLimitInfty
  neg_to_infty := RightLimitNegInfty.toRightLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtPosInfty F)
    (PosInftyLimitPosInfty F)
    (PosInftyLimitNegInfty F)
    (PosInftyLimitInfty F)
:= {
  pos_not_finite := PosInftyLimitPosInfty.notFinite
  neg_not_finite := PosInftyLimitNegInfty.notFinite
  infty_not_finite := PosInftyLimitInfty.notFinite
  neg_not_pos := PosInftyLimitNegInfty.notPosInfty
  pos_to_infty := PosInftyLimitPosInfty.toPosInftyLimitInfty
  neg_to_infty := PosInftyLimitNegInfty.toPosInftyLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtNegInfty F)
    (NegInftyLimitPosInfty F)
    (NegInftyLimitNegInfty F)
    (NegInftyLimitInfty F)
:= {
  pos_not_finite := NegInftyLimitPosInfty.notFinite
  neg_not_finite := NegInftyLimitNegInfty.notFinite
  infty_not_finite := NegInftyLimitInfty.notFinite
  neg_not_pos := NegInftyLimitNegInfty.notPosInfty
  pos_to_infty := NegInftyLimitPosInfty.toNegInftyLimitInfty
  neg_to_infty := NegInftyLimitNegInfty.toNegInftyLimitInfty
}

instance (F : Function) : GenericExprLaws
    (ConvergesAtInfty F)
    (InftyLimitPosInfty F)
    (InftyLimitNegInfty F)
    (InftyLimitInfty F)
:= {
  pos_not_finite := InftyLimitPosInfty.notFinite
  neg_not_finite := InftyLimitNegInfty.notFinite
  infty_not_finite := InftyLimitInfty.notFinite
  neg_not_pos := InftyLimitNegInfty.notPosInfty
  pos_to_infty := InftyLimitPosInfty.toInftyLimitInfty
  neg_to_infty := InftyLimitNegInfty.toInftyLimitInfty
}


/-! # Bridges between Limit & Limit Expression -/

open Classical in section
variable {a : ℕ → ℝ} {f : ℝ → ℝ} {x₀ L : ℝ} {init : ℕ} {dom : Set ℝ}

theorem SeqLimit.toSeqLimitExpr
    (h : SeqLimit ⟨a, init, none⟩ L) : limₙ a =. the L
:= by
  apply generic_finite_intro ⟨L, h⟩
  intro hC
  exact SeqLimit_Unique (choose_spec hC) h

theorem SeqLimit.fromSeqLimitExpr
    (h : limₙ a =. the L) : SeqLimit ⟨a, init, none⟩ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact choose_spec hC

theorem FuncLimit.toFuncLimitExpr
    (h : FuncLimit ⟨f, dom⟩ x₀ L) : lim f x₀ =. the L
:= by
  have h_F : FuncLimit ⟨f, Iii⟩ x₀ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact FuncLimit_Unique (choose_spec hC) h_F

theorem FuncLimit.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. the L) :
    FuncLimit ⟨f, dom⟩ x₀ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem LeftLimit.toLeftLimitExpr
    (h : LeftLimit ⟨f, dom⟩ x₀ L) : lim₋ f x₀ =. the L
:= by
  have h_F : LeftLimit ⟨f, Iii⟩ x₀ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact LeftLimit_Unique (choose_spec hC) h_F

theorem LeftLimit.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. the L) :
    LeftLimit ⟨f, dom⟩ x₀ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem RightLimit.toRightLimitExpr
    (h : RightLimit ⟨f, dom⟩ x₀ L) : lim₊ f x₀ =. the L
:= by
  have h_F : RightLimit ⟨f, Iii⟩ x₀ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact RightLimit_Unique (choose_spec hC) h_F

theorem RightLimit.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. the L) :
    RightLimit ⟨f, dom⟩ x₀ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem PosInftyLimit.toPosInftyLimitExpr
    (h : PosInftyLimit ⟨f, dom⟩ L) : lim pos_infty f =. the L
:= by
  have h_F : PosInftyLimit ⟨f, Iii⟩ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact PosInftyLimit_Unique (choose_spec hC) h_F

theorem PosInftyLimit.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. the L) :
    PosInftyLimit ⟨f, dom⟩ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem NegInftyLimit.toNegInftyLimitExpr
    (h : NegInftyLimit ⟨f, dom⟩ L) : lim neg_infty f =. the L
:= by
  have h_F : NegInftyLimit ⟨f, Iii⟩ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact NegInftyLimit_Unique (choose_spec hC) h_F

theorem NegInftyLimit.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. the L) :
    NegInftyLimit ⟨f, dom⟩ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem InftyLimit.toInftyLimitExpr
    (h : InftyLimit ⟨f, dom⟩ L) : lim infty f =. the L
:= by
  have h_F : InftyLimit ⟨f, Iii⟩ L := ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩
  apply generic_finite_intro ⟨L, h_F⟩
  intro hC
  exact InftyLimit_Unique (choose_spec hC) h_F

theorem InftyLimit.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
    (h : lim infty f =. the L) : InftyLimit ⟨f, dom⟩ L
:= by
  rcases generic_finite_elim h with ⟨hC, hL⟩
  rw [← hL]
  exact ⟨h_dom, (choose_spec hC).2⟩

theorem SeqLimitPosInfty.toSeqLimitExpr
    (h : SeqLimitPosInfty ⟨a, init, none⟩) : limₙ a =. pos_infty
:= generic_pos_iff.mpr (h : SeqLimitPosInfty ⟨a, 0, none⟩)

theorem SeqLimitPosInfty.fromSeqLimitExpr
    (h : limₙ a =. pos_infty) : SeqLimitPosInfty ⟨a, init, none⟩
:= (generic_pos_iff.mp h : SeqLimitPosInfty ⟨a, 0, none⟩)

theorem SeqLimitNegInfty.toSeqLimitExpr
    (h : SeqLimitNegInfty ⟨a, init, none⟩) : limₙ a =. neg_infty
:= generic_neg_iff.mpr (h : SeqLimitNegInfty ⟨a, 0, none⟩)

theorem SeqLimitNegInfty.fromSeqLimitExpr
    (h : limₙ a =. neg_infty) : SeqLimitNegInfty ⟨a, init, none⟩
:= (generic_neg_iff.mp h : SeqLimitNegInfty ⟨a, 0, none⟩)

theorem SeqLimitInfty.toSeqLimitExpr
    (h : SeqLimitInfty ⟨a, init, none⟩) : limₙ a =. infty
:= generic_infty_iff.mpr (h : SeqLimitInfty ⟨a, 0, none⟩)

theorem SeqLimitInfty.fromSeqLimitExpr
    (h : limₙ a =. infty) : SeqLimitInfty ⟨a, init, none⟩
:= (generic_infty_iff.mp h : SeqLimitInfty ⟨a, 0, none⟩)

theorem FuncLimitPosInfty.toFuncLimitExpr
    (h : FuncLimitPosInfty ⟨f, dom⟩ x₀) : lim f x₀ =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitPosInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. pos_infty) :
    FuncLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem FuncLimitNegInfty.toFuncLimitExpr
    (h : FuncLimitNegInfty ⟨f, dom⟩ x₀) : lim f x₀ =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitNegInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. neg_infty) :
    FuncLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem FuncLimitInfty.toFuncLimitExpr
    (h : FuncLimitInfty ⟨f, dom⟩ x₀) : lim f x₀ =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. infty) :
    FuncLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem LeftLimitPosInfty.toLeftLimitExpr
    (h : LeftLimitPosInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitPosInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. pos_infty) :
    LeftLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem LeftLimitNegInfty.toLeftLimitExpr
    (h : LeftLimitNegInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitNegInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. neg_infty) :
    LeftLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem LeftLimitInfty.toLeftLimitExpr
    (h : LeftLimitInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. infty) :
    LeftLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem RightLimitPosInfty.toRightLimitExpr
    (h : RightLimitPosInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitPosInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. pos_infty) :
    RightLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem RightLimitNegInfty.toRightLimitExpr
    (h : RightLimitNegInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitNegInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. neg_infty) :
    RightLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem RightLimitInfty.toRightLimitExpr
    (h : RightLimitInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. infty) :
    RightLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem PosInftyLimitPosInfty.toPosInftyLimitExpr
    (h : PosInftyLimitPosInfty ⟨f, dom⟩) : lim pos_infty f =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitPosInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. pos_infty) :
    PosInftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem PosInftyLimitNegInfty.toPosInftyLimitExpr
    (h : PosInftyLimitNegInfty ⟨f, dom⟩) : lim pos_infty f =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitNegInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. neg_infty) :
    PosInftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem PosInftyLimitInfty.toPosInftyLimitExpr
    (h : PosInftyLimitInfty ⟨f, dom⟩) : lim pos_infty f =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. infty) :
    PosInftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem NegInftyLimitPosInfty.toNegInftyLimitExpr
    (h : NegInftyLimitPosInfty ⟨f, dom⟩) : lim neg_infty f =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitPosInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. pos_infty) :
    NegInftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem NegInftyLimitNegInfty.toNegInftyLimitExpr
    (h : NegInftyLimitNegInfty ⟨f, dom⟩) : lim neg_infty f =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitNegInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. neg_infty) :
    NegInftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem NegInftyLimitInfty.toNegInftyLimitExpr
    (h : NegInftyLimitInfty ⟨f, dom⟩) : lim neg_infty f =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. infty) :
    NegInftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem InftyLimitPosInfty.toInftyLimitExpr
    (h : InftyLimitPosInfty ⟨f, dom⟩) : lim infty f =. pos_infty
:= generic_pos_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitPosInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. pos_infty) : InftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_pos_iff.mp h).2⟩

theorem InftyLimitNegInfty.toInftyLimitExpr
    (h : InftyLimitNegInfty ⟨f, dom⟩) : lim infty f =. neg_infty
:= generic_neg_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitNegInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. neg_infty) : InftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_neg_iff.mp h).2⟩

theorem InftyLimitInfty.toInftyLimitExpr
    (h : InftyLimitInfty ⟨f, dom⟩) : lim infty f =. infty
:= generic_infty_iff.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. infty) : InftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, (generic_infty_iff.mp h).2⟩

theorem SeqLimitExpr.ofNotConverges
    (h : ¬ SeqConverges ⟨a, init, none⟩) : limₙ a =. diverg
:= generic_diverg_iff.mpr h

theorem SeqLimitExpr.toNotConverges
    (h : limₙ a =. diverg) : ¬ SeqConverges ⟨a, init, none⟩
:= generic_diverg_iff.mp h

theorem FuncLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
    (h : ¬ FuncConvergesAt ⟨f, dom⟩ x₀) : lim f x₀ =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem FuncLimitExpr.toNotConverges
    (h : lim f x₀ =. diverg) :
    ¬ FuncConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem LeftLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
    (h : ¬ LeftConvergesAt ⟨f, dom⟩ x₀) : lim₋ f x₀ =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem LeftLimitExpr.toNotConverges
    (h : lim₋ f x₀ =. diverg) :
    ¬ LeftConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem RightLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
    (h : ¬ RightConvergesAt ⟨f, dom⟩ x₀) : lim₊ f x₀ =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem RightLimitExpr.toNotConverges
    (h : lim₊ f x₀ =. diverg) :
    ¬ RightConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem PosInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
    (h : ¬ ConvergesAtPosInfty ⟨f, dom⟩) : lim pos_infty f =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem PosInftyLimitExpr.toNotConverges
    (h : lim pos_infty f =. diverg) :
    ¬ ConvergesAtPosInfty ⟨f, dom⟩
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem NegInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
    (h : ¬ ConvergesAtNegInfty ⟨f, dom⟩) : lim neg_infty f =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem NegInftyLimitExpr.toNotConverges
    (h : lim neg_infty f =. diverg) :
    ¬ ConvergesAtNegInfty ⟨f, dom⟩
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem InftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
    (h : ¬ ConvergesAtInfty ⟨f, dom⟩) : lim infty f =. diverg
:= by
  apply generic_diverg_iff.mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem InftyLimitExpr.toNotConverges
    (h : lim infty f =. diverg) : ¬ ConvergesAtInfty ⟨f, dom⟩
:= by
  intro hC
  apply generic_diverg_iff.mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

end


page_end
