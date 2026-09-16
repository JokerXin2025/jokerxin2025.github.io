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

namespace LimitValue

/-- Concrete mathematical outcomes represented by `LimitValue`.
    Unlike `LimitValue`, this type has no information-loss constructor. -/
inductive Outcome where
| finite : ℝ → Outcome
| posInfty
| negInfty
| otherDivergence

def Outcome.toAbstract : Outcome → LimitValue
| .finite a => .finite a
| .posInfty => .posInfty
| .negInfty => .negInfty
| .otherDivergence => .divergence

/-- Information precision, directed from a more precise result to a fallback. -/
def precision : LimitValue → LimitValue → Prop
| .finite a, .finite b => a = b
| .finite _, .unknown => True
| .posInfty, .posInfty => True
| .posInfty, .unsignedInfty => True
| .posInfty, .divergence => True
| .posInfty, .unknown => True
| .negInfty, .negInfty => True
| .negInfty, .unsignedInfty => True
| .negInfty, .divergence => True
| .negInfty, .unknown => True
| .unsignedInfty, .unsignedInfty => True
| .unsignedInfty, .divergence => True
| .unsignedInfty, .unknown => True
| .divergence, .divergence => True
| .divergence, .unknown => True
| .unknown, .unknown => True
| _, _ => False

/-- Concrete outcomes admitted by an abstract limit value. -/
def gamma : LimitValue → Set Outcome
| .finite a => {Outcome.finite a}
| .posInfty => {Outcome.posInfty}
| .negInfty => {Outcome.negInfty}
| .unsignedInfty => {Outcome.posInfty, Outcome.negInfty}
| .divergence => {Outcome.posInfty, Outcome.negInfty, Outcome.otherDivergence}
| .unknown => Set.univ

theorem mem_gamma_iff {o : Outcome} {A : LimitValue} :
    o ∈ gamma A ↔ precision o.toAbstract A := by
  cases o <;> cases A <;> simp [gamma, precision, Outcome.toAbstract]

@[simp] def isProper : LimitValue → Prop
| .finite _ => True
| _ => False

private theorem precision_refl (A : LimitValue) : precision A A := by
  cases A <;> simp [precision]

private theorem precision_trans {A B C : LimitValue} :
    precision A B → precision B C → precision A C := by
  cases A <;> cases B <;> cases C <;> simp_all [precision]

instance : Expr.Precision LimitValue where
  le := precision
  refl := precision_refl
  trans := precision_trans

private theorem gamma_mono {A B : LimitValue} (h : precision A B) :
    gamma A ⊆ gamma B := by
  cases A <;> cases B <;> simp_all [precision, gamma]

instance : Expr.Concretization LimitValue Outcome where
  gamma := gamma
  mono := gamma_mono

private theorem fallback_precision {A B : LimitValue} :
    LimitFallbackCore A B → precision A B := by
  intro h
  cases h <;> trivial

theorem polyEqual_to_precision {A B : LimitValue} (h : A =. B) :
    precision A B := by
  induction h with
  | refl => exact precision_refl A
  | tail _ h ih =>
      rcases h with ⟨h⟩
      exact precision_trans ih (fallback_precision h)

theorem precision_to_polyEqual {A B : LimitValue} (h : precision A B) :
    A =. B := by
  cases A <;> cases B <;> simp_all only [precision] <;> poly_fallback

private theorem proper_singleton {A : LimitValue} :
    isProper A → ∃ c, gamma A = {c} := by
  cases A <;> simp [LimitValue.isProper, gamma]

private theorem proper_rigid {A B : LimitValue} :
    precision A B → isProper B → A = B := by
  cases A <;> cases B <;> simp_all [precision, LimitValue.isProper]

instance : Expr.ProperDomain LimitValue Outcome where
  isProper := isProper
  singleton := proper_singleton
  rigid := proper_rigid

end LimitValue

instance : ProperClass LimitValue PolyEqual where
  isProper := LimitValue.isProper
  equal_refl := fun _ => PolyEqual_refl
  eq_of_proper h hB := Expr.ProperDomain.eq_of_le
    (LimitValue.polyEqual_to_precision h) hB

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
    isProper A → ∃ a : ℝ, A =. the a := by
  intro h
  cases A <;> try { exact ⟨_, PolyEqual_refl⟩ } <;>
    change False at h <;> contradiction

end
end ProperClass

namespace LimitValue

open Expr

/-- Necessary input shapes for inversion to return a proper value. -/
def InvProperPre : LimitValue → Prop
| the _ => True
| pos_infty => True
| neg_infty => True
| infty => True
| _ => False

private instance : ProperBackwardUnary (fun A : LimitValue => A⁻¹) where
  pre := InvProperPre
  necessary := by
    intro A h
    change LimitValue.isProper A⁻¹ at h
    cases A <;> simp_all [InvProperPre, Inv.inv, LimitValue.isProper]

theorem isProper_inv {A : LimitValue} (h : ProperClass.isProper A⁻¹) :
    InvProperPre A :=
  ProperBackward.unary (op := fun X : LimitValue => X⁻¹) h

private instance : ProperBackwardBinary (fun A B : LimitValue => A + B) where
  pre A B := isProper A ∧ isProper B
  necessary := by
    intro A B h
    change LimitValue.isProper (A + B) at h
    cases A <;> cases B <;> simp_all [LimitValue.isProper]

private noncomputable instance :
    ProperBackwardBinary (fun A B : LimitValue => A * B) where
  pre A B := isProper A ∧ isProper B
  necessary := by
    intro A B h
    change LimitValue.isProper (A * B) at h
    cases A <;> cases B <;>
      simp only [HMul.hMul, Mul.mul, LimitValue.isProper] at h ⊢
    all_goals try exact ⟨trivial, trivial⟩
    all_goals exfalso
    all_goals by_cases hp : 0 < ‹ℝ›
    all_goals by_cases hn : ‹ℝ› < 0
    all_goals by_cases hz : ‹ℝ› = 0
    all_goals simp_all

private instance : ProperBackwardUnary (fun A : LimitValue => -A) where
  pre A := isProper A
  necessary := by
    intro A h
    change LimitValue.isProper (-A) at h
    cases A <;> simp_all [LimitValue.isProper]

private instance : ProperBackwardBinary (fun A B : LimitValue => A - B) where
  pre A B := isProper A ∧ isProper B
  necessary := by
    intro A B h
    change LimitValue.isProper (A - B) at h
    cases A <;> cases B <;> simp_all [LimitValue.isProper]

private theorem isProper_add {A B : LimitValue} (h : ProperClass.isProper (A + B)) :
    ProperClass.isProper A ∧ ProperClass.isProper B :=
  ProperBackward.binary (op := fun X Y : LimitValue => X + Y) h

private theorem isProper_mul {A B : LimitValue} (h : ProperClass.isProper (A * B)) :
    ProperClass.isProper A ∧ ProperClass.isProper B :=
  ProperBackward.binary (op := fun X Y : LimitValue => X * Y) h

private theorem isProper_neg {A : LimitValue} (h : ProperClass.isProper (-A)) :
    ProperClass.isProper A :=
  ProperBackward.unary (op := fun X : LimitValue => -X) h

private theorem isProper_sub {A B : LimitValue} (h : ProperClass.isProper (A - B)) :
    ProperClass.isProper A ∧ ProperClass.isProper B :=
  ProperBackward.binary (op := fun X Y : LimitValue => X - Y) h

private theorem isProper_inv_finite {b : ℝ}
    (h : ProperClass.isProper (the b)⁻¹) : b ≠ 0 := by
  intro hb
  subst b
  change LimitValue.isProper (the 0)⁻¹ at h
  simp [Inv.inv, LimitValue.isProper] at h

private noncomputable instance properBackward_div_finite (b : ℝ) :
    ProperBackwardUnary (fun A : LimitValue => A / the b) where
  pre A := isProper A ∧ b ≠ 0
  necessary := by
    intro A h
    change LimitValue.isProper (A / the b) at h
    change LimitValue.isProper (A * (the b)⁻¹) at h
    have hm := isProper_mul h
    exact ⟨hm.1, isProper_inv_finite hm.2⟩

private theorem isProper_div_finite {A : LimitValue} {b : ℝ}
    (h : ProperClass.isProper (A / the b)) :
    ProperClass.isProper A ∧ b ≠ 0 :=
  ProperBackward.unary (op := fun X : LimitValue => X / the b) h

end LimitValue

namespace ProperClass

theorem isProper_div_finite {A : LimitValue} {b : ℝ}
    (h : isProper (A / the b)) : isProper A ∧ b ≠ 0 :=
  LimitValue.isProper_div_finite h

end ProperClass

instance AutoProperReflect_add_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A + B) target where
  reflect hroot := h.reflect (LimitValue.isProper_add hroot).1

instance AutoProperReflect_add_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A + B) target where
  reflect hroot := h.reflect (LimitValue.isProper_add hroot).2

instance AutoProperReflect_mul_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A * B) target where
  reflect hroot := h.reflect (LimitValue.isProper_mul hroot).1

instance AutoProperReflect_mul_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A * B) target where
  reflect hroot := h.reflect (LimitValue.isProper_mul hroot).2

instance AutoProperReflect_neg {A target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (-A) target where
  reflect hroot := h.reflect (LimitValue.isProper_neg hroot)

instance AutoProperReflect_sub_left {A B target : LimitValue}
    [h : AutoProperReflect A target] : AutoProperReflect (A - B) target where
  reflect hroot := h.reflect (LimitValue.isProper_sub hroot).1

instance AutoProperReflect_sub_right {A B target : LimitValue}
    [h : AutoProperReflect B target] : AutoProperReflect (A - B) target where
  reflect hroot := h.reflect (LimitValue.isProper_sub hroot).2

instance AutoProperReflect_div_finite {A target : LimitValue} {b : ℝ}
    [h : AutoProperReflect A target] : AutoProperReflect (A / the b) target where
  reflect hroot := h.reflect (LimitValue.isProper_div_finite hroot).1

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

namespace LimitValue.Outcome

/-- Relational concrete addition. Indeterminate forms may admit several outcomes. -/
def Add : Outcome → Outcome → Outcome → Prop
| .finite a, .finite b, .finite c => c = a + b
| .finite _, .posInfty, .posInfty
| .posInfty, .finite _, .posInfty
| .posInfty, .posInfty, .posInfty => True
| .finite _, .negInfty, .negInfty
| .negInfty, .finite _, .negInfty
| .negInfty, .negInfty, .negInfty => True
| .finite _, .otherDivergence, .otherDivergence
| .otherDivergence, .finite _, .otherDivergence => True
| .posInfty, .negInfty, _
| .negInfty, .posInfty, _
| .posInfty, .otherDivergence, _
| .otherDivergence, .posInfty, _
| .negInfty, .otherDivergence, _
| .otherDivergence, .negInfty, _
| .otherDivergence, .otherDivergence, _ => True
| _, _, _ => False

/-- Relational concrete negation. -/
def Neg : Outcome → Outcome → Prop
| .finite a, .finite b => b = -a
| .posInfty, .negInfty
| .negInfty, .posInfty
| .otherDivergence, .otherDivergence => True
| _, _ => False

/-- Relational concrete subtraction. -/
def Sub (x y z : Outcome) : Prop :=
  ∃ ny, Neg y ny ∧ Add x ny z

/-- Relational concrete multiplication. Indeterminate forms may admit several outcomes. -/
def Mul : Outcome → Outcome → Outcome → Prop
| .finite a, .finite b, .finite c => c = a * b
| .finite a, .posInfty, z
| .posInfty, .finite a, z =>
    if a > 0 then z = .posInfty
    else if a < 0 then z = .negInfty
    else True
| .finite a, .negInfty, z
| .negInfty, .finite a, z =>
    if a > 0 then z = .negInfty
    else if a < 0 then z = .posInfty
    else True
| .finite a, .otherDivergence, z
| .otherDivergence, .finite a, z => if a = 0 then True else z = .otherDivergence
| .posInfty, .posInfty, .posInfty
| .negInfty, .negInfty, .posInfty
| .posInfty, .negInfty, .negInfty
| .negInfty, .posInfty, .negInfty => True
| .posInfty, .otherDivergence, _
| .otherDivergence, .posInfty, _
| .negInfty, .otherDivergence, _
| .otherDivergence, .negInfty, _
| .otherDivergence, .otherDivergence, _ => True
| _, _, _ => False

/-- Relational concrete inversion. -/
def Inv : Outcome → Outcome → Prop
| .finite a, y => if a = 0 then y = .posInfty ∨ y = .negInfty else y = .finite a⁻¹
| .posInfty, .finite b
| .negInfty, .finite b => b = 0
| .otherDivergence, _ => True
| _, _ => False

/-- Relational concrete division. -/
def Div (x y z : Outcome) : Prop :=
  ∃ iy, Inv y iy ∧ Mul x iy z

/-- Relational concrete real-power computation. -/
def Pow : Outcome → Outcome → Outcome → Prop
| .finite a, .finite b, z =>
    if a = 0 ∧ b > 0 then z = .finite 0
    else if a > 0 then z = .finite (a ^ b)
    else True
| .finite a, .posInfty, z =>
    if a > 1 then z = .posInfty
    else if 0 < a ∧ a < 1 then z = .finite 0
    else True
| .finite a, .negInfty, z =>
    if a > 1 then z = .finite 0
    else if 0 < a ∧ a < 1 then z = .posInfty
    else True
| .posInfty, .finite b, z =>
    if b > 0 then z = .posInfty
    else if b < 0 then z = .finite 0
    else True
| .posInfty, .posInfty, .posInfty => True
| .posInfty, .negInfty, z => z = .finite 0
| _, _, _ => True

end LimitValue.Outcome

namespace LimitValue

open Expr

/-- Necessary conditions for real-power abstraction to return a proper value. -/
def PowProperPre : LimitValue → LimitValue → Prop
| the a, the b => (a = 0 ∧ b > 0) ∨ a > 0
| the a, pos_infty => 0 < a ∧ a < 1
| the a, neg_infty => a > 1
| pos_infty, the b => b < 0
| pos_infty, neg_infty => True
| _, _ => False

private noncomputable instance :
    ProperBackwardBinary (fun A B : LimitValue => A ^ B) where
  pre := PowProperPre
  necessary := by
    intro A B h
    change LimitValue.isProper (A ^ B) at h
    cases A <;> cases B <;>
      simp only [HPow.hPow, Pow.pow, PowProperPre] at h ⊢
    all_goals try split_ifs at h with h₁ h₂
    all_goals simp_all

theorem isProper_pow {A B : LimitValue} (h : ProperClass.isProper (A ^ B)) :
    PowProperPre A B :=
  ProperBackward.binary (op := fun X Y : LimitValue => X ^ Y) h

end LimitValue

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

open Classical in noncomputable def genericExprOf
    (C P N U : Prop) [laws : GenericExprLaws C P N U] : LimitValue :=
  genericExpr C P N U laws.evC

open Classical in section
noncomputable section

instance (A : RSequence) : GenericExprLaws
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

instance (F : RFunction) (x₀ : ℝ) : GenericExprLaws
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

instance (F : RFunction) (x₀ : ℝ) : GenericExprLaws
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

instance (F : RFunction) (x₀ : ℝ) : GenericExprLaws
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

instance (F : RFunction) : GenericExprLaws
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

instance (F : RFunction) : GenericExprLaws
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

instance (F : RFunction) : GenericExprLaws
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
  let A : RSequence := ⟨a, 0, none⟩
  genericExprOf (SeqConverges A) (SeqLimitPosInfty A)
    (SeqLimitNegInfty A) (SeqLimitInfty A)

/-- Function Limit Expression -/
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (FuncConvergesAt F x₀) (FuncLimitPosInfty F x₀)
    (FuncLimitNegInfty F x₀) (FuncLimitInfty F x₀)

/-- (Function's) Left Limit Expression -/
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (LeftConvergesAt F x₀) (LeftLimitPosInfty F x₀)
    (LeftLimitNegInfty F x₀) (LeftLimitInfty F x₀)

/-- (Function's) Right Limit Expression -/
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (RightConvergesAt F x₀) (RightLimitPosInfty F x₀)
    (RightLimitNegInfty F x₀) (RightLimitInfty F x₀)

/-- (Function's) Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (ConvergesAtNegInfty F) (NegInftyLimitPosInfty F)
    (NegInftyLimitNegInfty F) (NegInftyLimitInfty F)

/-- (Function's) Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (ConvergesAtPosInfty F) (PosInftyLimitPosInfty F)
    (PosInftyLimitNegInfty F) (PosInftyLimitInfty F)

/-- (Function's) Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  genericExprOf (ConvergesAtInfty F) (InftyLimitPosInfty F)
    (InftyLimitNegInfty F) (InftyLimitInfty F)

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

private lemma finite_classify {a : ℝ}
  : x =. the a → x = the a
:= fun h => Expr.ProperDomain.eq_of_le
  (polyEqual_to_precision h) trivial

private lemma posInfty_classify
  : x =. pos_infty → x = pos_infty
:= by
  intro h
  have hp := polyEqual_to_precision h
  cases x <;> simp_all [precision]

private lemma negInfty_classify
  : x =. neg_infty → x = neg_infty
:= by
  intro h
  have hp := polyEqual_to_precision h
  cases x <;> simp_all [precision]

private lemma unsignedInfty_classify
  : x =. infty → x = pos_infty ∨ x = neg_infty ∨ x = infty
:= by
  intro h
  have hp := polyEqual_to_precision h
  cases x <;> simp_all [precision]

private lemma divergence_classify
  : x =. diverg → x = pos_infty ∨ x = neg_infty ∨ x = infty ∨ x = diverg
:= by
  intro h
  have hp := polyEqual_to_precision h
  cases x <;> simp_all [precision]

end

lemma unknown_always
  : ∀ A, A =. unknown
:= by
  intro A
  cases A <;> poly_fallback

end LimitValue
open LimitValue

open Classical in section
variable {C P N U : Prop} {L : ℝ}

/-- Semantic meaning of asking whether a generic computation proves an observation. -/
def GenericExprSem (C P N U : Prop) [laws : GenericExprLaws C P N U] :
    LimitValue → Prop
| the L => laws.finitePred L
| pos_infty => P
| neg_infty => N
| infty => U
| diverg => ¬ C
| unknown => True

/-- A single specification theorem for all observations of `genericExprOf`. -/
theorem genericExprOf_spec [laws : GenericExprLaws C P N U] {A : LimitValue} :
    genericExprOf C P N U =. A ↔ GenericExprSem C P N U A := by
  cases A with
  | finite L =>
      constructor
      · intro h
        have heq := finite_classify h
        unfold genericExprOf at heq
        unfold genericExpr at heq
        split at heq
        · rename_i hC
          rw [← LimitValue.finite.inj heq]
          exact laws.evC_spec hC
        · split at heq
          · contradiction
          · split at heq
            · contradiction
            · split at heq <;> contradiction
      · intro hL
        let hC := laws.finite_exists hL
        apply ProperClass.equal_of_eq
        simp only [genericExprOf, genericExpr, dif_pos hC]
        exact congrArg LimitValue.finite
          (laws.finite_unique (laws.evC_spec hC) hL)
  | «unknown» => exact ⟨fun _ => trivial, fun _ => unknown_always _⟩
  | posInfty =>
      unfold GenericExprSem
      constructor
      · intro h
        have heq := posInfty_classify h
        by_cases hC : C
        · simp [genericExprOf, genericExpr, hC] at heq
        · by_cases hP : P
          · exact hP
          · simp [genericExprOf, genericExpr, hC, hP] at heq
            split at heq <;> simp_all
            split at heq <;> simp_all
      · intro hP
        simpa [genericExprOf, genericExpr, laws.pos_not_finite hP, hP] using
          (by poly_fallback : pos_infty =. pos_infty)
  | negInfty =>
      unfold GenericExprSem
      constructor
      · intro h
        have heq := negInfty_classify h
        by_cases hC : C
        · simp [genericExprOf, genericExpr, hC] at heq
        · by_cases hP : P
          · simp [genericExprOf, genericExpr, hC, hP] at heq
          · by_cases hN : N
            · exact hN
            · simp [genericExprOf, genericExpr, hC, hP, hN] at heq
              split at heq <;> simp_all
      · intro hN
        simpa [genericExprOf, genericExpr, laws.neg_not_finite hN,
          laws.neg_not_pos hN, hN] using
          (by poly_fallback : neg_infty =. neg_infty)
  | unsignedInfty =>
      unfold GenericExprSem
      constructor
      · intro h
        rcases unsignedInfty_classify h with heq | heq | heq
        · by_cases hC : C
          · simp [genericExprOf, genericExpr, hC] at heq
          · by_cases hP : P
            · exact laws.pos_to_infty hP
            · simp [genericExprOf, genericExpr, hC, hP] at heq
              split at heq <;> simp_all
              split at heq <;> simp_all
        · by_cases hC : C
          · simp [genericExprOf, genericExpr, hC] at heq
          · by_cases hP : P
            · simp [genericExprOf, genericExpr, hC, hP] at heq
            · by_cases hN : N
              · exact laws.neg_to_infty hN
              · simp [genericExprOf, genericExpr, hC, hP, hN] at heq
                split at heq <;> simp_all
        · by_cases hC : C
          · simp [genericExprOf, genericExpr, hC] at heq
          · by_cases hP : P
            · exact laws.pos_to_infty hP
            · by_cases hN : N
              · exact laws.neg_to_infty hN
              · by_cases hU : U
                · exact hU
                · simp [genericExprOf, genericExpr, hC, hP, hN, hU] at heq
      · intro hU
        by_cases hP : P
        · simpa [genericExprOf, genericExpr, laws.pos_not_finite hP, hP] using
            (by poly_fallback : pos_infty =. infty)
        · by_cases hN : N
          · simpa [genericExprOf, genericExpr, laws.neg_not_finite hN, hP, hN] using
              (by poly_fallback : neg_infty =. infty)
          · simpa [genericExprOf, genericExpr, laws.infty_not_finite hU, hP, hN,
              hU] using (by poly_fallback : infty =. infty)
  | divergence =>
      unfold GenericExprSem
      constructor
      · intro h hC
        rcases divergence_classify h with heq | heq | heq | heq <;>
          simp [genericExprOf, genericExpr, hC] at heq
      · intro hC
        by_cases hP : P
        · simpa [genericExprOf, genericExpr, hC, hP] using
            (by poly_fallback : pos_infty =. diverg)
        · by_cases hN : N
          · simpa [genericExprOf, genericExpr, hC, hP, hN] using
              (by poly_fallback : neg_infty =. diverg)
          · by_cases hU : U
            · simpa [genericExprOf, genericExpr, hC, hP, hN, hU] using
                (by poly_fallback : infty =. diverg)
            · simpa [genericExprOf, genericExpr, hC, hP, hN, hU] using
                (by poly_fallback : diverg =. diverg)

end


/-! # Semantic specifications of limit evaluators -/

open Classical in section
noncomputable section

def SeqLimitExprSem (a : ℕ → ℝ) : LimitValue → Prop :=
  let A : RSequence := ⟨a, 0, none⟩
  fun
  | the L => SeqLimit A L
  | pos_infty => SeqLimitPosInfty A
  | neg_infty => SeqLimitNegInfty A
  | infty => SeqLimitInfty A
  | diverg => ¬ SeqConverges A
  | unknown => True

def FuncLimitExprSem (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => FuncLimit F x₀ L
  | pos_infty => FuncLimitPosInfty F x₀
  | neg_infty => FuncLimitNegInfty F x₀
  | infty => FuncLimitInfty F x₀
  | diverg => ¬ FuncConvergesAt F x₀
  | unknown => True

def LeftLimitExprSem (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => LeftLimit F x₀ L
  | pos_infty => LeftLimitPosInfty F x₀
  | neg_infty => LeftLimitNegInfty F x₀
  | infty => LeftLimitInfty F x₀
  | diverg => ¬ LeftConvergesAt F x₀
  | unknown => True

def RightLimitExprSem (f : ℝ → ℝ) (x₀ : ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => RightLimit F x₀ L
  | pos_infty => RightLimitPosInfty F x₀
  | neg_infty => RightLimitNegInfty F x₀
  | infty => RightLimitInfty F x₀
  | diverg => ¬ RightConvergesAt F x₀
  | unknown => True

def PosInftyLimitExprSem (f : ℝ → ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => PosInftyLimit F L
  | pos_infty => PosInftyLimitPosInfty F
  | neg_infty => PosInftyLimitNegInfty F
  | infty => PosInftyLimitInfty F
  | diverg => ¬ ConvergesAtPosInfty F
  | unknown => True

def NegInftyLimitExprSem (f : ℝ → ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => NegInftyLimit F L
  | pos_infty => NegInftyLimitPosInfty F
  | neg_infty => NegInftyLimitNegInfty F
  | infty => NegInftyLimitInfty F
  | diverg => ¬ ConvergesAtNegInfty F
  | unknown => True

def InftyLimitExprSem (f : ℝ → ℝ) : LimitValue → Prop :=
  let F : RFunction := ⟨f, Iii⟩
  fun
  | the L => InftyLimit F L
  | pos_infty => InftyLimitPosInfty F
  | neg_infty => InftyLimitNegInfty F
  | infty => InftyLimitInfty F
  | diverg => ¬ ConvergesAtInfty F
  | unknown => True

theorem SeqLimitExpr_spec (a : ℕ → ℝ) (A : LimitValue)
  : limₙ a =. A ↔ SeqLimitExprSem a A
:= by
  cases A <;> simp only [SeqLimitExpr, SeqLimitExprSem] <;> exact genericExprOf_spec

theorem FuncLimitExpr_spec (f : ℝ → ℝ) (x₀ : ℝ) (A : LimitValue)
  : lim f x₀ =. A ↔ FuncLimitExprSem f x₀ A
:= by
  cases A <;> simp only [FuncLimitExpr, FuncLimitExprSem] <;> exact genericExprOf_spec

theorem LeftLimitExpr_spec (f : ℝ → ℝ) (x₀ : ℝ) (A : LimitValue)
  : lim₋ f x₀ =. A ↔ LeftLimitExprSem f x₀ A
:= by
  cases A <;> simp only [LeftLimitExpr, LeftLimitExprSem] <;> exact genericExprOf_spec

theorem RightLimitExpr_spec (f : ℝ → ℝ) (x₀ : ℝ) (A : LimitValue)
  : lim₊ f x₀ =. A ↔ RightLimitExprSem f x₀ A
:= by
  cases A <;> simp only [RightLimitExpr, RightLimitExprSem] <;> exact genericExprOf_spec

theorem PosInftyLimitExpr_spec (f : ℝ → ℝ) (A : LimitValue)
  : lim pos_infty f =. A ↔ PosInftyLimitExprSem f A
:= by
  cases A <;> simp only [PosInftyLimitExpr, PosInftyLimitExprSem] <;> exact genericExprOf_spec

theorem NegInftyLimitExpr_spec (f : ℝ → ℝ) (A : LimitValue)
  : lim neg_infty f =. A ↔ NegInftyLimitExprSem f A
:= by
  cases A <;> simp only [NegInftyLimitExpr, NegInftyLimitExprSem] <;> exact genericExprOf_spec

theorem InftyLimitExpr_spec (f : ℝ → ℝ) (A : LimitValue)
  : lim infty f =. A ↔ InftyLimitExprSem f A
:= by
  cases A <;> simp only [InftyLimitExpr, InftyLimitExprSem] <;> exact genericExprOf_spec

end
end


/-! # Bridges between Limit & Limit Expression -/

open Classical in section
variable {a : ℕ → ℝ} {f : ℝ → ℝ} {x₀ L : ℝ} {init : ℕ} {dom : Set ℝ}

theorem SeqLimit.toSeqLimitExpr
    (h : SeqLimit ⟨a, init, none⟩ L) : limₙ a =. the L
:= (SeqLimitExpr_spec a (the L)).mpr (h : SeqLimit ⟨a, 0, none⟩ L)

theorem SeqLimit.fromSeqLimitExpr
    (h : limₙ a =. the L) : SeqLimit ⟨a, init, none⟩ L
:= (SeqLimitExpr_spec a (the L)).mp h

theorem FuncLimit.toFuncLimitExpr
    (h : FuncLimit ⟨f, dom⟩ x₀ L) : lim f x₀ =. the L
:= (FuncLimitExpr_spec f x₀ (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimit.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. the L) :
    FuncLimit ⟨f, dom⟩ x₀ L
:= ⟨h_dom, ((FuncLimitExpr_spec f x₀ (the L)).mp h).2⟩

theorem LeftLimit.toLeftLimitExpr
    (h : LeftLimit ⟨f, dom⟩ x₀ L) : lim₋ f x₀ =. the L
:= (LeftLimitExpr_spec f x₀ (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimit.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. the L) :
    LeftLimit ⟨f, dom⟩ x₀ L
:= ⟨h_dom, ((LeftLimitExpr_spec f x₀ (the L)).mp h).2⟩

theorem RightLimit.toRightLimitExpr
    (h : RightLimit ⟨f, dom⟩ x₀ L) : lim₊ f x₀ =. the L
:= (RightLimitExpr_spec f x₀ (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimit.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. the L) :
    RightLimit ⟨f, dom⟩ x₀ L
:= ⟨h_dom, ((RightLimitExpr_spec f x₀ (the L)).mp h).2⟩

theorem PosInftyLimit.toPosInftyLimitExpr
    (h : PosInftyLimit ⟨f, dom⟩ L) : lim pos_infty f =. the L
:= (PosInftyLimitExpr_spec f (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimit.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. the L) :
    PosInftyLimit ⟨f, dom⟩ L
:= ⟨h_dom, ((PosInftyLimitExpr_spec f (the L)).mp h).2⟩

theorem NegInftyLimit.toNegInftyLimitExpr
    (h : NegInftyLimit ⟨f, dom⟩ L) : lim neg_infty f =. the L
:= (NegInftyLimitExpr_spec f (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimit.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. the L) :
    NegInftyLimit ⟨f, dom⟩ L
:= ⟨h_dom, ((NegInftyLimitExpr_spec f (the L)).mp h).2⟩

theorem InftyLimit.toInftyLimitExpr
    (h : InftyLimit ⟨f, dom⟩ L) : lim infty f =. the L
:= (InftyLimitExpr_spec f (the L)).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimit.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
    (h : lim infty f =. the L) : InftyLimit ⟨f, dom⟩ L
:= ⟨h_dom, ((InftyLimitExpr_spec f (the L)).mp h).2⟩

theorem SeqLimitPosInfty.toSeqLimitExpr
    (h : SeqLimitPosInfty ⟨a, init, none⟩) : limₙ a =. pos_infty
:= (SeqLimitExpr_spec a pos_infty).mpr (h : SeqLimitPosInfty ⟨a, 0, none⟩)

theorem SeqLimitPosInfty.fromSeqLimitExpr
    (h : limₙ a =. pos_infty) : SeqLimitPosInfty ⟨a, init, none⟩
:= (SeqLimitExpr_spec a pos_infty).mp h

theorem SeqLimitNegInfty.toSeqLimitExpr
    (h : SeqLimitNegInfty ⟨a, init, none⟩) : limₙ a =. neg_infty
:= (SeqLimitExpr_spec a neg_infty).mpr (h : SeqLimitNegInfty ⟨a, 0, none⟩)

theorem SeqLimitNegInfty.fromSeqLimitExpr
    (h : limₙ a =. neg_infty) : SeqLimitNegInfty ⟨a, init, none⟩
:= (SeqLimitExpr_spec a neg_infty).mp h

theorem SeqLimitInfty.toSeqLimitExpr
    (h : SeqLimitInfty ⟨a, init, none⟩) : limₙ a =. infty
:= (SeqLimitExpr_spec a infty).mpr (h : SeqLimitInfty ⟨a, 0, none⟩)

theorem SeqLimitInfty.fromSeqLimitExpr
    (h : limₙ a =. infty) : SeqLimitInfty ⟨a, init, none⟩
:= (SeqLimitExpr_spec a infty).mp h

theorem FuncLimitPosInfty.toFuncLimitExpr
    (h : FuncLimitPosInfty ⟨f, dom⟩ x₀) : lim f x₀ =. pos_infty
:= (FuncLimitExpr_spec f x₀ pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitPosInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. pos_infty) :
    FuncLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((FuncLimitExpr_spec f x₀ pos_infty).mp h).2⟩

theorem FuncLimitNegInfty.toFuncLimitExpr
    (h : FuncLimitNegInfty ⟨f, dom⟩ x₀) : lim f x₀ =. neg_infty
:= (FuncLimitExpr_spec f x₀ neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitNegInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. neg_infty) :
    FuncLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((FuncLimitExpr_spec f x₀ neg_infty).mp h).2⟩

theorem FuncLimitInfty.toFuncLimitExpr
    (h : FuncLimitInfty ⟨f, dom⟩ x₀) : lim f x₀ =. infty
:= (FuncLimitExpr_spec f x₀ infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom) (h : lim f x₀ =. infty) :
    FuncLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((FuncLimitExpr_spec f x₀ infty).mp h).2⟩

theorem LeftLimitPosInfty.toLeftLimitExpr
    (h : LeftLimitPosInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. pos_infty
:= (LeftLimitExpr_spec f x₀ pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitPosInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. pos_infty) :
    LeftLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((LeftLimitExpr_spec f x₀ pos_infty).mp h).2⟩

theorem LeftLimitNegInfty.toLeftLimitExpr
    (h : LeftLimitNegInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. neg_infty
:= (LeftLimitExpr_spec f x₀ neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitNegInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. neg_infty) :
    LeftLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((LeftLimitExpr_spec f x₀ neg_infty).mp h).2⟩

theorem LeftLimitInfty.toLeftLimitExpr
    (h : LeftLimitInfty ⟨f, dom⟩ x₀) : lim₋ f x₀ =. infty
:= (LeftLimitExpr_spec f x₀ infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom) (h : lim₋ f x₀ =. infty) :
    LeftLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((LeftLimitExpr_spec f x₀ infty).mp h).2⟩

theorem RightLimitPosInfty.toRightLimitExpr
    (h : RightLimitPosInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. pos_infty
:= (RightLimitExpr_spec f x₀ pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitPosInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. pos_infty) :
    RightLimitPosInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((RightLimitExpr_spec f x₀ pos_infty).mp h).2⟩

theorem RightLimitNegInfty.toRightLimitExpr
    (h : RightLimitNegInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. neg_infty
:= (RightLimitExpr_spec f x₀ neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitNegInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. neg_infty) :
    RightLimitNegInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((RightLimitExpr_spec f x₀ neg_infty).mp h).2⟩

theorem RightLimitInfty.toRightLimitExpr
    (h : RightLimitInfty ⟨f, dom⟩ x₀) : lim₊ f x₀ =. infty
:= (RightLimitExpr_spec f x₀ infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom) (h : lim₊ f x₀ =. infty) :
    RightLimitInfty ⟨f, dom⟩ x₀
:= ⟨h_dom, ((RightLimitExpr_spec f x₀ infty).mp h).2⟩

theorem PosInftyLimitPosInfty.toPosInftyLimitExpr
    (h : PosInftyLimitPosInfty ⟨f, dom⟩) : lim pos_infty f =. pos_infty
:= (PosInftyLimitExpr_spec f pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitPosInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. pos_infty) :
    PosInftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, ((PosInftyLimitExpr_spec f pos_infty).mp h).2⟩

theorem PosInftyLimitNegInfty.toPosInftyLimitExpr
    (h : PosInftyLimitNegInfty ⟨f, dom⟩) : lim pos_infty f =. neg_infty
:= (PosInftyLimitExpr_spec f neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitNegInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. neg_infty) :
    PosInftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, ((PosInftyLimitExpr_spec f neg_infty).mp h).2⟩

theorem PosInftyLimitInfty.toPosInftyLimitExpr
    (h : PosInftyLimitInfty ⟨f, dom⟩) : lim pos_infty f =. infty
:= (PosInftyLimitExpr_spec f infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom) (h : lim pos_infty f =. infty) :
    PosInftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, ((PosInftyLimitExpr_spec f infty).mp h).2⟩

theorem NegInftyLimitPosInfty.toNegInftyLimitExpr
    (h : NegInftyLimitPosInfty ⟨f, dom⟩) : lim neg_infty f =. pos_infty
:= (NegInftyLimitExpr_spec f pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitPosInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. pos_infty) :
    NegInftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, ((NegInftyLimitExpr_spec f pos_infty).mp h).2⟩

theorem NegInftyLimitNegInfty.toNegInftyLimitExpr
    (h : NegInftyLimitNegInfty ⟨f, dom⟩) : lim neg_infty f =. neg_infty
:= (NegInftyLimitExpr_spec f neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitNegInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. neg_infty) :
    NegInftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, ((NegInftyLimitExpr_spec f neg_infty).mp h).2⟩

theorem NegInftyLimitInfty.toNegInftyLimitExpr
    (h : NegInftyLimitInfty ⟨f, dom⟩) : lim neg_infty f =. infty
:= (NegInftyLimitExpr_spec f infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom) (h : lim neg_infty f =. infty) :
    NegInftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, ((NegInftyLimitExpr_spec f infty).mp h).2⟩

theorem InftyLimitPosInfty.toInftyLimitExpr
    (h : InftyLimitPosInfty ⟨f, dom⟩) : lim infty f =. pos_infty
:= (InftyLimitExpr_spec f pos_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitPosInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. pos_infty) : InftyLimitPosInfty ⟨f, dom⟩
:= ⟨h_dom, ((InftyLimitExpr_spec f pos_infty).mp h).2⟩

theorem InftyLimitNegInfty.toInftyLimitExpr
    (h : InftyLimitNegInfty ⟨f, dom⟩) : lim infty f =. neg_infty
:= (InftyLimitExpr_spec f neg_infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitNegInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. neg_infty) : InftyLimitNegInfty ⟨f, dom⟩
:= ⟨h_dom, ((InftyLimitExpr_spec f neg_infty).mp h).2⟩

theorem InftyLimitInfty.toInftyLimitExpr
    (h : InftyLimitInfty ⟨f, dom⟩) : lim infty f =. infty
:= (InftyLimitExpr_spec f infty).mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
    (h : lim infty f =. infty) : InftyLimitInfty ⟨f, dom⟩
:= ⟨h_dom, ((InftyLimitExpr_spec f infty).mp h).2⟩

theorem SeqLimitExpr.ofNotConverges
    (h : ¬ SeqConverges ⟨a, init, none⟩) : limₙ a =. diverg
:= (SeqLimitExpr_spec a diverg).mpr h

theorem SeqLimitExpr.toNotConverges
    (h : limₙ a =. diverg) : ¬ SeqConverges ⟨a, init, none⟩
:= (SeqLimitExpr_spec a diverg).mp h

theorem FuncLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
    (h : ¬ FuncConvergesAt ⟨f, dom⟩ x₀) : lim f x₀ =. diverg
:= by
  apply (FuncLimitExpr_spec f x₀ diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem FuncLimitExpr.toNotConverges
    (h : lim f x₀ =. diverg) :
    ¬ FuncConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply (FuncLimitExpr_spec f x₀ diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem LeftLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
    (h : ¬ LeftConvergesAt ⟨f, dom⟩ x₀) : lim₋ f x₀ =. diverg
:= by
  apply (LeftLimitExpr_spec f x₀ diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem LeftLimitExpr.toNotConverges
    (h : lim₋ f x₀ =. diverg) :
    ¬ LeftConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply (LeftLimitExpr_spec f x₀ diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem RightLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
    (h : ¬ RightConvergesAt ⟨f, dom⟩ x₀) : lim₊ f x₀ =. diverg
:= by
  apply (RightLimitExpr_spec f x₀ diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem RightLimitExpr.toNotConverges
    (h : lim₊ f x₀ =. diverg) :
    ¬ RightConvergesAt ⟨f, dom⟩ x₀
:= by
  intro hC
  apply (RightLimitExpr_spec f x₀ diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem PosInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
    (h : ¬ ConvergesAtPosInfty ⟨f, dom⟩) : lim pos_infty f =. diverg
:= by
  apply (PosInftyLimitExpr_spec f diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem PosInftyLimitExpr.toNotConverges
    (h : lim pos_infty f =. diverg) :
    ¬ ConvergesAtPosInfty ⟨f, dom⟩
:= by
  intro hC
  apply (PosInftyLimitExpr_spec f diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem NegInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
    (h : ¬ ConvergesAtNegInfty ⟨f, dom⟩) : lim neg_infty f =. diverg
:= by
  apply (NegInftyLimitExpr_spec f diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem NegInftyLimitExpr.toNotConverges
    (h : lim neg_infty f =. diverg) :
    ¬ ConvergesAtNegInfty ⟨f, dom⟩
:= by
  intro hC
  apply (NegInftyLimitExpr_spec f diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

theorem InftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
    (h : ¬ ConvergesAtInfty ⟨f, dom⟩) : lim infty f =. diverg
:= by
  apply (InftyLimitExpr_spec f diverg).mpr
  rintro ⟨L, hL⟩
  exact h ⟨L, h_dom, hL.2⟩

theorem InftyLimitExpr.toNotConverges
    (h : lim infty f =. diverg) : ¬ ConvergesAtInfty ⟨f, dom⟩
:= by
  intro hC
  apply (InftyLimitExpr_spec f diverg).mp h
  rcases hC with ⟨L, hL⟩
  exact ⟨L, ⟨1, zero_lt_one, by simp⟩, hL.2⟩

end


page_end
