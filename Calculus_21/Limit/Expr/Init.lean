/-
    «Calculus_21».Limit.Expr.Init
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».PolyCalc
import «Calculus_21».Limit.Defs
set_option linter.style.header false

open PolyCalc


/-! # Limit Expression's Value -/

inductive LimitValue
| finite (a : ℝ)
| unknownLimit
| posInfty
| negInfty
| unsignedInfty
| divergence

inductive LimitFallbackCore : LimitValue → LimitValue → Prop
| infty_divergence : LimitFallbackCore .unsignedInfty .divergence
| pos_infty_infty : LimitFallbackCore .posInfty .unsignedInfty
| neg_infty_infty : LimitFallbackCore .negInfty .unsignedInfty

instance : PolyCalc LimitValue where
  fallbackCore := LimitFallbackCore
  unknown := .unknownLimit

macro "the" : term => `(LimitValue.finite)
macro "pos_infty" : term => `(LimitValue.posInfty)
macro "neg_infty" : term => `(LimitValue.negInfty)
macro "infty" : term => `(LimitValue.unsignedInfty)
macro "diverg" : term => `(LimitValue.divergence)
macro "unknown" : term => `(LimitValue.unknownLimit)

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

namespace LimitValue
variable {A : LimitValue} {b : ℝ} {cond₁ : Prop}

def isProper : LimitValue → Prop
| .finite _ => True
| _         => False

instance : ProperClass LimitValue where
  isProper := isProper
  rigid A B := by
    intro h hB
    cases B <;> simp only [isProper] at hB
    cases h <;> trivial

lemma isProper.getEqual
  : A.isProper → ∃ a : ℝ, A =. the a
:= by intro h; cases A <;> first | exact ⟨_, by rfl⟩ | contradiction

lemma isProper.getEqual!
  : A.isProper → ∃ a : ℝ, A = the a
:= by intro h; cases A <;> simp [isProper] at h ⊢

private lemma isProper.inv_finite
  : (the b)⁻¹.isProper → b ≠ 0
:= by
  intro h hb
  subst b
  change (the 0)⁻¹.isProper at h
  simp [Inv.inv, isProper] at h

end LimitValue

open Classical in section
noncomputable section
variable {A : RSequence} {F : RFunction} {x₀ : ℝ}

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

instance : GenericExprLaws
    (SeqConverges A)
    (SeqLimitPosInfty A)
    (SeqLimitNegInfty A)
    (SeqLimitInfty A)
:= {
  finitePred := SeqLimit A
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := SeqLimit.unique
  pos_not_finite := SeqLimitPosInfty.notFinite
  neg_not_finite := SeqLimitNegInfty.notFinite
  infty_not_finite := SeqLimitInfty.notFinite
  neg_not_pos := SeqLimitNegInfty.notPosInfty
  pos_to_infty := SeqLimitPosInfty.toSeqLimitInfty
  neg_to_infty := SeqLimitNegInfty.toSeqLimitInfty
}

instance : GenericExprLaws
    (FuncConvergesAt F x₀)
    (FuncLimitPosInfty F x₀)
    (FuncLimitNegInfty F x₀)
    (FuncLimitInfty F x₀)
:= {
  finitePred := FuncLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := FuncLimit.unique
  pos_not_finite := FuncLimitPosInfty.notFinite
  neg_not_finite := FuncLimitNegInfty.notFinite
  infty_not_finite := FuncLimitInfty.notFinite
  neg_not_pos := FuncLimitNegInfty.notPosInfty
  pos_to_infty := FuncLimitPosInfty.toFuncLimitInfty
  neg_to_infty := FuncLimitNegInfty.toFuncLimitInfty
}

instance : GenericExprLaws
    (LeftConvergesAt F x₀)
    (LeftLimitPosInfty F x₀)
    (LeftLimitNegInfty F x₀)
    (LeftLimitInfty F x₀)
:= {
  finitePred := LeftLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := LeftLimit.unique
  pos_not_finite := LeftLimitPosInfty.notFinite
  neg_not_finite := LeftLimitNegInfty.notFinite
  infty_not_finite := LeftLimitInfty.notFinite
  neg_not_pos := LeftLimitNegInfty.notPosInfty
  pos_to_infty := LeftLimitPosInfty.toLeftLimitInfty
  neg_to_infty := LeftLimitNegInfty.toLeftLimitInfty
}

instance : GenericExprLaws
    (RightConvergesAt F x₀)
    (RightLimitPosInfty F x₀)
    (RightLimitNegInfty F x₀)
    (RightLimitInfty F x₀)
:= {
  finitePred := RightLimit F x₀
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := RightLimit.unique
  pos_not_finite := RightLimitPosInfty.notFinite
  neg_not_finite := RightLimitNegInfty.notFinite
  infty_not_finite := RightLimitInfty.notFinite
  neg_not_pos := RightLimitNegInfty.notPosInfty
  pos_to_infty := RightLimitPosInfty.toRightLimitInfty
  neg_to_infty := RightLimitNegInfty.toRightLimitInfty
}

instance : GenericExprLaws
    (ConvergesAtPosInfty F)
    (PosInftyLimitPosInfty F)
    (PosInftyLimitNegInfty F)
    (PosInftyLimitInfty F)
:= {
  finitePred := PosInftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := PosInftyLimit.unique
  pos_not_finite := PosInftyLimitPosInfty.notFinite
  neg_not_finite := PosInftyLimitNegInfty.notFinite
  infty_not_finite := PosInftyLimitInfty.notFinite
  neg_not_pos := PosInftyLimitNegInfty.notPosInfty
  pos_to_infty := PosInftyLimitPosInfty.toPosInftyLimitInfty
  neg_to_infty := PosInftyLimitNegInfty.toPosInftyLimitInfty
}

instance : GenericExprLaws
    (ConvergesAtNegInfty F)
    (NegInftyLimitPosInfty F)
    (NegInftyLimitNegInfty F)
    (NegInftyLimitInfty F)
:= {
  finitePred := NegInftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := NegInftyLimit.unique
  pos_not_finite := NegInftyLimitPosInfty.notFinite
  neg_not_finite := NegInftyLimitNegInfty.notFinite
  infty_not_finite := NegInftyLimitInfty.notFinite
  neg_not_pos := NegInftyLimitNegInfty.notPosInfty
  pos_to_infty := NegInftyLimitPosInfty.toNegInftyLimitInfty
  neg_to_infty := NegInftyLimitNegInfty.toNegInftyLimitInfty
}

instance : GenericExprLaws
    (ConvergesAtInfty F)
    (InftyLimitPosInfty F)
    (InftyLimitNegInfty F)
    (InftyLimitInfty F)
:= {
  finitePred := InftyLimit F
  evC := choose
  evC_spec := choose_spec
  finite_exists := (⟨_, ·⟩)
  finite_unique := InftyLimit.unique
  pos_not_finite := InftyLimitPosInfty.notFinite
  neg_not_finite := InftyLimitNegInfty.notFinite
  infty_not_finite := InftyLimitInfty.notFinite
  neg_not_pos := InftyLimitNegInfty.notPosInfty
  pos_to_infty := InftyLimitPosInfty.toInftyLimitInfty
  neg_to_infty := InftyLimitNegInfty.toInftyLimitInfty
}

def GenericExpr (C P N U : Prop)
    [laws : GenericExprLaws C P N U] : LimitValue :=
  if h : C then the (laws.evC h)
  else if P then pos_infty
  else if N then neg_infty
  else if U then infty
  else diverg

/-- Sequence Limit Expression -/
def SeqLimitExpr (a : ℕ → ℝ) : LimitValue :=
  let A : RSequence := ⟨a, 0, none⟩
  GenericExpr (SeqConverges A)
              (SeqLimitPosInfty A)
              (SeqLimitNegInfty A)
              (SeqLimitInfty A)

/-- Function Limit Expression -/
def FuncLimitExpr (x₀ : ℝ) (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (FuncConvergesAt F x₀)
              (FuncLimitPosInfty F x₀)
              (FuncLimitNegInfty F x₀)
              (FuncLimitInfty F x₀)

/-- (Function's) Left Limit Expression -/
def LeftLimitExpr (x₀ : ℝ) (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (LeftConvergesAt F x₀)
              (LeftLimitPosInfty F x₀)
              (LeftLimitNegInfty F x₀)
              (LeftLimitInfty F x₀)

/-- (Function's) Right Limit Expression -/
def RightLimitExpr (x₀ : ℝ) (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (RightConvergesAt F x₀)
              (RightLimitPosInfty F x₀)
              (RightLimitNegInfty F x₀)
              (RightLimitInfty F x₀)

/-- (Function's) Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (ConvergesAtNegInfty F)
              (NegInftyLimitPosInfty F)
              (NegInftyLimitNegInfty F)
              (NegInftyLimitInfty F)

/-- (Function's) Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (ConvergesAtPosInfty F)
              (PosInftyLimitPosInfty F)
              (PosInftyLimitNegInfty F)
              (PosInftyLimitInfty F)

/-- (Function's) Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : LimitValue :=
  let F : RFunction := ⟨f, Iii⟩
  GenericExpr (ConvergesAtInfty F)
              (InftyLimitPosInfty F)
              (InftyLimitNegInfty F)
              (InftyLimitInfty F)

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


/-! # Limit Expression Utilities -/

namespace LimitValue
variable {A B : LimitValue} {a b : ℝ}

def LessPreciseThan : LimitValue → LimitValue → Prop
  | .finite a, .finite b            => a = b
  | .finite _, .unknownLimit        => True
  | .posInfty, .posInfty            => True
  | .posInfty, .unsignedInfty       => True
  | .posInfty, .divergence          => True
  | .posInfty, .unknownLimit        => True
  | .negInfty, .negInfty            => True
  | .negInfty, .unsignedInfty       => True
  | .negInfty, .divergence          => True
  | .negInfty, .unknownLimit        => True
  | .unsignedInfty, .unsignedInfty  => True
  | .unsignedInfty, .divergence     => True
  | .unsignedInfty, .unknownLimit   => True
  | .divergence, .divergence        => True
  | .divergence, .unknownLimit      => True
  | .unknownLimit, .unknownLimit    => True
  | _, _                            => False

theorem polyEq_iff_lessPreciseThan
  : A =. B ↔ LessPreciseThan A B
:= by
  constructor
  · intro h
    induction h with
    | refl => cases A <;> simp only [LessPreciseThan]
    | tail _ step ih =>
        cases step with
        | core core => cases core <;> cases A <;> simp_all only [LessPreciseThan]
        | «unknown» =>
            change LessPreciseThan A .unknownLimit
            cases A <;> simp only [LessPreciseThan]
  · intro h
    cases A <;> cases B <;> simp only [LessPreciseThan] at h
    all_goals first
    | subst_vars; rfl
    | exact pe_unknown _
    | exact pe_of_fallbackCore .pos_infty_infty
    | exact pe_of_fallbackCore .neg_infty_infty
    | exact pe_of_fallbackCore .infty_divergence
    | calc
        pos_infty  =. infty
                      := pe_of_fallbackCore .pos_infty_infty
        _          =. diverg
                      := pe_of_fallbackCore .infty_divergence
    | calc
        neg_infty  =. infty
                      := pe_of_fallbackCore .neg_infty_infty
        _          =. diverg
                      := pe_of_fallbackCore .infty_divergence

lemma finite_iff
  : A =. the a ↔ A = the a
:= by
  rw [polyEq_iff_lessPreciseThan]
  cases A <;> simp [LessPreciseThan]

@[simp] lemma finite_add {a b : ℝ}
  : the a + the b = the (a + b)
:= rfl

@[simp] lemma finite_neg {a : ℝ}
  : - the a = the (-a)
:= rfl

@[simp] lemma finite_sub {a b : ℝ}
  : the a - the b = the (a - b)
:= rfl

@[simp] lemma finite_mul {a b : ℝ}
  : the a * the b = the (a * b)
:= rfl

lemma finite_div
    (h_b : b ≠ 0)
  : the a / the b =. the (a / b)
:= by
  change the a * (if b ≠ 0 then the b⁻¹ else infty) =. the (a / b)
  rw_pos h_b
  rfl

lemma finite_div_zero
    (h_a : a ≠ 0)
  : the a / the 0 = infty
:= by
  change the a * (if 0 ≠ 0 then the 0⁻¹ else infty) = infty
  rw_neg not_ne_iff.mpr rfl
  change (if a ≠ 0 then infty else unknown) = infty
  rw_pos h_a

end LimitValue


/-! # Bridges between Limit and Limit Expression -/

def GenericExprSem (C P N U : Prop)
    [laws : GenericExprLaws C P N U] : LimitValue → Prop
  | the L     => laws.finitePred L
  | pos_infty => P
  | neg_infty => N
  | infty     => U
  | diverg    => ¬ C
  | unknown   => True

open LimitValue in
theorem GenericExprBridge {C P N U : Prop} {A : LimitValue}
    [laws : GenericExprLaws C P N U]
  : GenericExpr C P N U =. A ↔ GenericExprSem C P N U A
:= by
  rw [polyEq_iff_lessPreciseThan]
  by_cases hC : C
  · have hP : ¬ P := (laws.pos_not_finite · hC)
    have hN : ¬ N := (laws.neg_not_finite · hC)
    have hU : ¬ U := (laws.infty_not_finite · hC)
    have hfinite : ∀ L, laws.finitePred L ↔ laws.evC hC = L := by
      intro _
      constructor
      · exact laws.finite_unique (laws.evC_spec hC)
      · intro h
        rw [← h]
        exact laws.evC_spec hC
    cases A <;> simp [GenericExpr, GenericExprSem, LessPreciseThan,
      hC, hP, hN, hU, hfinite]
  · have hfinite : ∀ L, ¬ laws.finitePred L := by
      intro _ h
      exact hC (laws.finite_exists h)
    by_cases hP : P
    · have hN : ¬ N := (laws.neg_not_pos · hP)
      have hU : U := laws.pos_to_infty hP
      cases A <;> simp [GenericExpr, GenericExprSem, LessPreciseThan,
        hC, hP, hN, hU, hfinite]
    · by_cases hN : N
      · have hU : U := laws.neg_to_infty hN
        cases A <;> simp [GenericExpr, GenericExprSem, LessPreciseThan,
          hC, hP, hN, hU, hfinite]
      · by_cases hU : U
        · cases A <;> simp [GenericExpr, GenericExprSem, LessPreciseThan,
            hC, hP, hN, hU, hfinite]
        · cases A <;> simp [GenericExpr, GenericExprSem, LessPreciseThan,
            hC, hP, hN, hU, hfinite]

open Classical in section
variable {a : ℕ → ℝ} {f : ℝ → ℝ} {x₀ L : ℝ} {init : ℕ} {dom : Set ℝ}

theorem SeqLimit.toSeqLimitExpr
  : SeqLimit ⟨a, init, none⟩ L → limₙ a =. the L
:= fun h => GenericExprBridge.mpr (h : SeqLimit ⟨a, 0, none⟩ L)

theorem SeqLimit.fromSeqLimitExpr
  : limₙ a =. the L → SeqLimit ⟨a, init, none⟩ L
:= fun h => GenericExprBridge.mp h

theorem FuncLimit.toFuncLimitExpr
  : FuncLimit ⟨f, dom⟩ x₀ L → lim x₀ f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimit.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : lim x₀ f =. the L → FuncLimit ⟨f, dom⟩ x₀ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem LeftLimit.toLeftLimitExpr
  : LeftLimit ⟨f, dom⟩ x₀ L → lim₋ x₀ f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimit.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : lim₋ x₀ f =. the L → LeftLimit ⟨f, dom⟩ x₀ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem RightLimit.toRightLimitExpr
  : RightLimit ⟨f, dom⟩ x₀ L → lim₊ x₀ f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimit.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : lim₊ x₀ f =. the L → RightLimit ⟨f, dom⟩ x₀ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem PosInftyLimit.toPosInftyLimitExpr
  : PosInftyLimit ⟨f, dom⟩ L → lim pos_infty f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimit.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
  : lim pos_infty f =. the L → PosInftyLimit ⟨f, dom⟩ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem NegInftyLimit.toNegInftyLimitExpr
  : NegInftyLimit ⟨f, dom⟩ L → lim neg_infty f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimit.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
  : lim neg_infty f =. the L → NegInftyLimit ⟨f, dom⟩ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem InftyLimit.toInftyLimitExpr
  : InftyLimit ⟨f, dom⟩ L → lim infty f =. the L
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimit.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
  : lim infty f =. the L → InftyLimit ⟨f, dom⟩ L
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem SeqLimitPosInfty.toSeqLimitExpr
  : SeqLimitPosInfty ⟨a, init, none⟩ → limₙ a =. pos_infty
:= fun h => GenericExprBridge.mpr (h : SeqLimitPosInfty ⟨a, 0, none⟩)

theorem SeqLimitPosInfty.fromSeqLimitExpr
  : limₙ a =. pos_infty → SeqLimitPosInfty ⟨a, init, none⟩
:= fun h => GenericExprBridge.mp h

theorem SeqLimitNegInfty.toSeqLimitExpr
  : SeqLimitNegInfty ⟨a, init, none⟩ → limₙ a =. neg_infty
:= fun h => GenericExprBridge.mpr (h : SeqLimitNegInfty ⟨a, 0, none⟩)

theorem SeqLimitNegInfty.fromSeqLimitExpr
  : limₙ a =. neg_infty → SeqLimitNegInfty ⟨a, init, none⟩
:= fun h => GenericExprBridge.mp h

theorem SeqLimitInfty.toSeqLimitExpr
  : SeqLimitInfty ⟨a, init, none⟩ → limₙ a =. infty
:= fun h => GenericExprBridge.mpr (h : SeqLimitInfty ⟨a, 0, none⟩)

theorem SeqLimitInfty.fromSeqLimitExpr
  : limₙ a =. infty → SeqLimitInfty ⟨a, init, none⟩
:= fun h => GenericExprBridge.mp h

theorem FuncLimitPosInfty.toFuncLimitExpr
  : FuncLimitPosInfty ⟨f, dom⟩ x₀ → lim x₀ f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitPosInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : lim x₀ f =. pos_infty → FuncLimitPosInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem FuncLimitNegInfty.toFuncLimitExpr
  : FuncLimitNegInfty ⟨f, dom⟩ x₀ → lim x₀ f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitNegInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : lim x₀ f =. neg_infty → FuncLimitNegInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem FuncLimitInfty.toFuncLimitExpr
  : FuncLimitInfty ⟨f, dom⟩ x₀ → lim x₀ f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem FuncLimitInfty.fromFuncLimitExpr
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : lim x₀ f =. infty → FuncLimitInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem LeftLimitPosInfty.toLeftLimitExpr
  : LeftLimitPosInfty ⟨f, dom⟩ x₀ → lim₋ x₀ f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitPosInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : lim₋ x₀ f =. pos_infty → LeftLimitPosInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem LeftLimitNegInfty.toLeftLimitExpr
  : LeftLimitNegInfty ⟨f, dom⟩ x₀ → lim₋ x₀ f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitNegInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : lim₋ x₀ f =. neg_infty → LeftLimitNegInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem LeftLimitInfty.toLeftLimitExpr
  : LeftLimitInfty ⟨f, dom⟩ x₀ → lim₋ x₀ f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem LeftLimitInfty.fromLeftLimitExpr
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : lim₋ x₀ f =. infty → LeftLimitInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem RightLimitPosInfty.toRightLimitExpr
  : RightLimitPosInfty ⟨f, dom⟩ x₀ → lim₊ x₀ f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitPosInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : lim₊ x₀ f =. pos_infty → RightLimitPosInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem RightLimitNegInfty.toRightLimitExpr
  : RightLimitNegInfty ⟨f, dom⟩ x₀ → lim₊ x₀ f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitNegInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : lim₊ x₀ f =. neg_infty → RightLimitNegInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem RightLimitInfty.toRightLimitExpr
  : RightLimitInfty ⟨f, dom⟩ x₀ → lim₊ x₀ f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem RightLimitInfty.fromRightLimitExpr
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : lim₊ x₀ f =. infty → RightLimitInfty ⟨f, dom⟩ x₀
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem PosInftyLimitPosInfty.toPosInftyLimitExpr
  : PosInftyLimitPosInfty ⟨f, dom⟩ → lim pos_infty f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitPosInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
  : lim pos_infty f =. pos_infty → PosInftyLimitPosInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem PosInftyLimitNegInfty.toPosInftyLimitExpr
  : PosInftyLimitNegInfty ⟨f, dom⟩ → lim pos_infty f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitNegInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
  : lim pos_infty f =. neg_infty → PosInftyLimitNegInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem PosInftyLimitInfty.toPosInftyLimitExpr
  : PosInftyLimitInfty ⟨f, dom⟩ → lim pos_infty f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem PosInftyLimitInfty.fromPosInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
  : lim pos_infty f =. infty → PosInftyLimitInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem NegInftyLimitPosInfty.toNegInftyLimitExpr
  : NegInftyLimitPosInfty ⟨f, dom⟩ → lim neg_infty f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitPosInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
  : lim neg_infty f =. pos_infty → NegInftyLimitPosInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem NegInftyLimitNegInfty.toNegInftyLimitExpr
  : NegInftyLimitNegInfty ⟨f, dom⟩ → lim neg_infty f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitNegInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
  : lim neg_infty f =. neg_infty → NegInftyLimitNegInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem NegInftyLimitInfty.toNegInftyLimitExpr
  : NegInftyLimitInfty ⟨f, dom⟩ → lim neg_infty f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem NegInftyLimitInfty.fromNegInftyLimitExpr
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
  : lim neg_infty f =. infty → NegInftyLimitInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem InftyLimitPosInfty.toInftyLimitExpr
  : InftyLimitPosInfty ⟨f, dom⟩ → lim infty f =. pos_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitPosInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
  : lim infty f =. pos_infty → InftyLimitPosInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem InftyLimitNegInfty.toInftyLimitExpr
  : InftyLimitNegInfty ⟨f, dom⟩ → lim infty f =. neg_infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitNegInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
  : lim infty f =. neg_infty → InftyLimitNegInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem InftyLimitInfty.toInftyLimitExpr
  : InftyLimitInfty ⟨f, dom⟩ → lim infty f =. infty
:= fun h => GenericExprBridge.mpr ⟨⟨1, zero_lt_one, by simp⟩, h.2⟩

theorem InftyLimitInfty.fromInftyLimitExpr
    (h_dom : ∃ M > 0, Ioi M ⊆ dom ∧ Iio (-M) ⊆ dom)
  : lim infty f =. infty → InftyLimitInfty ⟨f, dom⟩
:= fun h => ⟨h_dom, (GenericExprBridge.mp h).2⟩

theorem SeqLimitExpr.ofNotConverges
  : (¬ SeqConverges ⟨a, init, none⟩) → limₙ a =. diverg
:= fun h => GenericExprBridge.mpr h

theorem SeqLimitExpr.toNotConverges
  : limₙ a =. diverg → ¬ SeqConverges ⟨a, init, none⟩
:= fun h => GenericExprBridge.mp h

theorem FuncLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
  : (¬ FuncConvergesAt ⟨f, dom⟩ x₀) → lim x₀ f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem FuncLimitExpr.toNotConverges
  : lim x₀ f =. diverg → ¬ FuncConvergesAt ⟨f, dom⟩ x₀
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, subset_univ _⟩, h_L.2⟩

theorem LeftLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ dom)
  : (¬ LeftConvergesAt ⟨f, dom⟩ x₀) → lim₋ x₀ f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem LeftLimitExpr.toNotConverges
  : lim₋ x₀ f =. diverg → ¬ LeftConvergesAt ⟨f, dom⟩ x₀
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, subset_univ _⟩, h_L.2⟩

theorem RightLimitExpr.ofNotConverges
    (h_dom : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ dom)
  : (¬ RightConvergesAt ⟨f, dom⟩ x₀) → lim₊ x₀ f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem RightLimitExpr.toNotConverges
  : lim₊ x₀ f =. diverg → ¬ RightConvergesAt ⟨f, dom⟩ x₀
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, subset_univ _⟩, h_L.2⟩

theorem PosInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Ioi M ⊆ dom)
  : (¬ ConvergesAtPosInfty ⟨f, dom⟩) → lim pos_infty f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem PosInftyLimitExpr.toNotConverges
  : lim pos_infty f =. diverg → ¬ ConvergesAtPosInfty ⟨f, dom⟩
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, subset_univ _⟩, h_L.2⟩

theorem NegInftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom)
  : (¬ ConvergesAtNegInfty ⟨f, dom⟩) → lim neg_infty f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem NegInftyLimitExpr.toNotConverges
  : lim neg_infty f =. diverg → ¬ ConvergesAtNegInfty ⟨f, dom⟩
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, subset_univ _⟩, h_L.2⟩

theorem InftyLimitExpr.ofNotConverges
    (h_dom : ∃ M > 0, Iio (-M) ⊆ dom ∧ Ioi M ⊆ dom)
  : (¬ ConvergesAtInfty ⟨f, dom⟩) → lim infty f =. diverg
:= fun h => GenericExprBridge.mpr fun ⟨L, h_L⟩ => h ⟨L, h_dom, h_L.2⟩

theorem InftyLimitExpr.toNotConverges
  : lim infty f =. diverg → ¬ ConvergesAtInfty ⟨f, dom⟩
:= fun h ⟨L, h_L⟩ =>
  GenericExprBridge.mp h ⟨L, ⟨1, zero_lt_one, by grind⟩, h_L.2⟩

end


page_end
