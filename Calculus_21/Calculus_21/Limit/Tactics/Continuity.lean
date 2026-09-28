/-
    «Calculus_21».Limit.Tactics.Continuity
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Elementary

open RFunction


/-! # Continuity Inference for `RFunction` -/

namespace AutoContinuity
variable {F G : RFunction} {x l r k : ℝ}

private lemma iccOfPointwise (h : ∀ t ∈ Icc l r, F.isContinuousAt t)
    (hlr : l ≤ r) : F.isContinuousInIcc l r :=
  ⟨fun t ht => h t ⟨ht.1.le, ht.2.le⟩,
    ⟨(h l ⟨le_rfl, hlr⟩).1, FuncLimit.toRight (h l ⟨le_rfl, hlr⟩).2⟩,
    ⟨(h r ⟨hlr, le_rfl⟩).1, FuncLimit.toLeft (h r ⟨hlr, le_rfl⟩).2⟩⟩

private lemma iccOfAll (h : ∀ t, F.isContinuousAt t) : F.isContinuousInIcc l r :=
  ⟨fun t _ => h t, ⟨(h l).1, FuncLimit.toRight (h l).2⟩,
    ⟨(h r).1, FuncLimit.toLeft (h r).2⟩⟩

-- Only commit when the whole bridge closes. A stronger pointwise premise must
-- never replace a goal that could instead be proved using one-sided endpoints.
-- Disable recovery, and accept Aesop's normalized (curried) Icc hypotheses too.
@[aesop safe -100 tactic (rule_sets := [AutoContinuity])
  (index := [target RFunction.isContinuousInIcc _ _ _])]
private meta def closePointwiseInterval : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic (← `(tactic|
    solve
    | apply iccOfAll; assumption
    | apply iccOfPointwise
      · first | assumption | simp only [Set.mem_Icc, and_imp]; assumption
      · first | assumption | exact le_of_lt (by assumption)))

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma iccIntro
    (h_Ioo : F.isContinuousIn (Ioo l r))
    (h_left : F.isRightContinuousAt l)
    (h_right : F.isLeftContinuousAt r)
  : F.isContinuousInIcc l r
:= ⟨h_Ioo, h_left, h_right⟩

-- Existing full continuity must project before safe operation rules split the
-- expression. Backward bridges remain unsafe so one-sided proofs can still win.
@[aesop safe -10 forward (rule_sets := [AutoContinuity]),
  aesop unsafe 80% apply (rule_sets := [AutoContinuity])]
private lemma atToLeftAt
  : F.isContinuousAt x → F.isLeftContinuousAt x
:= fun h => ⟨h.1, FuncLimit.toLeft h.2⟩

@[aesop safe -10 forward (rule_sets := [AutoContinuity]),
  aesop unsafe 80% apply (rule_sets := [AutoContinuity])]
private lemma atToRightAt
  : F.isContinuousAt x → F.isRightContinuousAt x
:= fun h => ⟨h.1, FuncLimit.toRight h.2⟩

@[aesop safe forward (rule_sets := [AutoContinuity])]
private lemma iccInterior
  : F.isContinuousInIcc l r → F.isContinuousIn (Ioo l r)
:= fun h => h.1

@[aesop safe forward (rule_sets := [AutoContinuity])]
private lemma iccRightEnd
  : F.isContinuousInIcc l r → F.isLeftContinuousAt r
:= fun h => h.2.2

@[aesop safe forward (rule_sets := [AutoContinuity])]
private lemma iccLeftEnd
  : F.isContinuousInIcc l r → F.isRightContinuousAt l
:= fun h => h.2.1

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma atToMem
  : F.isContinuousAt x → x ∈ F.domain
:= fun h => h.1

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma atToLimit
  : F.isContinuousAt x → FuncLimit F x (F.map x)
:= fun h => h.2

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma leftAtToMem
  : F.isLeftContinuousAt x → x ∈ F.domain
:= fun h => h.1

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma leftAtToLimit
  : F.isLeftContinuousAt x → LeftLimit F x (F.map x)
:= fun h => h.2

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma rightAtToMem
  : F.isRightContinuousAt x → x ∈ F.domain
:= fun h => h.1

@[aesop unsafe 90% apply (rule_sets := [AutoContinuity])]
private lemma rightAtToLimit
  : F.isRightContinuousAt x → RightLimit F x (F.map x)
:= fun h => h.2

-- Pointwise conclusions give Aesop concrete function heads to index.
@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma constant {c : ℝ} : (Constant c).isContinuousAt x :=
  Continuity.Constant x (mem_univ _)

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma identity : Identity.isContinuousAt x := Continuity.Identity x (mem_univ _)

-- One-sided operation rules avoid decomposing arbitrary conjunctions or limits.
@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftNeg (h : F.isLeftContinuousAt x) : (-F).isLeftContinuousAt x :=
  ⟨h.1, LeftLimit.Neg h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightNeg (h : F.isRightContinuousAt x) : (-F).isRightContinuousAt x :=
  ⟨h.1, RightLimit.Neg h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftSMul (h : F.isLeftContinuousAt x) : (k • F).isLeftContinuousAt x :=
  ⟨h.1, LeftLimit.SMul h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightSMul (h : F.isRightContinuousAt x) : (k • F).isRightContinuousAt x :=
  ⟨h.1, RightLimit.SMul h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftAdd (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x) :
    (F + G).isLeftContinuousAt x := ⟨⟨hF.1, hG.1⟩, LeftLimit.Add hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightAdd (hF : F.isRightContinuousAt x) (hG : G.isRightContinuousAt x) :
    (F + G).isRightContinuousAt x := ⟨⟨hF.1, hG.1⟩, RightLimit.Add hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftSub (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x) :
    (F - G).isLeftContinuousAt x := ⟨⟨hF.1, hG.1⟩, LeftLimit.Sub hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightSub (hF : F.isRightContinuousAt x) (hG : G.isRightContinuousAt x) :
    (F - G).isRightContinuousAt x := ⟨⟨hF.1, hG.1⟩, RightLimit.Sub hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftMul (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x) :
    (F * G).isLeftContinuousAt x := ⟨⟨hF.1, hG.1⟩, LeftLimit.Mul ⟨hF.2, hG.2⟩⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightMul (hF : F.isRightContinuousAt x) (hG : G.isRightContinuousAt x) :
    (F * G).isRightContinuousAt x := ⟨⟨hF.1, hG.1⟩, RightLimit.Mul ⟨hF.2, hG.2⟩⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftDiv (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x)
    (hne : G.map x ≠ 0) : (F / G).isLeftContinuousAt x :=
  ⟨⟨⟨hF.1, hG.1⟩, hne⟩, LeftLimit.Div hne hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightDiv (hF : F.isRightContinuousAt x) (hG : G.isRightContinuousAt x)
    (hne : G.map x ≠ 0) : (F / G).isRightContinuousAt x :=
  ⟨⟨⟨hF.1, hG.1⟩, hne⟩, RightLimit.Div hne hF.2 hG.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftInv (h : F.isLeftContinuousAt x) (hne : F.map x ≠ 0) :
    F⁻¹.isLeftContinuousAt x := ⟨⟨h.1, hne⟩, LeftLimit.Inv hne h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightInv (h : F.isRightContinuousAt x) (hne : F.map x ≠ 0) :
    F⁻¹.isRightContinuousAt x := ⟨⟨h.1, hne⟩, RightLimit.Inv hne h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma leftMSPow {n : ℕ} (h : F.isLeftContinuousAt x) :
    (F ^ n).isLeftContinuousAt x := ⟨h.1, LeftLimit.MSPow h.2⟩

@[aesop safe apply (rule_sets := [AutoContinuity])]
private lemma rightMSPow {n : ℕ} (h : F.isRightContinuousAt x) :
    (F ^ n).isRightContinuousAt x := ⟨h.1, RightLimit.MSPow h.2⟩

end AutoContinuity

attribute [aesop safe apply (rule_sets := [AutoContinuity])]
  Continuity.Neg Continuity.SMul Continuity.Inv Continuity.MSPow
  Continuity.Add Continuity.Sub Continuity.Mul Continuity.Div Continuity.Comp


macro "infer_continuity" : tactic => `(tactic|
  aesop
    (rule_sets := [AutoContinuity])
    (config := { useSimpAll := false, terminal := true })
)
script_macro "infer_continuity" => `(tactic| infer_continuity)
