/-
    «Calculus_21».Limit.Expr.BasicRules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
set_option linter.style.header false

local macro "script_exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Properties of Limit Expression -/

open Classical in section
variable {a b : ℕ → ℝ} {f g : ℝ → ℝ} {x₀ : ℝ}

private lemma generic_congr {C P N U : Prop} {C' P' N' U' : Prop}
    [laws : GenericExprLaws C P N U] [laws' : GenericExprLaws C' P' N' U']
    (hC : C ↔ C') (hP : P ↔ P') (hN : N ↔ N') (hU : U ↔ U')
    (hevC : ∀ h h', laws.evC h = laws'.evC h')
  : GenericExpr C P N U = GenericExpr C' P' N' U'
:= by
  by_cases hc : C
  · have hc' := hC.mp hc
    simp [GenericExpr, hc, hc', hevC hc hc']
  · have hc' : ¬ C' := fun h => hc (hC.mpr h)
    by_cases hp : P
    · have hp' := hP.mp hp
      simp [GenericExpr, hc, hc', hp, hp']
    · have hp' : ¬ P' := fun h => hp (hP.mpr h)
      by_cases hn : N
      · have hn' := hN.mp hn
        simp [GenericExpr, hc, hc', hp, hp', hn, hn']
      · have hn' : ¬ N' := fun h => hn (hN.mpr h)
        by_cases hu : U
        · have hu' := hU.mp hu
          simp [GenericExpr, hc, hc', hp, hp', hn, hn', hu, hu']
        · have hu' : ¬ U' := fun h => hu (hU.mpr h)
          simp [GenericExpr, hc, hc', hp, hp', hn, hn', hu, hu']

/-- Congruence of RSequence Limit (Expression) -/
theorem SeqLimitExpr.Congr
    (h_congr : ∃ N : ℕ, ∀ n > N, a n = b n)
  : limₙ a = limₙ b
:= by
  let A : RSequence := ⟨a, 0, none⟩
  let B : RSequence := ⟨b, 0, none⟩
  have h_congr' : ∃ N : ℕ, ∀ n > N, B.map n = A.map n := by
    rcases h_congr with ⟨N, h_N⟩
    exists N
    intro n h_n
    exact (h_N n h_n).symm
  apply generic_congr
  · constructor <;> intro ⟨L, hL⟩
    · exact ⟨L, hL.Congr rfl h_congr⟩
    · exact ⟨L, hL.Congr rfl h_congr'⟩
  · constructor <;> intro h
    · exact SeqLimitPosInfty.Congr h rfl h_congr
    · exact SeqLimitPosInfty.Congr h rfl h_congr'
  · constructor <;> intro h
    · exact SeqLimitNegInfty.Congr h rfl h_congr
    · exact SeqLimitNegInfty.Congr h rfl h_congr'
  · constructor <;> intro h
    · exact SeqLimitInfty.Congr h rfl h_congr
    · exact SeqLimitInfty.Congr h rfl h_congr'
  · intro hA hB
    exact ((choose_spec hA).Congr rfl h_congr).unique (choose_spec hB)

/-- Congruence of RFunction Limit (Expression) -/
theorem FuncLimitExpr.Congr
    (h_congr : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x)
  : lim x₀ f = lim x₀ g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨δ, hδ, heq⟩
  have heq' : ∀ x ∈ Nbhd x₀ δ, G.map x = F.map x := by
    intro x h_x
    exact (heq x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq⟩⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq'⟩⟩
  · constructor <;> intro h
    · exact FuncLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact FuncLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact FuncLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact FuncLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact FuncLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact FuncLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · intro hF hG
    exact
      (FuncLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩).unique
      (choose_spec hG)

/-- Congruence of Left Limit (Expression) -/
theorem LeftLimitExpr.Congr
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ x₀ f = lim₋ x₀ g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨δ, hδ, heq⟩
  have heq' : ∀ x ∈ Ioo (x₀ - δ) x₀, G.map x = F.map x := by
    intro x h_x
    exact (heq x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq⟩⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq'⟩⟩
  · constructor <;> intro h
    · exact LeftLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact LeftLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact LeftLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact LeftLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact LeftLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact LeftLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · intro hF hG
    exact
      (LeftLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩).unique
      (choose_spec hG)

/-- Congruence of Right Limit (Expression) -/
theorem RightLimitExpr.Congr
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ x₀ f = lim₊ x₀ g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨δ, hδ, heq⟩
  have heq' : ∀ x ∈ Ioo x₀ (x₀ + δ), G.map x = F.map x := by
    intro x h_x
    exact (heq x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq⟩⟩
    · exact ⟨L, hL.Congr ⟨δ, hδ, fun _ _ => trivial, heq'⟩⟩
  · constructor <;> intro h
    · exact RightLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact RightLimitPosInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact RightLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact RightLimitNegInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact RightLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq⟩
    · exact RightLimitInfty.Congr h ⟨δ, hδ, fun _ _ => trivial, heq'⟩
  · intro hF hG
    exact
      (RightLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩).unique
      (choose_spec hG)

/-- Congruence of Limit at Positive Infinity (Expression) -/
theorem PosInftyLimitExpr.Congr
    (h_congr : ∃ M > 0, ∀ x ∈ Ioi M, f x = g x)
  : lim pos_infty f = lim pos_infty g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨M, hM, heq⟩
  have heq' : ∀ x ∈ Ioi M, G.map x = F.map x := by
    intro x h_x
    exact (heq x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, heq⟩⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, heq'⟩⟩
  · constructor <;> intro h
    · exact PosInftyLimitPosInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact PosInftyLimitPosInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact PosInftyLimitNegInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact PosInftyLimitNegInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact PosInftyLimitInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact PosInftyLimitInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · intro hF hG
    exact
      (PosInftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, heq⟩).unique
      (choose_spec hG)

/-- Congruence of Limit at Negative Infinity (Expression) -/
theorem NegInftyLimitExpr.Congr
    (h_congr : ∃ M > 0, ∀ x ∈ Iio (-M), f x = g x)
  : lim neg_infty f = lim neg_infty g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨M, hM, heq⟩
  have heq' : ∀ x ∈ Iio (-M), G.map x = F.map x := by
    intro x h_x
    exact (heq x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, heq⟩⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, heq'⟩⟩
  · constructor <;> intro h
    · exact NegInftyLimitPosInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact NegInftyLimitPosInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact NegInftyLimitNegInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact NegInftyLimitNegInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · constructor <;> intro h
    · exact NegInftyLimitInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq⟩
    · exact NegInftyLimitInfty.Congr h ⟨M, hM, fun _ _ => trivial, heq'⟩
  · intro hF hG
    exact
      (NegInftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, heq⟩).unique
      (choose_spec hG)

/-- Congruence of Limit at Infinity (Expression) -/
theorem InftyLimitExpr.Congr
    (h_congr : ∃ M > 0, (∀ x ∈ Iio (-M), f x = g x) ∧ (∀ x ∈ Ioi M, f x = g x))
  : lim infty f = lim infty g
:= by
  let F : RFunction := ⟨f, Iii⟩
  let G : RFunction := ⟨g, Iii⟩
  rcases h_congr with ⟨M, hM, hneg, hpos⟩
  have hneg' : ∀ x ∈ Iio (-M), G.map x = F.map x := by
    intro x h_x
    exact (hneg x h_x).symm
  have hpos' : ∀ x ∈ Ioi M, G.map x = F.map x := by
    intro x h_x
    exact (hpos x h_x).symm
  apply generic_congr
  · constructor <;> rintro ⟨L, hL⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial, hneg, hpos⟩⟩
    · exact ⟨L, hL.Congr ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial, hneg', hpos'⟩⟩
  · constructor <;> intro h
    · exact InftyLimitPosInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos x h_x) (fun h_x => hneg x h_x)⟩
    · exact InftyLimitPosInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos' x h_x) (fun h_x => hneg' x h_x)⟩
  · constructor <;> intro h
    · exact InftyLimitNegInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos x h_x) (fun h_x => hneg x h_x)⟩
    · exact InftyLimitNegInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos' x h_x) (fun h_x => hneg' x h_x)⟩
  · constructor <;> intro h
    · exact InftyLimitInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos x h_x) (fun h_x => hneg x h_x)⟩
    · exact InftyLimitInfty.Congr h
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial,
          fun x h_x => h_x.elim (fun h_x => hpos' x h_x) (fun h_x => hneg' x h_x)⟩
  · intro hF hG
    exact
      (InftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial, hneg, hpos⟩).unique
      (choose_spec hG)

end


/-! # Basic Rules of Limit Calculation -/

section
variable {a b : ℕ → ℝ} {f g : ℝ → ℝ} {n : ℕ} {k x₀ : ℝ}

/-- RSequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul
  : limₙ (k • a) =. the k * limₙ a
:= sorry

/-- RFunction Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul
  : lim x₀ (k • f) =. the k * lim x₀ f
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul
  : lim₋ x₀ (k • f) =. the k * lim₋ x₀ f
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul
  : lim₊ x₀ (k • f) =. the k * lim₊ x₀ f
:= sorry

/-- RSequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul'
  : limₙ (fun n ↦ a n * k) =. limₙ a * the k
:= sorry

/-- RFunction Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul'
  : (lim x₀ fun x ↦ f x * k) =. lim x₀ f * the k
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul'
  : (lim₋ x₀ fun x ↦ f x * k) =. lim₋ x₀ f * the k
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul'
  : (lim₊ x₀ fun x ↦ f x * k) =. lim₊ x₀ f * the k
:= sorry

/-- RSequence Limit of Additive Inverse (Expression) -/
theorem SeqLimitExpr.Neg
  : limₙ (-a) =. - limₙ a
:= sorry

/-- RFunction Limit of Additive Inverse (Expression) -/
theorem FuncLimitExpr.Neg
  : lim x₀ (-f) =. - lim x₀ f
:= sorry

/-- Left Limit of Additive Inverse (Expression) -/
theorem LeftLimitExpr.Neg
  : lim₋ x₀ (-f) =. - lim₋ x₀ f
:= sorry

/-- Right Limit of Additive Inverse (Expression) -/
theorem RightLimitExpr.Neg
  : lim₊ x₀ (-f) =. - lim₊ x₀ f
:= sorry

/-- RSequence Limit of Multiplicative Scalar Power (Expression) -/
theorem SeqLimitExpr.MSPow
  : limₙ (a ^ n) =. limₙ a ^ the n
:= sorry

/-- RFunction Limit of Multiplicative Scalar Power (Expression) -/
theorem FuncLimitExpr.MSPow
  : lim x₀ (f ^ n) =. lim x₀ f ^ the n
:= sorry

/-- Left Limit of Multiplicative Scalar Power (Expression) -/
theorem LeftLimitExpr.MSPow
  : lim₋ x₀ (f ^ n) =. lim₋ x₀ f ^ the n
:= sorry

/-- Right Limit of Multiplicative Scalar Power (Expression) -/
theorem RightLimitExpr.MSPow
  : lim₊ x₀ (f ^ n) =. lim₊ x₀ f ^ the n
:= sorry

/-- RSequence Limit of Multiplicative Inverse (Expression) -/
theorem SeqLimitExpr.Inv
  : limₙ a⁻¹ =. (limₙ a)⁻¹
:= sorry

/-- RFunction Limit of Multiplicative Inverse (Expression) -/
theorem FuncLimitExpr.Inv
  : lim x₀ f⁻¹ =. (lim x₀ f)⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse (Expression) -/
theorem LeftLimitExpr.Inv
  : lim₋ x₀ f⁻¹ =. (lim₋ x₀ f)⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse (Expression) -/
theorem RightLimitExpr.Inv
  : lim₊ x₀ f⁻¹ =. (lim₊ x₀ f)⁻¹
:= sorry

/-- RSequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add
  : limₙ (a + b) =. limₙ a + limₙ b
:= sorry

/-- RFunction Limit Addition (Expression) -/
theorem FuncLimitExpr.Add
  : lim x₀ (f + g) =. lim x₀ f + lim x₀ g
:= sorry

/-- Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add
  : lim₋ x₀ (f + g) =. lim₋ x₀ f + lim₋ x₀ g
:= sorry

/-- Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add
  : lim₊ x₀ (f + g) =. lim₊ x₀ f + lim₊ x₀ g
:= sorry

/-- RSequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub
  : limₙ (a - b) =. limₙ a - limₙ b
:= sorry

/-- RFunction Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub
  : lim x₀ (f - g) =. lim x₀ f - lim x₀ g
:= sorry

/-- Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub
  : lim₋ x₀ (f - g) =. lim₋ x₀ f - lim₋ x₀ g
:= sorry

/-- Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub
  : lim₊ x₀ (f - g) =. lim₊ x₀ f - lim₊ x₀ g
:= sorry

/-- RSequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul
  : limₙ (a * b) =. limₙ a * limₙ b
:= sorry

/-- RFunction Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul
  : lim x₀ (f * g) =. lim x₀ f * lim x₀ g
:= sorry

/-- Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul
  : lim₋ x₀ (f * g) =. lim₋ x₀ f * lim₋ x₀ g
:= sorry

/-- Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul
  : lim₊ x₀ (f * g) =. lim₊ x₀ f * lim₊ x₀ g
:= sorry

/-- RSequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div
  : limₙ (a / b) =. limₙ a / limₙ b
:= sorry

/-- RFunction Limit Division (Expression) -/
theorem FuncLimitExpr.Div
  : lim x₀ (f / g) =. lim x₀ f / lim x₀ g
:= sorry

/-- Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div
  : lim₋ x₀ (f / g) =. lim₋ x₀ f / lim₋ x₀ g
:= sorry

/-- Right Limit Division (Expression) -/
theorem RightLimitExpr.Div
  : lim₊ x₀ (f / g) =. lim₊ x₀ f / lim₊ x₀ g
:= sorry

end

section
variable {a b c : ℕ → ℝ} {f g h : ℝ → ℝ} {x₀ : ℝ} {A : LimitValue}

/-- RFunction Limit → Left Limit (Expression) -/
theorem FuncLimitExpr.toLeft
  : lim x₀ f =. A → lim₋ x₀ f =. A
:= sorry

/-- RFunction Limit → Right Limit (Expression) -/
theorem FuncLimitExpr.toRight
  : lim x₀ f =. A → lim₊ x₀ f =. A
:= sorry

/-- Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr.toPos
  : lim infty f =. A → lim pos_infty f =. A
:= sorry

/-- Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr.toNeg
  : lim infty f =. A → lim neg_infty f =. A
:= sorry

/-- Squeeze Theorem for RSequence Limit (Expression) -/
theorem SeqLimitExpr.Squeeze
    (h_sqz : ∃ N : ℕ, ∀ n > N, a n ≤ b n ∧ b n ≤ c n)
  : limₙ a =. A ∧ limₙ c =. A → limₙ b =. A
:= sorry

/-- Squeeze Theorem for RFunction Limit (Expression) -/
theorem FuncLimitExpr.Squeeze
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≤ g x ∧ g x ≤ h x)
  : lim x₀ f =. A ∧ lim x₀ h =. A → lim x₀ g =. A
:= sorry

end


page_end
