/-
    «Calculus_21».Limit.Expr.BasicRules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Expr.Init
import «Calculus_21».Limit.Elementary
set_option linter.style.header false

local macro "exists" data:term "with" cond:term : tactic => `(tactic| refine ⟨$data, $cond, ?_⟩)


/-! # Properties of Limit Expression -/

open Classical in
private lemma generic_congr {C P N U : Prop} {C' P' N' U' : Prop}
    {evC : C → ℝ} {evC' : C' → ℝ}
    (hC : C ↔ C') (hP : P ↔ P') (hN : N ↔ N') (hU : U ↔ U')
    (hevC : ∀ h h', evC h = evC' h')
  : genericExpr C P N U evC = genericExpr C' P' N' U' evC'
:= by
  by_cases hc : C
  · have hc' := hC.mp hc
    simp [genericExpr, hc, hc', hevC hc hc']
  · have hc' : ¬ C' := fun h => hc (hC.mpr h)
    by_cases hp : P
    · have hp' := hP.mp hp
      simp [genericExpr, hc, hc', hp, hp']
    · have hp' : ¬ P' := fun h => hp (hP.mpr h)
      by_cases hn : N
      · have hn' := hN.mp hn
        simp [genericExpr, hc, hc', hp, hp', hn, hn']
      · have hn' : ¬ N' := fun h => hn (hN.mpr h)
        by_cases hu : U
        · have hu' := hU.mp hu
          simp [genericExpr, hc, hc', hp, hp', hn, hn', hu, hu']
        · have hu' : ¬ U' := fun h => hu (hU.mpr h)
          simp [genericExpr, hc, hc', hp, hp', hn, hn', hu, hu']

open Classical in section
variable {a b : ℕ → ℝ} {f g : ℝ → ℝ} {x₀ : ℝ}

/-- Congruence of Sequence Limit (Expression) -/
lemma SeqLimitExpr.Congr {a b : ℕ → ℝ}
    (h_congr : ∃ N : ℕ, ∀ n > N, a n = b n)
  : limₙ a = limₙ b
:= by
  let A : Sequence := ⟨a, 0, none⟩
  let B : Sequence := ⟨b, 0, none⟩
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
    exact SeqLimit_Unique ((choose_spec hA).Congr rfl h_congr) (choose_spec hB)

/-- Congruence of Function Limit (Expression) -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x)
  : lim f x₀ = lim g x₀
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact FuncLimit_Unique
      (FuncLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩)
      (choose_spec hG)

/-- Congruence of Left Limit (Expression) -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ = lim₋ g x₀
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact LeftLimit_Unique
      (LeftLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩)
      (choose_spec hG)

/-- Congruence of Right Limit (Expression) -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ = lim₊ g x₀
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact RightLimit_Unique
      (RightLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨δ, hδ, fun _ _ => trivial, heq⟩)
      (choose_spec hG)

/-- Congruence of Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Ioi M, f x = g x)
  : lim pos_infty f = lim pos_infty g
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact PosInftyLimit_Unique
      (PosInftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, heq⟩)
      (choose_spec hG)

/-- Congruence of Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Iio (-M), f x = g x)
  : lim neg_infty f = lim neg_infty g
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact NegInftyLimit_Unique
      (NegInftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, heq⟩)
      (choose_spec hG)

/-- Congruence of Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, (∀ x ∈ Iio (-M), f x = g x) ∧ (∀ x ∈ Ioi M, f x = g x))
  : lim infty f = lim infty g
:= by
  let F : Function := ⟨f, Iii⟩
  let G : Function := ⟨g, Iii⟩
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
    exact InftyLimit_Unique
      (InftyLimit.Congr (F := F) (G := G) (choose_spec hF)
        ⟨M, hM, fun _ _ => trivial, fun _ _ => trivial, hneg, hpos⟩)
      (choose_spec hG)

end


/-! # Basic Rules of Limit Calculation -/

section
variable {a b : ℕ → ℝ} {f g : ℝ → ℝ} {n : ℕ} {k x₀ : ℝ}

/-- Sequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul
  : limₙ (k • a) =. the k * limₙ a
:= sorry

/-- Function Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul
  : lim (k • f) x₀ =. the k * lim f x₀
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul
  : lim₋ (k • f) x₀ =. the k * lim₋ f x₀
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul
  : lim₊ (k • f) x₀ =. the k * lim₊ f x₀
:= sorry

/-- Sequence Limit of Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul'
  : limₙ (fun n ↦ a n * k) =. limₙ a * the k
:= sorry

/-- Function Limit of Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.SMul'
  : lim (fun x ↦ f x * k) x₀ =. lim f x₀ * the k
:= sorry

/-- Left Limit of Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul'
  : lim₋ (fun x ↦ f x * k) x₀ =. lim₋ f x₀ * the k
:= sorry

/-- Right Limit of Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul'
  : lim₊ (fun x ↦ f x * k) x₀ =. lim₊ f x₀ * the k
:= sorry

/-- Sequence Limit of Additive Inverse (Expression) -/
theorem SeqLimitExpr.Neg
  : limₙ (-a) =. - limₙ a
:= sorry

/-- Function Limit of Additive Inverse (Expression) -/
theorem FuncLimitExpr.Neg
  : lim (-f) x₀ =. - lim f x₀
:= sorry

/-- Left Limit of Additive Inverse (Expression) -/
theorem LeftLimitExpr.Neg
  : lim₋ (-f) x₀ =. - lim₋ f x₀
:= sorry

/-- Right Limit of Additive Inverse (Expression) -/
theorem RightLimitExpr.Neg
  : lim₊ (-f) x₀ =. - lim₊ f x₀
:= sorry

/-- Sequence Limit of Multiplicative Scalar Power (Expression) -/
theorem SeqLimitExpr.MSPow
  : limₙ (a ^ n) =. limₙ a ^ the n
:= sorry

/-- Function Limit of Multiplicative Scalar Power (Expression) -/
theorem FuncLimitExpr.MSPow
  : lim (f ^ n) x₀ =. lim f x₀ ^ the n
:= sorry

/-- Left Limit of Multiplicative Scalar Power (Expression) -/
theorem LeftLimitExpr.MSPow
  : lim₋ (f ^ n) x₀ =. lim₋ f x₀ ^ the n
:= sorry

/-- Right Limit of Multiplicative Scalar Power (Expression) -/
theorem RightLimitExpr.MSPow
  : lim₊ (f ^ n) x₀ =. lim₊ f x₀ ^ the n
:= sorry

/-- Sequence Limit of Multiplicative Inverse (Expression) -/
theorem SeqLimitExpr.Inv
  : limₙ a⁻¹ =. (limₙ a)⁻¹
:= sorry

/-- Function Limit of Multiplicative Inverse (Expression) -/
theorem FuncLimitExpr.Inv
  : lim f⁻¹ x₀ =. (lim f x₀)⁻¹
:= sorry

/-- Left Limit of Multiplicative Inverse (Expression) -/
theorem LeftLimitExpr.Inv
  : lim₋ f⁻¹ x₀ =. (lim₋ f x₀)⁻¹
:= sorry

/-- Right Limit of Multiplicative Inverse (Expression) -/
theorem RightLimitExpr.Inv
  : lim₊ f⁻¹ x₀ =. (lim₊ f x₀)⁻¹
:= sorry

/-- Sequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add
  : limₙ (a + b) =. limₙ a + limₙ b
:= sorry

/-- Function Limit Addition (Expression) -/
theorem FuncLimitExpr.Add
  : lim (f + g) x₀ =. lim f x₀ + lim g x₀
:= sorry

/-- Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add
  : lim₋ (f + g) x₀ =. lim₋ f x₀ + lim₋ g x₀
:= sorry

/-- Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add
  : lim₊ (f + g) x₀ =. lim₊ f x₀ + lim₊ g x₀
:= sorry

/-- Sequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub
  : limₙ (a - b) =. limₙ a - limₙ b
:= sorry

/-- Function Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub
  : lim (f - g) x₀ =. lim f x₀ - lim g x₀
:= sorry

/-- Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub
  : lim₋ (f - g) x₀ =. lim₋ f x₀ - lim₋ g x₀
:= sorry

/-- Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub
  : lim₊ (f - g) x₀ =. lim₊ f x₀ - lim₊ g x₀
:= sorry

/-- Sequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul
  : limₙ (a * b) =. limₙ a * limₙ b
:= sorry

/-- Function Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul
  : lim (f * g) x₀ =. lim f x₀ * lim g x₀
:= sorry

/-- Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul
  : lim₋ (f * g) x₀ =. lim₋ f x₀ * lim₋ g x₀
:= sorry

/-- Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul
  : lim₊ (f * g) x₀ =. lim₊ f x₀ * lim₊ g x₀
:= sorry

/-- Sequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div
  : limₙ (a / b) =. limₙ a / limₙ b
:= sorry

/-- Function Limit Division (Expression) -/
theorem FuncLimitExpr.Div
  : lim (f / g) x₀ =. lim f x₀ / lim g x₀
:= sorry

/-- Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div
  : lim₋ (f / g) x₀ =. lim₋ f x₀ / lim₋ g x₀
:= sorry

/-- Right Limit Division (Expression) -/
theorem RightLimitExpr.Div
  : lim₊ (f / g) x₀ =. lim₊ f x₀ / lim₊ g x₀
:= sorry

end

section
variable {a b c : ℕ → ℝ} {f g h : ℝ → ℝ} {x₀ : ℝ} {A : LimitValue}

/-- Function Limit → Left Limit (Expression) -/
theorem FuncLimitExpr.toLeft
  : lim f x₀ =. A → lim₋ f x₀ =. A
:= sorry

/-- Function Limit → Right Limit (Expression) -/
theorem FuncLimitExpr.toRight
  : lim f x₀ =. A → lim₊ f x₀ =. A
:= sorry

/-- Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr.toPos
  : lim infty f =. A → lim pos_infty f =. A
:= sorry

/-- Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr.toNeg
  : lim infty f =. A → lim neg_infty f =. A
:= sorry

/-- Squeeze Theorem for Sequence Limit (Expression) -/
theorem SeqLimitExpr.Squeeze
    (h_sqz : ∃ N : ℕ, ∀ n > N, a n ≤ b n ∧ b n ≤ c n)
  : limₙ a =. A ∧ limₙ c =. A → limₙ b =. A
:= sorry

/-- Squeeze Theorem for Function Limit (Expression) -/
theorem FuncLimitExpr.Squeeze
    (h_sqz : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≤ g x ∧ g x ≤ h x)
  : lim f x₀ =. A ∧ lim h x₀ =. A → lim g x₀ =. A
:= sorry

end


page_end
