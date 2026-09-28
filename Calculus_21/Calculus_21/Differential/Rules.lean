/-
    «Calculus_21».Differential.Rules
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Expr
import «Calculus_21».Limit.Elementary
set_option linter.style.header false

open LimitValue (finite_neg finite_add finite_sub finite_mul finite_div)


/-! # Derivative Calculation Rules -/

section
variable {n : ℕ} {F G : RFunction} {f g : ℝ → ℝ} {k x₀ D₁ D₂ : ℝ}

/-- Scalar Multiplication of Derivative Expression -/
theorem DerivExpr.SMul
  : D (k • f) x₀ =. the k * D f x₀
:= script
  calc
    _  =  lim x₀ fun x ↦ (k * f x - k * f x₀) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ k * ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. the k * lim x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_smul
    _  =  the k * D f x₀
          := rfl

/-- Scalar Multiplication of Derivative -/
theorem Deriv.SMul
    (h_F : Deriv F x₀ D₁)
  : Deriv (k • F) x₀ (k * D₁)
:= by
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation => calc
      D (k • F).map x₀ =. the k * D F.map x₀ := DerivExpr.SMul
      _ = the k * the D₁ := by poly_rw [h_F.toDerivExpr]
      _ = the (k * D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Scalar Multiplication of Left Derivative Expression -/
theorem LeftDerivExpr.SMul
  : D₋ (k • f) x₀ =. the k * D₋ f x₀
:= script
  calc
    _  =  lim₋ x₀ fun x ↦ (k * f x - k * f x₀) / (x - x₀)
          := rfl
    _  =  lim₋ x₀ fun x ↦ k * ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. the k * lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_smul
    _  =  the k * D₋ f x₀
          := rfl

/-- Scalar Multiplication of Left Derivative -/
theorem LeftDeriv.SMul
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (k • F) x₀ (k * D₁)
:= by
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation => calc
      D₋ (k • F).map x₀ =. the k * D₋ F.map x₀ := LeftDerivExpr.SMul
      _ = the k * the D₁ := by poly_rw [h_F.toLeftDerivExpr]
      _ = the (k * D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Scalar Multiplication of Right Derivative Expression -/
theorem RightDerivExpr.SMul
  : D₊ (k • f) x₀ =. the k * D₊ f x₀
:= script
  calc
    _  =  lim₊ x₀ fun x ↦ (k * f x - k * f x₀) / (x - x₀)
          := rfl
    _  =  lim₊ x₀ fun x ↦ k * ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. the k * lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_smul
    _  =  the k * D₊ f x₀
          := rfl

/-- Scalar Multiplication of Right Derivative -/
theorem RightDeriv.SMul
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (k • F) x₀ (k * D₁)
:= by
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation => calc
      D₊ (k • F).map x₀ =. the k * D₊ F.map x₀ := RightDerivExpr.SMul
      _ = the k * the D₁ := by poly_rw [h_F.toRightDerivExpr]
      _ = the (k * D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Scalar Multiplication of N-th Order Derivative -/
theorem NthDeriv.SMul
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (k • F) x₀ (k * D₁)
:= by
  classical
  have smul_deriv : ∀ {G : RFunction} {x d c : ℝ},
      Deriv G x d → Deriv (c • G) x (c * d) := by
    intro G x d c hd
    have heq : ((c • G - Constant ((c • G).map x)) / (Identity - Constant x)) =
        c • ((G - Constant (G.map x)) / (Identity - Constant x)) := by
      apply RFunction.ext
      · funext y
        change (c * G.map y - c * G.map x) / (y - x) =
          c * ((G.map y - G.map x) / (y - x))
        ring
      · rfl
    unfold Deriv
    rw [heq]
    exact FuncLimit.SMul hd
  have zero_deriv : ∀ (G : RFunction) (x : ℝ),
      (∀ y, G.map y = 0) → (∃ δ > 0, Nbhd x δ ⊆ G.domain) → Deriv G x 0 := by
    intro G x hmap hdom
    constructor
    · rcases hdom with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, fun y hy => ?_⟩
      exact ⟨⟨⟨hdom hy, trivial⟩, ⟨trivial, trivial⟩⟩, sub_ne_zero.mpr hy.2.2⟩
    · intro ε hε
      refine ⟨1, zero_lt_one, fun y _ => ?_⟩
      change (G.map y - G.map x) / (y - x) ∈ Nbho 0 ε
      simp only [hmap, sub_self, zero_div]
      exact ⟨by linarith, by linarith⟩
  by_cases hk : k = 0
  · subst k
    have hz : ∀ m, (∀ x, (NthDiff m ((0 : ℝ) • F)).map x = 0) ∧
        (NthDiff m F).domain ⊆ (NthDiff m ((0 : ℝ) • F)).domain := by
      intro m
      induction m with
      | zero => exact ⟨fun x => zero_mul _, fun _ hx => hx⟩
      | succ m ih =>
        have hd : ∀ x, (NthDiff m F).isDerivableAt x →
            Deriv (NthDiff m ((0 : ℝ) • F)) x 0 := by
          intro x ⟨d, hd⟩
          apply zero_deriv _ _ ih.1
          rcases hd.1 with ⟨δ, hδ, hdom⟩
          exact ⟨δ, hδ, fun y hy => ih.2 (hdom hy).1.1.1⟩
        constructor
        · intro x
          change (if h : (NthDiff m ((0 : ℝ) • F)).isDerivableAt x then
            Classical.choose h else 0) = 0
          split
          · rename_i h
            apply FuncLimit.unique (Classical.choose_spec h)
            apply zero_deriv _ _ ih.1
            rcases (Classical.choose_spec h).1 with ⟨δ, hδ, hdom⟩
            exact ⟨δ, hδ, fun y hy => (hdom hy).1.1.1⟩
          · rfl
        · intro x hx
          exact ⟨0, hd x hx⟩
    induction n generalizing D₁ with
    | zero => exact ⟨by change 0 * F.map x₀ = 0 * D₁; simp, h_F.2⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := h_F.lower
      refine ⟨⟨0 * d, ih hd⟩, ?_⟩
      rw [zero_mul]
      apply zero_deriv _ _ (hz n).1
      rcases h_F.deriv.1 with ⟨δ, hδ, hdom⟩
      exact ⟨δ, hδ, fun y hy => (hz n).2 (hdom hy).1.1.1⟩
  · have hdiff : ∀ G : RFunction, Diff (k • G) = k • Diff G := by
      intro G
      have hiff : ∀ x, (k • G).isDerivableAt x ↔ G.isDerivableAt x := by
        intro x
        constructor
        · rintro ⟨d, hd⟩
          have heq : k⁻¹ • (k • G) = G := by
            apply RFunction.ext
            · funext y
              change k⁻¹ * (k * G.map y) = G.map y
              rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
            · rfl
          exact ⟨k⁻¹ * d, heq ▸ smul_deriv hd⟩
        · rintro ⟨d, hd⟩
          exact ⟨k * d, smul_deriv hd⟩
      apply RFunction.ext
      · funext x
        change (if h : (k • G).isDerivableAt x then Classical.choose h else 0) =
          k * (if h : G.isDerivableAt x then Classical.choose h else 0)
        by_cases h : G.isDerivableAt x
        · rw [dif_pos h, dif_pos ((hiff x).mpr h)]
          exact FuncLimit.unique (Classical.choose_spec ((hiff x).mpr h))
            (smul_deriv (Classical.choose_spec h))
        · rw [dif_neg h, dif_neg (fun hs => h ((hiff x).mp hs)), mul_zero]
      · exact Set.ext hiff
    have hn : ∀ m, NthDiff m (k • F) = k • NthDiff m F := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [NthDiff_succ, ih, hdiff, NthDiff_succ]
    induction n generalizing D₁ with
    | zero => exact ⟨congrArg (k * ·) h_F.1, h_F.2⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := h_F.lower
      refine ⟨⟨k * d, ih hd⟩, ?_⟩
      rw [hn]
      exact smul_deriv h_F.deriv

/-- Addition of Derivative Expression -/
theorem DerivExpr.Add
  : D (f + g) x₀ =. D f x₀ + D g x₀
:= script
  calc
    _  =  lim x₀ fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          + lim x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_add
    _  =  D f x₀ + D g x₀
          := rfl

/-- Addition of Derivative -/
theorem Deriv.Add
  : Deriv F x₀ D₁ → Deriv G x₀ D₂ → Deriv (F + G) x₀ (D₁ + D₂)
:= script
  intro h_F h_G
  use_expr
  | calculation => calc
      D (F + G).map x₀ =. D F.map x₀ + D G.map x₀
                          := DerivExpr.Add
      _                =  the D₁ + the D₂
                          := by poly_rw [h_F.toDerivExpr, h_G.toDerivExpr]
      _                =  the (D₁ + D₂)
                          := by rfl
  | side =>
    unpack_and ⟨h_nbhd₁, h⟩ := h_F
    obtain_exist ⟨δ₁, h_δ₁, h_dom₁⟩ := h_nbhd₁
    unpack_and ⟨h_nbhd₂, h⟩ := h_G
    obtain_exist ⟨δ₂, h_δ₂, h_dom₂⟩ := h_nbhd₂
    exists min δ₁ δ₂ with lt_min h_δ₁ h_δ₂
    intro x
    intro hx
    unpack_and ⟨hx_lower, hx_upper, hx_ne⟩ := hx
    split_and
    | left =>
      claim h_x₁ : x ∈ Nbhd x₀ δ₁
      | proof =>
        split_and!
        · linarith [min_le_left δ₁ δ₂]
        · linarith [min_le_left δ₁ δ₂]
        · exact hx_ne
      have h_dom := h_dom₁ h_x₁
      exact_proj h_dom
    | right =>
      claim h_x₂ : x ∈ Nbhd x₀ δ₂
      | proof =>
        split_and!
        · linarith [min_le_right δ₁ δ₂]
        · linarith [min_le_right δ₁ δ₂]
        · exact hx_ne
      have h_dom := h_dom₂ h_x₂
      exact_proj h_dom

/-- Addition of Left Derivative Expression -/
theorem LeftDerivExpr.Add
  : D₋ (f + g) x₀ =. D₋ f x₀ + D₋ g x₀
:= script
  calc
    _  =  lim₋ x₀ fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)
          := rfl
    _  =  lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          + lim₋ x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_add
    _  =  D₋ f x₀ + D₋ g x₀
          := rfl

/-- Addition of Left Derivative -/
theorem LeftDeriv.Add
  : LeftDeriv F x₀ D₁ → LeftDeriv G x₀ D₂ → LeftDeriv (F + G) x₀ (D₁ + D₂)
:= by
  intro h_F h_G
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation => calc
      D₋ (F + G).map x₀ =. D₋ F.map x₀ + D₋ G.map x₀ := LeftDerivExpr.Add
      _ = the D₁ + the D₂ := by poly_rw [h_F.toLeftDerivExpr, h_G.toLeftDerivExpr]
      _ = the (D₁ + D₂) := rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, h_dom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, h_dom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      exact ⟨(h_dom₁ ⟨by linarith [hx.1, min_le_left δ₁ δ₂], hx.2⟩).1.1.1,
        (h_dom₂ ⟨by linarith [hx.1, min_le_right δ₁ δ₂], hx.2⟩).1.1.1⟩

/-- Addition of Right Derivative Expression -/
theorem RightDerivExpr.Add
  : D₊ (f + g) x₀ =. D₊ f x₀ + D₊ g x₀
:= script
  calc
    _  =  lim₊ x₀ fun x ↦ ((f x + g x) - (f x₀ + g x₀)) / (x - x₀)
          := rfl
    _  =  lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀) + (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          + lim₊ x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_add
    _  =  D₊ f x₀ + D₊ g x₀
          := rfl

/-- Addition of Right Derivative -/
theorem RightDeriv.Add
  : RightDeriv F x₀ D₁ → RightDeriv G x₀ D₂ → RightDeriv (F + G) x₀ (D₁ + D₂)
:= by
  intro h_F h_G
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation => calc
      D₊ (F + G).map x₀ =. D₊ F.map x₀ + D₊ G.map x₀ := RightDerivExpr.Add
      _ = the D₁ + the D₂ := by poly_rw [h_F.toRightDerivExpr, h_G.toRightDerivExpr]
      _ = the (D₁ + D₂) := rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, h_dom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, h_dom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      exact ⟨(h_dom₁ ⟨hx.1, by linarith [hx.2, min_le_left δ₁ δ₂]⟩).1.1.1,
        (h_dom₂ ⟨hx.1, by linarith [hx.2, min_le_right δ₁ δ₂]⟩).1.1.1⟩

/-- Addition of N-th Order Derivative -/
theorem NthDeriv.Add
  : NthDeriv n F x₀ D₁ → NthDeriv n G x₀ D₂ → NthDeriv n (F + G) x₀ (D₁ + D₂)
:= sorry

/-- Additive Inverse of Derivative Expression -/
theorem DerivExpr.Neg
  : D (-f) x₀ =. - D f x₀
:= script
  calc
    _  =  lim x₀ fun x ↦ (- f x - (- f x₀)) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ - ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. - lim x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_neg
    _  =  - D f x₀
          := rfl

/-- Additive Inverse of Derivative -/
theorem Deriv.Neg
    (h_F : Deriv F x₀ D₁)
  : Deriv (-F) x₀ (-D₁)
:= by
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation => calc
      D (-F).map x₀ =. - D F.map x₀ := DerivExpr.Neg
      _ = - the D₁ := by poly_rw [h_F.toDerivExpr]
      _ = the (-D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Additive Inverse of Left Derivative Expression -/
theorem LeftDerivExpr.Neg
  : D₋ (-f) x₀ =. - D₋ f x₀
:= script
  calc
    _  =  lim₋ x₀ fun x ↦ (- f x - (- f x₀)) / (x - x₀)
          := rfl
    _  =  lim₋ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. - lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_neg
    _  =  - D₋ f x₀
          := rfl

/-- Additive Inverse of Left Derivative -/
theorem LeftDeriv.Neg
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (-F) x₀ (-D₁)
:= by
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation => calc
      D₋ (-F).map x₀ =. - D₋ F.map x₀ := LeftDerivExpr.Neg
      _ = - the D₁ := by poly_rw [h_F.toLeftDerivExpr]
      _ = the (-D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Additive Inverse of Right Derivative Expression -/
theorem RightDerivExpr.Neg
  : D₊ (-f) x₀ =. - D₊ f x₀
:= script
  calc
    _  =  lim₊ x₀ fun x ↦ (- f x - (- f x₀)) / (x - x₀)
          := rfl
    _  =  lim₊ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀))
          := by lim_congr 1; ring
    _  =. - lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀)
          := by lim_neg
    _  =  - D₊ f x₀
          := rfl

/-- Additive Inverse of Right Derivative -/
theorem RightDeriv.Neg
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (-F) x₀ (-D₁)
:= by
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation => calc
      D₊ (-F).map x₀ =. - D₊ F.map x₀ := RightDerivExpr.Neg
      _ = - the D₁ := by poly_rw [h_F.toRightDerivExpr]
      _ = the (-D₁) := rfl
  case side =>
      rcases h_F.1 with ⟨δ, hδ, h_dom⟩
      exact ⟨δ, hδ, fun _ hx => (h_dom hx).1.1.1⟩

/-- Additive Inverse of N-th Order Derivative -/
theorem NthDeriv.Neg
    (h_F : NthDeriv n F x₀ D₁)
  : NthDeriv n (-F) x₀ (-D₁)
:= by
  have heq : (-1 : ℝ) • F = -F := by
    apply RFunction.ext
    · funext x
      change -1 * F.map x = -F.map x
      ring
    · rfl
  simpa only [heq, neg_one_mul] using (h_F.SMul (k := -1))

/-- Subtraction of Derivative Expression -/
theorem DerivExpr.Sub
  : D (f - g) x₀ =. D f x₀ - D g x₀
:= script
  calc
    _  =  lim x₀ fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          - lim x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_sub
    _  =  D f x₀ - D g x₀
          := rfl

/-- Subtraction of Derivative -/
theorem Deriv.Sub
  : Deriv F x₀ D₁ → Deriv G x₀ D₂ → Deriv (F - G) x₀ (D₁ - D₂)
:= by
  intro h_F h_G
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation => calc
      D (F - G).map x₀ =. D F.map x₀ - D G.map x₀ := DerivExpr.Sub
      _ = the D₁ - the D₂ := by poly_rw [h_F.toDerivExpr, h_G.toDerivExpr]
      _ = the (D₁ - D₂) := rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, h_dom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, h_dom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      exact ⟨(h_dom₁ ⟨by linarith [hx.1, min_le_left δ₁ δ₂],
          by linarith [hx.2.1, min_le_left δ₁ δ₂], hx.2.2⟩).1.1.1,
        (h_dom₂ ⟨by linarith [hx.1, min_le_right δ₁ δ₂],
          by linarith [hx.2.1, min_le_right δ₁ δ₂], hx.2.2⟩).1.1.1⟩

/-- Subtraction of Left Derivative Expression -/
theorem LeftDerivExpr.Sub
  : D₋ (f - g) x₀ =. D₋ f x₀ - D₋ g x₀
:= script
  calc
    _  =  lim₋ x₀ fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)
          := rfl
    _  =  lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          - lim₋ x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_sub
    _  =  D₋ f x₀ - D₋ g x₀
          := rfl

/-- Subtraction of Left Derivative -/
theorem LeftDeriv.Sub
  : LeftDeriv F x₀ D₁ → LeftDeriv G x₀ D₂ → LeftDeriv (F - G) x₀ (D₁ - D₂)
:= by
  intro h_F h_G
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation => calc
      D₋ (F - G).map x₀ =. D₋ F.map x₀ - D₋ G.map x₀ := LeftDerivExpr.Sub
      _ = the D₁ - the D₂ := by poly_rw [h_F.toLeftDerivExpr, h_G.toLeftDerivExpr]
      _ = the (D₁ - D₂) := rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, h_dom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, h_dom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      exact ⟨(h_dom₁ ⟨by linarith [hx.1, min_le_left δ₁ δ₂], hx.2⟩).1.1.1,
        (h_dom₂ ⟨by linarith [hx.1, min_le_right δ₁ δ₂], hx.2⟩).1.1.1⟩

/-- Subtraction of Right Derivative Expression -/
theorem RightDerivExpr.Sub
  : D₊ (f - g) x₀ =. D₊ f x₀ - D₊ g x₀
:= script
  calc
    _  =  lim₊ x₀ fun x ↦ ((f x - g x) - (f x₀ - g x₀)) / (x - x₀)
          := rfl
    _  =  lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀) - (g x - g x₀) / (x - x₀)
          := by lim_congr 1; ring
    _  =. (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
          - lim₊ x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_sub
    _  =  D₊ f x₀ - D₊ g x₀
          := rfl

/-- Subtraction of Right Derivative -/
theorem RightDeriv.Sub
  : RightDeriv F x₀ D₁ → RightDeriv G x₀ D₂ → RightDeriv (F - G) x₀ (D₁ - D₂)
:= by
  intro h_F h_G
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation => calc
      D₊ (F - G).map x₀ =. D₊ F.map x₀ - D₊ G.map x₀ := RightDerivExpr.Sub
      _ = the D₁ - the D₂ := by poly_rw [h_F.toRightDerivExpr, h_G.toRightDerivExpr]
      _ = the (D₁ - D₂) := rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, h_dom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, h_dom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      exact ⟨(h_dom₁ ⟨hx.1, by linarith [hx.2, min_le_left δ₁ δ₂]⟩).1.1.1,
        (h_dom₂ ⟨hx.1, by linarith [hx.2, min_le_right δ₁ δ₂]⟩).1.1.1⟩

/-- Subtraction of N-th Order Derivative -/
theorem NthDeriv.Sub
  : NthDeriv n F x₀ D₁ → NthDeriv n G x₀ D₂ → NthDeriv n (F - G) x₀ (D₁ - D₂)
:= sorry

/-- Multiplication of Derivative Expression -/
theorem DerivExpr.Mul
  : D (f * g) x₀ =? D f x₀ * the (g x₀) + D g x₀ * the (f x₀)
:= script
  intro h_proper
  claim h_Df : ∃ a, D f x₀ =. the a
  | proof => proper_reflect
  calc
    _  =  lim x₀ fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)
          := rfl
    _  =  lim x₀ fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x
          := by lim_congr 1; ring
    _  =. (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀) * g x₀)
            + lim x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_add
    _  =. (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + lim x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_smul
    _  =. (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + (lim x₀ fun x ↦ (g x - g x₀) / (x - x₀)) * lim x₀ f
          := by lim_mul
    _  =  D f x₀ * the (g x₀) + D g x₀ * the (f x₀)
          := by poly_rw [toCont h_Df]

/-- Multiplication of Derivative -/
theorem Deriv.Mul
  : Deriv F x₀ D₁ → Deriv G x₀ D₂
    → Deriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= by
  intro h_F h_G
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D (F * G).map x₀ =? the (D₁ * G.map x₀ + F.map x₀ * D₂) from h trivial
    calc
      D (F * G).map x₀ =? D F.map x₀ * the (G.map x₀) + D G.map x₀ * the (F.map x₀)
                          := DerivExpr.Mul
      _ =. the (D₁ * G.map x₀ + F.map x₀ * D₂) := by
        poly_rw [h_F.toDerivExpr, h_G.toDerivExpr]
        simp only [finite_mul, finite_add, mul_comm D₂]
        rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, hdom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, hdom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      have hx₁ : x ∈ Nbhd x₀ δ₁ :=
        ⟨by linarith [hx.1, min_le_left δ₁ δ₂],
          by linarith [hx.2.1, min_le_left δ₁ δ₂], hx.2.2⟩
      have hx₂ : x ∈ Nbhd x₀ δ₂ :=
        ⟨by linarith [hx.1, min_le_right δ₁ δ₂],
          by linarith [hx.2.1, min_le_right δ₁ δ₂], hx.2.2⟩
      exact ⟨(hdom₁ hx₁).1.1.1, (hdom₂ hx₂).1.1.1⟩

/-- Multiplication of Left Derivative Expression -/
theorem LeftDerivExpr.Mul
  : D₋ (f * g) x₀ =? D₋ f x₀ * the (g x₀) + D₋ g x₀ * the (f x₀)
:= script
  intro h_proper
  claim h_Df : ∃ a, D₋ f x₀ =. the a
  | proof => proper_reflect
  calc
    _  =  lim₋ x₀ fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)
          := rfl
    _  =  lim₋ x₀ fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x
          := by lim_congr 1; ring
    _  =. (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀) * g x₀)
            + lim₋ x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_add
    _  =. (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + lim₋ x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_smul
    _  =. (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + (lim₋ x₀ fun x ↦ (g x - g x₀) / (x - x₀)) * lim₋ x₀ f
          := by lim_mul
    _  =  D₋ f x₀ * the (g x₀) + D₋ g x₀ * the (f x₀)
          := by poly_rw [toCont h_Df]

/-- Multiplication of Left Derivative -/
theorem LeftDeriv.Mul
  : LeftDeriv F x₀ D₁ → LeftDeriv G x₀ D₂
    → LeftDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= by
  intro h_F h_G
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₋ (F * G).map x₀ =? the (D₁ * G.map x₀ + F.map x₀ * D₂) from h trivial
    calc
      D₋ (F * G).map x₀ =? D₋ F.map x₀ * the (G.map x₀) + D₋ G.map x₀ * the (F.map x₀)
                           := LeftDerivExpr.Mul
      _ =. the (D₁ * G.map x₀ + F.map x₀ * D₂) := by
        poly_rw [h_F.toLeftDerivExpr, h_G.toLeftDerivExpr]
        simp only [finite_mul, finite_add, mul_comm D₂]
        rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, hdom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, hdom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      have hx₁ : x ∈ Ioo (x₀ - δ₁) x₀ :=
        ⟨by linarith [hx.1, min_le_left δ₁ δ₂], hx.2⟩
      have hx₂ : x ∈ Ioo (x₀ - δ₂) x₀ :=
        ⟨by linarith [hx.1, min_le_right δ₁ δ₂], hx.2⟩
      exact ⟨(hdom₁ hx₁).1.1.1, (hdom₂ hx₂).1.1.1⟩

/-- Multiplication of Right Derivative Expression -/
theorem RightDerivExpr.Mul
  : D₊ (f * g) x₀ =? D₊ f x₀ * the (g x₀) + D₊ g x₀ * the (f x₀)
:= script
  intro h_proper
  claim h_Df : ∃ a, D₊ f x₀ =. the a
  | proof => proper_reflect
  calc
    _  =  lim₊ x₀ fun x ↦ ((f x * g x) - (f x₀ * g x₀)) / (x - x₀)
          := rfl
    _  =  lim₊ x₀ fun x ↦
            (f x - f x₀) / (x - x₀) * g x₀ + (g x - g x₀) / (x - x₀) * f x
          := by lim_congr 1; ring
    _  =. (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀) * g x₀)
            + lim₊ x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_add
    _  =. (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + lim₊ x₀ fun x ↦ (g x - g x₀) / (x - x₀) * f x
          := by lim_smul
    _  =. (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀)) * the (g x₀)
            + (lim₊ x₀ fun x ↦ (g x - g x₀) / (x - x₀)) * lim₊ x₀ f
          := by lim_mul
    _  =  D₊ f x₀ * the (g x₀) + D₊ g x₀ * the (f x₀)
          := by poly_rw [toCont h_Df]

/-- Multiplication of Right Derivative -/
theorem RightDeriv.Mul
  : RightDeriv F x₀ D₁ → RightDeriv G x₀ D₂
    → RightDeriv (F * G) x₀ (D₁ * G.map x₀ + F.map x₀ * D₂)
:= by
  intro h_F h_G
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₊ (F * G).map x₀ =? the (D₁ * G.map x₀ + F.map x₀ * D₂) from h trivial
    calc
      D₊ (F * G).map x₀ =? D₊ F.map x₀ * the (G.map x₀) + D₊ G.map x₀ * the (F.map x₀)
                           := RightDerivExpr.Mul
      _ =. the (D₁ * G.map x₀ + F.map x₀ * D₂) := by
        poly_rw [h_F.toRightDerivExpr, h_G.toRightDerivExpr]
        simp only [finite_mul, finite_add, mul_comm D₂]
        rfl
  case side =>
      rcases h_F.1 with ⟨δ₁, hδ₁, hdom₁⟩
      rcases h_G.1 with ⟨δ₂, hδ₂, hdom₂⟩
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro x hx
      have hx₁ : x ∈ Ioo x₀ (x₀ + δ₁) :=
        ⟨hx.1, by linarith [hx.2, min_le_left δ₁ δ₂]⟩
      have hx₂ : x ∈ Ioo x₀ (x₀ + δ₂) :=
        ⟨hx.1, by linarith [hx.2, min_le_right δ₁ δ₂]⟩
      exact ⟨(hdom₁ hx₁).1.1.1, (hdom₂ hx₂).1.1.1⟩

/-- Multiplicative Scalar Power of Derivative Expression -/
theorem DerivExpr.MSPow
  : D (f ^ n) x₀ =? the n * D f x₀ * the (f x₀ ^ (n - 1))
:= script
  induction n
  | zero =>
    intro an
    claim hf_proper : ∃ a, D f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      D (f ^ 0) x₀ =  D (fun _ ↦ 1) x₀
                      := rfl
      _            =  lim x₀ fun _ ↦ 0
                      := by lim_congr 1; norm_num
      _            =  the 0
                      := by lim_cont
      _            =. the (0 : ℕ) * D f x₀ * the (f x₀ ^ (0 - 1))
                      := by
                        poly_rw [hD₁]
                        simp only [Nat.cast_zero, Nat.zero_sub, pow_zero,
                          finite_mul, zero_mul]
                        rfl
  | succ n ih =>
    intro_proper' h_proper
    claim hf_proper : ∃ a, D f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      _  =? D (f ^ n) x₀ * the (f x₀) + D f x₀ * the (f x₀ ^ n)
            := Mul
      _  =? (the n * D f x₀ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            D f x₀ * the (f x₀ ^ n)
            := by
              intro h_step
              gcongr
              apply ih
              poly_rw [hD₁]
              trivial
      _  =  (the n * the D₁ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            the D₁ * the (f x₀ ^ n)
            := by poly_rw [hD₁]
      _  =  the n * D f x₀ * the (f x₀ ^ (n + 1 - 1))
              + D f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [Nat.add_sub_cancel, finite_mul, finite_add]
              by_cases hn : n = 0
              · subst n
                norm_num
              · have hn_pow : f x₀ ^ (n - 1) * f x₀ = f x₀ ^ n := by
                  nth_rewrite 2 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
                  rw [pow_succ]
                rw [mul_assoc, hn_pow]
      _  =  the n * D f x₀ * the (f x₀ ^ (n + 1 - 1))
              + the 1 * D f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_mul, one_mul]
      _  =  the (n + 1 : ℕ) * D f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_add, finite_mul]
              norm_num
              ring

/-- Multiplicative Scalar Power of Derivative -/
theorem Deriv.MSPow
    (h_F : Deriv F x₀ D₁)
  : Deriv (F ^ n) x₀ (n * D₁ * F.map x₀ ^ (n - 1))
:= by
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D (F ^ n).map x₀ =? the (n * D₁ * F.map x₀ ^ (n - 1)) from h trivial
    calc
      D (F ^ n).map x₀ =? the n * D F.map x₀ * the (F.map x₀ ^ (n - 1))
                          := DerivExpr.MSPow
      _ =. the (n * D₁ * F.map x₀ ^ (n - 1)) := by
        poly_rw [h_F.toDerivExpr]
  case side =>
      rcases h_F.1 with ⟨δ, hδ, hdom⟩
      exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩

/-- Multiplicative Scalar Power of Left Derivative Expression -/
theorem LeftDerivExpr.MSPow
  : D₋ (f ^ n) x₀ =? the n * D₋ f x₀ * the (f x₀ ^ (n - 1))
:= script
  induction n
  | zero =>
    intro an
    claim hf_proper : ∃ a, D₋ f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      D₋ (f ^ 0) x₀  =  D₋ (fun _ ↦ 1) x₀
                        := rfl
      _              =  lim₋ x₀ fun _ ↦ 0
                        := by lim_congr 1; norm_num
      _              =  the 0
                        := by lim_cont
      _              =. the (0 : ℕ) * D₋ f x₀ * the (f x₀ ^ (0 - 1))
                        := by
                          poly_rw [hD₁]
                          simp only [Nat.cast_zero, Nat.zero_sub, pow_zero,
                            finite_mul, zero_mul]
                          rfl
  | succ n ih =>
    intro_proper' h_proper
    claim hf_proper : ∃ a, D₋ f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      _  =? D₋ (f ^ n) x₀ * the (f x₀) + D₋ f x₀ * the (f x₀ ^ n)
            := Mul
      _  =? (the n * D₋ f x₀ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            D₋ f x₀ * the (f x₀ ^ n)
            := by
              intro h_step
              gcongr
              apply ih
              poly_rw [hD₁]
              trivial
      _  =  (the n * the D₁ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            the D₁ * the (f x₀ ^ n)
            := by poly_rw [hD₁]
      _  =  the n * D₋ f x₀ * the (f x₀ ^ (n + 1 - 1))
              + D₋ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [Nat.add_sub_cancel, finite_mul, finite_add]
              by_cases hn : n = 0
              · subst n
                norm_num
              · have hn_pow : f x₀ ^ (n - 1) * f x₀ = f x₀ ^ n := by
                  nth_rewrite 2 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
                  rw [pow_succ]
                rw [mul_assoc, hn_pow]
      _  =  the n * D₋ f x₀ * the (f x₀ ^ (n + 1 - 1))
              + the 1 * D₋ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_mul, one_mul]
      _  =  the (n + 1 : ℕ) * D₋ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_add, finite_mul]
              norm_num
              ring

/-- Multiplicative Scalar Power of Left Derivative -/
theorem LeftDeriv.MSPow
    (h_F : LeftDeriv F x₀ D₁)
  : LeftDeriv (F ^ n) x₀ (n * D₁ * F.map x₀ ^ (n - 1))
:= by
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₋ (F ^ n).map x₀ =? the (n * D₁ * F.map x₀ ^ (n - 1)) from h trivial
    calc
      D₋ (F ^ n).map x₀ =? the n * D₋ F.map x₀ * the (F.map x₀ ^ (n - 1))
                           := LeftDerivExpr.MSPow
      _ =. the (n * D₁ * F.map x₀ ^ (n - 1)) := by
        poly_rw [h_F.toLeftDerivExpr]
  case side =>
      rcases h_F.1 with ⟨δ, hδ, hdom⟩
      exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩

/-- Multiplicative Scalar Power of Right Derivative Expression -/
theorem RightDerivExpr.MSPow
  : D₊ (f ^ n) x₀ =? the n * D₊ f x₀ * the (f x₀ ^ (n - 1))
:= script
  induction n
  | zero =>
    intro an
    claim hf_proper : ∃ a, D₊ f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      D₊ (f ^ 0) x₀  =  D₊ (fun _ ↦ 1) x₀
                        := rfl
      _              =  lim₊ x₀ fun _ ↦ 0
                        := by lim_congr 1; norm_num
      _              =  the 0
                        := by lim_cont
      _              =. the (0 : ℕ) * D₊ f x₀ * the (f x₀ ^ (0 - 1))
                        := by
                          poly_rw [hD₁]
                          simp only [Nat.cast_zero, Nat.zero_sub, pow_zero,
                            finite_mul, zero_mul]
                          rfl
  | succ n ih =>
    intro_proper' h_proper
    claim hf_proper : ∃ a, D₊ f x₀ =. the a
    | proof => proper_reflect
    obtain_exist ⟨D₁, hD₁⟩ := hf_proper
    calc
      _  =? D₊ (f ^ n) x₀ * the (f x₀) + D₊ f x₀ * the (f x₀ ^ n)
            := Mul
      _  =? (the n * D₊ f x₀ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            D₊ f x₀ * the (f x₀ ^ n)
            := by
              intro h_step
              gcongr
              apply ih
              poly_rw [hD₁]
              trivial
      _  =  (the n * the D₁ * the (f x₀ ^ (n - 1))) * the (f x₀) +
            the D₁ * the (f x₀ ^ n)
            := by poly_rw [hD₁]
      _  =  the n * D₊ f x₀ * the (f x₀ ^ (n + 1 - 1))
              + D₊ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [Nat.add_sub_cancel, finite_mul, finite_add]
              by_cases hn : n = 0
              · subst n
                norm_num
              · have hn_pow : f x₀ ^ (n - 1) * f x₀ = f x₀ ^ n := by
                  nth_rewrite 2 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
                  rw [pow_succ]
                rw [mul_assoc, hn_pow]
      _  =  the n * D₊ f x₀ * the (f x₀ ^ (n + 1 - 1))
              + the 1 * D₊ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_mul, one_mul]
      _  =  the (n + 1 : ℕ) * D₊ f x₀ * the (f x₀ ^ (n + 1 - 1))
            := by
              poly_rw [hD₁]
              simp only [finite_add, finite_mul]
              norm_num
              ring

/-- Multiplicative Scalar Power of Right Derivative -/
theorem RightDeriv.MSPow
    (h_F : RightDeriv F x₀ D₁)
  : RightDeriv (F ^ n) x₀ (n * D₁ * F.map x₀ ^ (n - 1))
:= by
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₊ (F ^ n).map x₀ =? the (n * D₁ * F.map x₀ ^ (n - 1)) from h trivial
    calc
      D₊ (F ^ n).map x₀ =? the n * D₊ F.map x₀ * the (F.map x₀ ^ (n - 1))
                           := RightDerivExpr.MSPow
      _ =. the (n * D₁ * F.map x₀ ^ (n - 1)) := by
        poly_rw [h_F.toRightDerivExpr]
  case side =>
      rcases h_F.1 with ⟨δ, hδ, hdom⟩
      exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩

/-- Multiplicative Inverse of Derivative Expression -/
theorem DerivExpr.Inv
  : D f⁻¹ x₀ =? - D f x₀ / the (f x₀ ^ 2)
:= script
  intro h_proper
  claim hf_proper : ∃ a, D f x₀ =. the a
  | proof => proper_reflect
  claim hf0 : f x₀ ≠ 0
  | proof => proper_reflect
  claim h_f_ne0 : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≠ 0
  | proof => infer
    ∃ a, D f x₀ =. the a => lim x₀ f =. the (f x₀)
                            := toCont hf_proper
                         => FuncLimit ⟨f, Iii⟩ x₀ (f x₀)
                            := FuncLimit.fromFuncLimitExpr ⟨1, zero_lt_one, subset_univ _⟩ ?_
                         => ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x ≠ 0
                            := FuncLimit.LocallyNeZero ?_ hf0
  obtain_exist ⟨δ, hδ, hf_ne⟩ := h_f_ne0
  calc
    _  =  lim x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)) / (f x * f x₀)
          := by
            lim_congr' δ
            func_apply
            field [hf_ne]
    _  =. (lim x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)))
            / lim x₀ fun x ↦ f x * f x₀
          := by lim_div
    _  =. - (lim x₀ fun x ↦ (f x - f x₀) / (x - x₀))
            / lim x₀ fun x ↦ f x * f x₀
          := by lim_neg
    _  =  - D f x₀ / lim x₀ fun x ↦ f x * f x₀
          := rfl
    _  =. - D f x₀ / (lim x₀ f * the (f x₀))
          := by lim_smul
    _  =  - D f x₀ / (the (f x₀) * the (f x₀))
          := by poly_rw [toCont hf_proper]
    _  =  - D f x₀ / the (f x₀ ^ 2)
          := by rw [finite_mul]; ring_nf

/-- Multiplicative Inverse of Derivative -/
theorem Deriv.Inv
    (h_F : Deriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : Deriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= by
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D F⁻¹.map x₀ =? the (-D₁ / F.map x₀ ^ 2) from h trivial
    calc
      D F⁻¹.map x₀ =? - D F.map x₀ / the (F.map x₀ ^ 2) := DerivExpr.Inv
      _ =. the (-D₁ / F.map x₀ ^ 2) := by
        poly_rw [h_F.toDerivExpr]
        exact finite_div (pow_ne_zero 2 h_F_ne0)
  case side =>
      have h_cont : FuncLimit F x₀ (F.map x₀) := by
        apply FuncLimit.fromFuncLimitExpr
        · rcases h_F.1 with ⟨δ, hδ, hdom⟩
          exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩
        · exact DerivExpr.toCont ⟨D₁, h_F.toDerivExpr⟩
      exact (FuncLimit.Inv h_F_ne0 h_cont).1

/-- Multiplicative Inverse of Left Derivative Expression -/
theorem LeftDerivExpr.Inv
  : D₋ f⁻¹ x₀ =? - D₋ f x₀ / the (f x₀ ^ 2)
:= script
  intro h_proper
  claim hf_proper : ∃ a, D₋ f x₀ =. the a
  | proof => proper_reflect
  claim hf0 : f x₀ ≠ 0
  | proof => proper_reflect
  claim h_f_ne0 : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x ≠ 0
  | proof => infer
    ∃ a, D₋ f x₀ =. the a  => lim₋ x₀ f =. the (f x₀)
                              := toCont hf_proper
                           => LeftLimit ⟨f, Iii⟩ x₀ (f x₀)
                              := LeftLimit.fromLeftLimitExpr ⟨1, zero_lt_one, subset_univ _⟩ ?_
                           => ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x ≠ 0
                              := LeftLimit.LocallyNeZero ?_ hf0
  obtain_exist ⟨δ, hδ, hf_ne⟩ := h_f_ne0
  calc
    _  =  lim₋ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)) / (f x * f x₀)
          := by
            lim_congr' δ
            func_apply
            field [hf_ne]
    _  =. (lim₋ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)))
            / lim₋ x₀ fun x ↦ f x * f x₀
          := by lim_div
    _  =. - (lim₋ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
            / lim₋ x₀ fun x ↦ f x * f x₀
          := by lim_neg
    _  =  - D₋ f x₀ / lim₋ x₀ fun x ↦ f x * f x₀
          := rfl
    _  =. - D₋ f x₀ / (lim₋ x₀ f * the (f x₀))
          := by lim_smul
    _  =  - D₋ f x₀ / (the (f x₀) * the (f x₀))
          := by poly_rw [toCont hf_proper]
    _  =  - D₋ f x₀ / the (f x₀ ^ 2)
          := by rw [finite_mul]; ring_nf

/-- Multiplicative Inverse of Left Derivative -/
theorem LeftDeriv.Inv
    (h_F : LeftDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : LeftDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= by
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₋ F⁻¹.map x₀ =? the (-D₁ / F.map x₀ ^ 2) from h trivial
    calc
      D₋ F⁻¹.map x₀ =? - D₋ F.map x₀ / the (F.map x₀ ^ 2) := LeftDerivExpr.Inv
      _ =. the (-D₁ / F.map x₀ ^ 2) := by
        poly_rw [h_F.toLeftDerivExpr]
        exact finite_div (pow_ne_zero 2 h_F_ne0)
  case side =>
      have h_cont : LeftLimit F x₀ (F.map x₀) := by
        apply LeftLimit.fromLeftLimitExpr
        · rcases h_F.1 with ⟨δ, hδ, hdom⟩
          exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩
        · exact LeftDerivExpr.toCont ⟨D₁, h_F.toLeftDerivExpr⟩
      exact (LeftLimit.Inv h_F_ne0 h_cont).1

/-- Multiplicative Inverse of Right Derivative Expression -/
theorem RightDerivExpr.Inv
  : D₊ f⁻¹ x₀ =? - D₊ f x₀ / the (f x₀ ^ 2)
:= script
  intro h_proper
  claim hf_proper : ∃ a, D₊ f x₀ =. the a
  | proof => proper_reflect
  claim hf0 : f x₀ ≠ 0
  | proof => proper_reflect
  claim h_f_ne0 : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x ≠ 0
  | proof => infer
    ∃ a, D₊ f x₀ =. the a  => lim₊ x₀ f =. the (f x₀)
                              := toCont hf_proper
                           => RightLimit ⟨f, Iii⟩ x₀ (f x₀)
                              := RightLimit.fromRightLimitExpr ⟨1, zero_lt_one, subset_univ _⟩ ?_
                           => ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x ≠ 0
                              := RightLimit.LocallyNeZero ?_ hf0
  obtain_exist ⟨δ, hδ, hf_ne⟩ := h_f_ne0
  calc
    _  =  lim₊ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)) / (f x * f x₀)
          := by
            lim_congr' δ
            func_apply
            field [hf_ne]
    _  =. (lim₊ x₀ fun x ↦ - ((f x - f x₀) / (x - x₀)))
            / lim₊ x₀ fun x ↦ f x * f x₀
          := by lim_div
    _  =. - (lim₊ x₀ fun x ↦ (f x - f x₀) / (x - x₀))
            / lim₊ x₀ fun x ↦ f x * f x₀
          := by lim_neg
    _  =  - D₊ f x₀ / lim₊ x₀ fun x ↦ f x * f x₀
          := rfl
    _  =. - D₊ f x₀ / (lim₊ x₀ f * the (f x₀))
          := by lim_smul
    _  =  - D₊ f x₀ / (the (f x₀) * the (f x₀))
          := by poly_rw [toCont hf_proper]
    _  =  - D₊ f x₀ / the (f x₀ ^ 2)
          := by rw [finite_mul]; ring_nf

/-- Multiplicative Inverse of Right Derivative -/
theorem RightDeriv.Inv
    (h_F : RightDeriv F x₀ D₁)
    (h_F_ne0 : F.map x₀ ≠ 0)
  : RightDeriv F⁻¹ x₀ (-D₁ / F.map x₀ ^ 2)
:= by
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₊ F⁻¹.map x₀ =? the (-D₁ / F.map x₀ ^ 2) from h trivial
    calc
      D₊ F⁻¹.map x₀ =? - D₊ F.map x₀ / the (F.map x₀ ^ 2) := RightDerivExpr.Inv
      _ =. the (-D₁ / F.map x₀ ^ 2) := by
        poly_rw [h_F.toRightDerivExpr]
        exact finite_div (pow_ne_zero 2 h_F_ne0)
  case side =>
      have h_cont : RightLimit F x₀ (F.map x₀) := by
        apply RightLimit.fromRightLimitExpr
        · rcases h_F.1 with ⟨δ, hδ, hdom⟩
          exact ⟨δ, hδ, fun _ hx => (hdom hx).1.1.1⟩
        · exact RightDerivExpr.toCont ⟨D₁, h_F.toRightDerivExpr⟩
      exact (RightLimit.Inv h_F_ne0 h_cont).1

/-- Division of Derivative Expression -/
theorem DerivExpr.Div
  : D (f / g) x₀ =? (D f x₀ * the (g x₀) - D g x₀ * the (f x₀)) / the (g x₀ ^ 2)
:= script
  intro_proper' h_proper
  claim hf_proper : ∃ a, D f x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Df, hDf⟩ := hf_proper
  claim hg_proper : ∃ a, D g x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Dg, hDg⟩ := hg_proper
  claim h_den_ne0 : g x₀ ^ 2 ≠ 0
  | proof => proper_reflect
  calc
    _  =  D (f * g⁻¹) x₀
          := rfl
    _  =? D f x₀ * the ((g⁻¹) x₀) + D g⁻¹ x₀ * the (f x₀)
          := Mul
    _  =? D f x₀ * the ((g⁻¹) x₀) + (- D g x₀ / the (g x₀ ^ 2)) * the (f x₀)
          := by
            intro _
            gcongr
            apply Inv
            poly_rw [hDg]
            change (the (-Dg) / the (g x₀ ^ 2)).isProper
            poly_rw [finite_div h_den_ne0]
            trivial
    _  =  D f x₀ * the ((g⁻¹) x₀) + (- the Dg / the (g x₀ ^ 2)) * the (f x₀)
          := by poly_rw [hDg]
    _  =  D f x₀ * the ((g⁻¹) x₀) + (the (-Dg) / the (g x₀ ^ 2)) * the (f x₀)
          := rfl
    _  =  D f x₀ * the ((g⁻¹) x₀) + the (-Dg / g x₀ ^ 2) * the (f x₀)
          := by poly_rw [finite_div h_den_ne0]
    _  =  (D f x₀ * the (g x₀) - D g x₀ * the (f x₀)) / the (g x₀ ^ 2)
          := by
            func_apply
            poly_rw [hDf, hDg]
            simp only [finite_add, finite_mul, finite_sub]
            poly_rw [finite_div h_den_ne0]
            congr 1
            field

/-- Division of Derivative -/
theorem Deriv.Div
    (h_G_ne0 : G.map x₀ ≠ 0)
  : Deriv F x₀ D₁ → Deriv G x₀ D₂
    → Deriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= by
  intro h_F h_G
  refine Deriv.fromDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D (F / G).map x₀ =?
        the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) from h trivial
    calc
      D (F / G).map x₀ =? (D F.map x₀ * the (G.map x₀) -
          D G.map x₀ * the (F.map x₀)) / the (G.map x₀ ^ 2) := DerivExpr.Div
      _ =. the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) := by
        poly_rw [h_F.toDerivExpr, h_G.toDerivExpr]
        simp only [finite_mul, finite_sub, mul_comm D₂]
        exact finite_div (pow_ne_zero 2 h_G_ne0)
  case side =>
      rcases (h_F.Mul (h_G.Inv h_G_ne0)).1 with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, ?_⟩
      intro x hx
      have h := (hdom hx).1.1.1
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Division of Left Derivative Expression -/
theorem LeftDerivExpr.Div
  : D₋ (f / g) x₀ =? (D₋ f x₀ * the (g x₀) - D₋ g x₀ * the (f x₀)) / the (g x₀ ^ 2)
:= script
  intro_proper' h_proper
  claim hf_proper : ∃ a, D₋ f x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Df, hDf⟩ := hf_proper
  claim hg_proper : ∃ a, D₋ g x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Dg, hDg⟩ := hg_proper
  claim h_den_ne0 : g x₀ ^ 2 ≠ 0
  | proof => proper_reflect
  calc
    _  =  D₋ (f * g⁻¹) x₀
          := rfl
    _  =? D₋ f x₀ * the ((g⁻¹) x₀) + D₋ g⁻¹ x₀ * the (f x₀)
          := Mul
    _  =? D₋ f x₀ * the ((g⁻¹) x₀) + (- D₋ g x₀ / the (g x₀ ^ 2)) * the (f x₀)
          := by
            intro _
            gcongr
            apply Inv
            poly_rw [hDg]
            change (the (-Dg) / the (g x₀ ^ 2)).isProper
            poly_rw [finite_div h_den_ne0]
            trivial
    _  =  D₋ f x₀ * the ((g⁻¹) x₀) + (- the Dg / the (g x₀ ^ 2)) * the (f x₀)
          := by poly_rw [hDg]
    _  =  D₋ f x₀ * the ((g⁻¹) x₀) + (the (-Dg) / the (g x₀ ^ 2)) * the (f x₀)
          := rfl
    _  =  D₋ f x₀ * the ((g⁻¹) x₀) + the (-Dg / g x₀ ^ 2) * the (f x₀)
          := by poly_rw [finite_div h_den_ne0]
    _  =  (D₋ f x₀ * the (g x₀) - D₋ g x₀ * the (f x₀)) / the (g x₀ ^ 2)
          := by
            func_apply
            poly_rw [hDf, hDg]
            simp only [finite_add, finite_mul, finite_sub]
            poly_rw [finite_div h_den_ne0]
            congr 1
            field

/-- Division of Left Derivative -/
theorem LeftDeriv.Div
    (h_G_ne0 : G.map x₀ ≠ 0)
  : LeftDeriv F x₀ D₁ → LeftDeriv G x₀ D₂
    → LeftDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= by
  intro h_F h_G
  refine LeftDeriv.fromLeftDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₋ (F / G).map x₀ =?
        the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) from h trivial
    calc
      D₋ (F / G).map x₀ =? (D₋ F.map x₀ * the (G.map x₀) -
          D₋ G.map x₀ * the (F.map x₀)) / the (G.map x₀ ^ 2) := LeftDerivExpr.Div
      _ =. the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) := by
        poly_rw [h_F.toLeftDerivExpr, h_G.toLeftDerivExpr]
        simp only [finite_mul, finite_sub, mul_comm D₂]
        exact finite_div (pow_ne_zero 2 h_G_ne0)
  case side =>
      rcases (h_F.Mul (h_G.Inv h_G_ne0)).1 with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, ?_⟩
      intro x hx
      have h := (hdom hx).1.1.1
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- Division of Left Derivative Expression -/
theorem RightDerivExpr.Div
  : D₊ (f / g) x₀ =? (D₊ f x₀ * the (g x₀) - D₊ g x₀ * the (f x₀)) / the (g x₀ ^ 2)
:= script
  intro_proper' h_proper
  claim hf_proper : ∃ a, D₊ f x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Df, hDf⟩ := hf_proper
  claim hg_proper : ∃ a, D₊ g x₀ =. the a
  | proof => proper_reflect
  obtain_exist ⟨Dg, hDg⟩ := hg_proper
  claim h_den_ne0 : g x₀ ^ 2 ≠ 0
  | proof => proper_reflect
  calc
    _  =  D₊ (f * g⁻¹) x₀
          := rfl
    _  =? D₊ f x₀ * the ((g⁻¹) x₀) + D₊ g⁻¹ x₀ * the (f x₀)
          := Mul
    _  =? D₊ f x₀ * the ((g⁻¹) x₀) + (- D₊ g x₀ / the (g x₀ ^ 2)) * the (f x₀)
          := by
            intro _
            gcongr
            apply Inv
            poly_rw [hDg]
            change (the (-Dg) / the (g x₀ ^ 2)).isProper
            poly_rw [finite_div h_den_ne0]
            trivial
    _  =  D₊ f x₀ * the ((g⁻¹) x₀) + (- the Dg / the (g x₀ ^ 2)) * the (f x₀)
          := by poly_rw [hDg]
    _  =  D₊ f x₀ * the ((g⁻¹) x₀) + (the (-Dg) / the (g x₀ ^ 2)) * the (f x₀)
          := rfl
    _  =  D₊ f x₀ * the ((g⁻¹) x₀) + the (-Dg / g x₀ ^ 2) * the (f x₀)
          := by poly_rw [finite_div h_den_ne0]
    _  =  (D₊ f x₀ * the (g x₀) - D₊ g x₀ * the (f x₀)) / the (g x₀ ^ 2)
          := by
            func_apply
            poly_rw [hDf, hDg]
            simp only [finite_add, finite_mul, finite_sub]
            poly_rw [finite_div h_den_ne0]
            congr 1
            field

/-- Division of Right Derivative -/
theorem RightDeriv.Div
    (h_G_ne0 : G.map x₀ ≠ 0)
  : RightDeriv F x₀ D₁ → RightDeriv G x₀ D₂
    → RightDeriv (F / G) x₀ ((D₁ * G.map x₀ - F.map x₀ * D₂) / (G.map x₀) ^ 2)
:= by
  intro h_F h_G
  refine RightDeriv.fromRightDerivExpr ?side ?calculation
  case calculation =>
    suffices h : D₊ (F / G).map x₀ =?
        the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) from h trivial
    calc
      D₊ (F / G).map x₀ =? (D₊ F.map x₀ * the (G.map x₀) -
          D₊ G.map x₀ * the (F.map x₀)) / the (G.map x₀ ^ 2) := RightDerivExpr.Div
      _ =. the ((D₁ * G.map x₀ - F.map x₀ * D₂) / G.map x₀ ^ 2) := by
        poly_rw [h_F.toRightDerivExpr, h_G.toRightDerivExpr]
        simp only [finite_mul, finite_sub, mul_comm D₂]
        exact finite_div (pow_ne_zero 2 h_G_ne0)
  case side =>
      rcases (h_F.Mul (h_G.Inv h_G_ne0)).1 with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, ?_⟩
      intro x hx
      have h := (hdom hx).1.1.1
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/-- (Composition) Chain Rule of Derivative Expression -/
theorem DerivExpr.Comp
  : D (f ∘ g) x₀ =? D f (g x₀) * D g x₀
:= by
  script_intro h_proper
  script_claim hf_proper : ∃ a, D f (g x₀) =. the a
  case proof => proper_reflect
  script_claim hg_proper : ∃ a, D g x₀ =. the a
  case proof => proper_reflect
  script_obtain_exist ⟨D₁, hD₁⟩ := hf_proper
  let slope (u : ℝ) : ℝ :=
    if u = g x₀ then D₁
    else (f u - f (g x₀)) / (u - g x₀)
  have h_slope_comp : lim x₀ (slope ∘ g) =. the D₁ := by
    have h_slope_lim : lim (g x₀) slope =. the (slope (g x₀)) := by
      simp only [slope]
      calc
        _ = lim (g x₀) fun u ↦ (f u - f (g x₀)) / (u - g x₀) := by
          apply FuncLimitExpr.Congr
          script_exists 1 with zero_lt_one
          intro _ hu
          simp [hu.2.2]
        _ =. the D₁ := hD₁
    simpa [slope] using
      FuncLimitExpr.CompSV (by poly_rw [toCont hg_proper]) h_slope_lim
  calc
    _  =  lim x₀ fun x ↦ slope (g x) * ((g x - g x₀) / (x - x₀))
          := by
            apply FuncLimitExpr.Congr
            script_exists 1 with zero_lt_one
            intro x hx
            by_cases hg_eq : g x = g x₀
            · simp_all only [mem_setOf_eq, ne_eq, Function.comp_apply, sub_self, zero_div, mul_zero]
            · simp only [Function.comp_apply, slope, hg_eq, ↓reduceIte]
              field
    _  =. lim x₀ (slope ∘ g) * lim x₀ fun x ↦ (g x - g x₀) / (x - x₀)
          := by lim_mul
    _  =  D f (g x₀) * D g x₀
          := by poly_rw [h_slope_comp, ← hD₁]

/-- Composition of Derivative -/
theorem Deriv.Comp {F' G' : ℝ}
    (h_G : Deriv G x₀ G') (h_F : Deriv F (G.map x₀) F')
    (h_FGx₀ : G.map x₀ ∈ F.domain)
  : Deriv (F ⊙ G) x₀ (F' * G')
:= by
  let slope : RFunction :=
    ⟨fun u ↦ if u = G.map x₀ then F' else
        (F.map u - F.map (G.map x₀)) / (u - G.map x₀),
      F.domain ∪ {G.map x₀}⟩
  have h_slope : FuncLimit slope (G.map x₀) F' := by
    apply h_F.Congr
    rcases h_F.1 with ⟨δ, hδ, hdom⟩
    script_exists δ with hδ
    constructor
    · intro u hu
      exact Or.inl (hdom hu).1.1.1
    · intro u hu
      change (F.map u - F.map (G.map x₀)) / (u - G.map x₀) = _
      simp [slope, hu.2.2]
  have h_slope_cont : slope.isContinuousAt (G.map x₀) := by
    refine ⟨Or.inr rfl, ?_⟩
    simpa [slope] using h_slope
  have h_G_cont : FuncLimit G x₀ (G.map x₀) := by
    let displacement := Identity - Constant x₀
    have h_displacement : FuncLimit displacement x₀ 0 := by
      convert FuncLimit.Sub
        (Continuity.Identity x₀ (mem_univ _)).2
        (Continuity.Constant x₀ (mem_univ _) :
          (Constant x₀).isContinuousAt x₀).2 using 1
      change 0 = x₀ - x₀
      ring
    have h_product := FuncLimit.Mul h_G h_displacement
    have h_difference : FuncLimit (G - Constant (G.map x₀)) x₀ 0 := by
      apply (show FuncLimit
        (((G - Constant (G.map x₀)) / (Identity - Constant x₀)) * displacement)
          x₀ 0 by simpa using h_product).Congr
      rcases h_G.1 with ⟨δ, hδ, hdom⟩
      refine ⟨δ, hδ, ?_, ?_⟩
      · intro x hx
        exact ⟨(hdom hx).1.1.1, trivial⟩
      · intro x hx
        change ((G.map x - G.map x₀) / (x - x₀)) * (x - x₀) =
          G.map x - G.map x₀
        field [sub_ne_zero.mpr hx.2.2]
    have h_sum := FuncLimit.Add h_difference
      (Continuity.Constant (C := G.map x₀) x₀ (mem_univ _)).2
    apply (show FuncLimit
      ((G - Constant (G.map x₀)) + Constant (G.map x₀)) x₀ (G.map x₀) by
        convert h_sum using 1
        change G.map x₀ = 0 + G.map x₀
        ring).Congr
    rcases h_G.1 with ⟨δ, hδ, hdom⟩
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro x hx
      exact (hdom hx).1.1.1
    · intro x hx
      change (G.map x - G.map x₀) + G.map x₀ = G.map x
      ring
  have h_slope_comp : FuncLimit (slope ⊙ G) x₀ F' :=
    by simpa [slope] using FuncLimit.CompSV h_G_cont h_slope_cont
  have h_product := FuncLimit.Mul h_slope_comp h_G
  apply h_product.Congr
  rcases h_G.1 with ⟨δG, hδG, hGdom⟩
  rcases h_F.1 with ⟨δF, hδF, hFdom⟩
  rcases h_G_cont.2 δF hδF with ⟨δC, hδC, hGclose⟩
  refine ⟨min δG δC, lt_min hδG hδC, ?_, ?_⟩
  · intro x hx
    have hxG : x ∈ Nbhd x₀ δG := by
      exact ⟨by linarith [hx.1, min_le_left δG δC],
        by linarith [hx.2.1, min_le_left δG δC], hx.2.2⟩
    have hxC : x ∈ Nbhd x₀ δC := by
      exact ⟨by linarith [hx.1, min_le_right δG δC],
        by linarith [hx.2.1, min_le_right δG δC], hx.2.2⟩
    have hxGdom := hGdom hxG
    have hGx_near := hGclose x hxC
    have hGxF : G.map x ∈ F.domain := by
      by_cases h_eq : G.map x = G.map x₀
      · simpa [h_eq] using h_FGx₀
      · exact (hFdom ⟨hGx_near.1, hGx_near.2, h_eq⟩).1.1.1
    refine ⟨⟨⟨⟨hxGdom.1.1.1, hGxF⟩, trivial⟩,
      ⟨trivial, trivial⟩⟩, ?_⟩
    change x - x₀ ≠ 0
    exact sub_ne_zero.mpr hx.2.2
  · intro x hx
    change slope.map (G.map x) * ((G.map x - G.map x₀) / (x - x₀)) =
      ((F.map (G.map x) - F.map (G.map x₀)) / (x - x₀))
    by_cases h_eq : G.map x = G.map x₀
    · simp [slope, h_eq]
    · simp only [slope, h_eq, ↓reduceIte]
      field_simp [sub_ne_zero.mpr hx.2.2, sub_ne_zero.mpr h_eq]

/-- Composition of Left Derivative -/
theorem LeftDeriv.Chain {F' G' : ℝ}
    (h_G : LeftDeriv G x₀ G') (h_F : LeftDeriv F (G.map x₀) F')
  : LeftDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- Composition of Right Derivative -/
theorem RightDeriv.Chain {F' G' : ℝ}
    (h_G : RightDeriv G x₀ G') (h_F : RightDeriv F (G.map x₀) F')
  : RightDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

end


page_end
