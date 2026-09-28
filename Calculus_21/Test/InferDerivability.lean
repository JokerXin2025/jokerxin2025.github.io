import Calculus_21.Differential.Tactics.Derivability

variable {F G : RFunction} {I J : Set ℝ} {x k c d e a : ℝ} {n : ℕ}

-- Operation rules, forward projections, and set/domain instantiation.
example (hF : F.isDerivableAt x) (hG : G.isDerivableAt x) :
    (k • (-F) + G * F - Constant c).isDerivableAt x := by infer_derivability

example : (Identity ^ n + Constant c).isDerivableAt x := by infer_derivability
example (hF : F.isDerivableAt x) : (F ^ 0).isDerivableAt x := by infer_derivability

example (hF : F.isDerivableAt x) (hG : G.isDerivableAt x)
    (hne : G.map x ≠ 0) : (F / G + G⁻¹).isDerivableAt x := by infer_derivability

example (h : Deriv F x d ∧ Deriv G x e) :
    (F * G + Identity).isDerivableAt x := by infer_derivability

example (hF : F.isDerivableIn I) (hx : x ∈ I) :
    (-F + Identity).isDerivableAt x := by infer_derivability

example (hF : F.isDerivableIn I) (hG : G.isDerivableIn I)
    (hne : ∀ y ∈ I, G.map y ≠ 0) :
    (F / G + G⁻¹).isDerivableIn I := by infer_derivability

example (hF : F.isDerivableIn I) (hJI : J ⊆ I) :
    (F ^ n).isDerivableIn J := by infer_derivability

example (hF : F.isDerivable) (hx : x ∈ F.domain) :
    (k • F).isDerivableAt x := by infer_derivability

example (hF : F.isDerivable) (hG : G.isDerivable) :
    (F / G).isDerivable := by infer_derivability
example (hF : F.isDerivable) : F⁻¹.isDerivable := by infer_derivability
example (hF : F.isDerivable) (hG : G.isDerivable) :
    (F ⊙ G).isDerivable := by infer_derivability
example (hF : F.isDerivable) : (k • (-F) ^ n).isDerivable := by infer_derivability
example : (Identity + Constant c).isDerivableIn I := by infer_derivability

example (hF : F.isDerivableAt (G.map x)) (hG : G.isDerivableAt x)
    (hm : G.map x ∈ F.domain) : (F ⊙ G).isDerivableAt x := by infer_derivability

example (hF : F.isDerivableIn J) (hG : G.isDerivableIn I)
    (hm : ∀ y ∈ I, G.map y ∈ J) (hdom : J ⊆ F.domain) :
    (F ⊙ G).isDerivableIn I := by infer_derivability

example (hF : ∀ y ∈ I, F.isDerivableAt y) :
    let H := F - k • Identity
    ∀ y ∈ I, H.isDerivableAt y := by
  intro H
  infer_derivability

-- Whole-expression derivatives must project before local definitions are split.
example : let H := F + G; Deriv H x d → H.isDerivableAt x := by
  intro H h
  infer_derivability

example : let H := F / G; Deriv H x d → H.isDerivableAt x := by
  intro H h
  aesop (rule_sets := [AutoDerivability]) (config := { terminal := true })

example : let H := F ⊙ G; Deriv H x d → H.isDerivableAt x := by
  intro H h
  infer_derivability

-- Without a whole-expression fact, arithmetic and its side conditions still apply.
example (hF : Deriv F x d) (hG : Deriv G x e) :
    let H := F / G
    G.map x ≠ 0 → H.isDerivableAt x := by
  intro H
  fail_if_success have hbad : H.isDerivableAt x := by infer_derivability
  intro hne
  infer_derivability

example (_h : Deriv (F + G) x d) : True := by
  fail_if_success have hbad : F.isDerivableAt x := by infer_derivability
  trivial

-- The named ruleset works directly, without opening a scope.
example : Identity.isDerivableAt x := by
  aesop (config := { terminal := true }) (rule_sets := [AutoDerivability])
example : Identity.isDerivableAt x := script
  infer_derivability

-- Constants remain automatic; elementary and numerical facts must be supplied.
example : (Constant c).isDerivableAt x := by infer_derivability

example (_hx : x > 0) (_ha : a > 1) : True := by
  fail_if_success have h : Sin.isDerivableAt x := by infer_derivability
  fail_if_success have h : Exp.isDerivableAt x := by infer_derivability
  fail_if_success have h : Sqrt.isDerivableAt x := by infer_derivability
  fail_if_success have h : Deriv (Constant c) x 0 := by infer_derivability
  fail_if_success have h : Deriv Identity x 1 := by infer_derivability
  fail_if_success have h : Deriv Sin x (cos x) := by infer_derivability
  fail_if_success have h : Deriv Sqrt x ((√x)⁻¹ * (2 : ℝ)⁻¹) := by infer_derivability
  fail_if_success have h : RightDeriv (Power a) 0 0 := by infer_derivability
  trivial

example : Sin.isDerivableAt x → (Sin + Identity).isDerivableAt x := by
  fail_if_success have h : (Sin + Identity).isDerivableAt x := by infer_derivability
  intro h
  infer_derivability

example (h : Deriv Sin x (cos x)) : (Sin + Identity).isDerivableAt x := by
  infer_derivability

-- Terminal mode must not silently leave side conditions behind.
example (hF : F.isDerivableAt x) (hG : G.isDerivableAt x) :
    G.map x ≠ 0 → (F / G).isDerivableAt x := by
  fail_if_success
    have hbad : (F / G).isDerivableAt x := by infer_derivability
  intro hne
  infer_derivability

example (hF : F.isDerivableAt x) : F.map x ≠ 0 → F⁻¹.isDerivableAt x := by
  fail_if_success
    have hbad : F⁻¹.isDerivableAt x := by infer_derivability
  intro hne
  infer_derivability

example (hF : F.isDerivableAt (G.map x)) (hG : G.isDerivableAt x) :
    G.map x ∈ F.domain → (F ⊙ G).isDerivableAt x := by
  fail_if_success
    have hbad : (F ⊙ G).isDerivableAt x := by infer_derivability
  intro hm
  infer_derivability

example (hF : F.isDerivableIn I) : x ∈ I → F.isDerivableAt x := by
  fail_if_success
    have hbad : F.isDerivableAt x := by infer_derivability
  intro hx
  infer_derivability

example (hF : F.isDerivable) : x ∈ F.domain → F.isDerivableAt x := by
  fail_if_success
    have hbad : F.isDerivableAt x := by infer_derivability
  intro hx
  infer_derivability

example (hF : F.isDerivableIn I) (hG : G.isDerivableIn I) :
    (∀ y ∈ I, G.map y ≠ 0) → (F / G).isDerivableIn I := by
  fail_if_success
    have hbad : (F / G).isDerivableIn I := by infer_derivability
  intro hne
  infer_derivability

-- Domain membership alone is insufficient at singularities and endpoints.
example : True := by
  fail_if_success have h : Abs.isDerivableAt 0 := by infer_derivability
  fail_if_success have h : Sqrt.isDerivableAt 0 := by infer_derivability
  fail_if_success have h : Ln.isDerivableAt 0 := by infer_derivability
  fail_if_success have h : (NPower (0 : ℤ)).isDerivableAt 0 := by infer_derivability
  fail_if_success have h : (Power (2 : ℝ)).isDerivableAt 0 := by infer_derivability
  fail_if_success have h : Coth.isDerivableAt 0 := by infer_derivability
  fail_if_success have h : Csch.isDerivableAt 0 := by infer_derivability
  fail_if_success have h : Arcsin.isDerivableAt 1 := by infer_derivability
  fail_if_success have h : Arccos.isDerivableAt (-1) := by infer_derivability
  fail_if_success have h : Arcsec.isDerivableAt 1 := by infer_derivability
  fail_if_success have h : Arccsc.isDerivableAt (-1) := by infer_derivability
  trivial

example : True := by
  fail_if_success have h : (Expow a).isDerivableAt x := by infer_derivability
  fail_if_success have h : (Log a).isDerivableAt x := by infer_derivability
  fail_if_success have h : Tan.isDerivableAt x := by infer_derivability
  fail_if_success have h : Cot.isDerivableAt x := by infer_derivability
  fail_if_success have h : Sec.isDerivableAt x := by infer_derivability
  fail_if_success have h : Csc.isDerivableAt x := by infer_derivability
  trivial

example (_hx : x > 0) (_ha : a > 0) (_ha1 : a ≠ 1) : True := by
  fail_if_success have h : (Log a).isDerivableAt x := by infer_derivability
  trivial

example : True := by
  fail_if_success have h : Deriv Sqrt x (1 / (2 * √x)) := by infer_derivability
  fail_if_success have h : Deriv (Log a) x (ln a * x)⁻¹ := by infer_derivability
  fail_if_success have h : RightDeriv (Power a) 0 0 := by infer_derivability
  trivial

-- Derivability does not imply membership of the center in the domain.
example (_hF : F.isDerivableAt x) : x ∈ F.domain → x ∈ F.domain := by
  fail_if_success
    have hbad : x ∈ F.domain := by infer_derivability
  intro hx
  exact hx

private def puncturedIdentity : RFunction := ⟨id, {y | y ≠ 0}⟩

private theorem puncturedIdentity_deriv : Deriv puncturedIdentity 0 1 := by
  apply Deriv.fromDerivExpr
  · exact ⟨1, zero_lt_one, fun _ hy => hy.2.2⟩
  · exact DerivExpr.Identity

example : 0 ∉ puncturedIdentity.domain := by
  intro h
  exact h rfl

example : (Identity ⊙ puncturedIdentity).isDerivableAt 0 := by
  have h := puncturedIdentity_deriv
  infer_derivability
