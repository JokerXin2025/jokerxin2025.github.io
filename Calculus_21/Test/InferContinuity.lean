import Calculus_21.Limit.Tactics.Continuity

open RFunction

variable {F G : RFunction} {a b x k c : ℝ}

-- Pointwise operations, including composition and a nonzero denominator.
example (hF : F.isContinuousAt x) (hG : G.isContinuousAt x) :
    (k • (-F) + G * F - Constant c).isContinuousAt x := by infer_continuity

example (hF : F.isContinuousAt x) (hG : G.isContinuousAt x)
    (hne : G.map x ≠ 0) : (F / G).isContinuousAt x := by infer_continuity

example (hF : F.isContinuousAt (G.map x)) (hG : G.isContinuousAt x) :
    (F ⊙ G).isContinuousAt x := by infer_continuity

-- Closed intervals must use one-sided continuity, not full endpoint continuity.
example (hF : F.isContinuousInIcc a b) (hG : G.isContinuousInIcc a b) :
    (k • (-F) + G * F - Constant c).isContinuousInIcc a b := by infer_continuity

example (hF : F.isContinuousInIcc a b) (hG : G.isContinuousInIcc a b)
    (hne : ∀ y, G.map y ≠ 0) :
    (F / G).isContinuousInIcc a b := by infer_continuity

example (hF : F.isContinuousInIcc a b) (hx : x ∈ Ioo a b) :
    (F + Identity).isContinuousAt x := by infer_continuity

example (hF : F.isContinuousIn (Ioo a b)) :
    (k • F - Identity).isContinuousIn (Ioo a b) := by infer_continuity

example (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x)
    (hne : G.map x ≠ 0) :
    ((k • (-F) + G * F) / G).isLeftContinuousAt x := by infer_continuity

example (hF : F.isRightContinuousAt x) (hG : G.isRightContinuousAt x)
    (hne : G.map x ≠ 0) :
    ((k • (-F) + G * F) / G).isRightContinuousAt x := by infer_continuity

example : (Identity + Constant c).isContinuousInIcc a b := by infer_continuity

-- Local definitions and endpoint equalities must not disrupt limit matching.
example (hF : F.isContinuousInIcc a b) :
    let H := F - k • Identity
    H.map a = H.map b → H.isContinuousInIcc a b := by
  intro H heq
  infer_continuity

-- Full continuity of a whole local expression projects before operation rules.
example : let H := F + G
    H.isContinuousAt x → H.isLeftContinuousAt x ∧ H.isRightContinuousAt x := by
  intro H h
  constructor <;> infer_continuity

example : let H := F / G
    H.isContinuousAt x → H.isLeftContinuousAt x ∧ H.isRightContinuousAt x := by
  intro H h
  constructor <;>
    aesop (rule_sets := [AutoContinuity]) (config := { terminal := true })

example : let H := F ⊙ G
    H.isContinuousAt x → H.isLeftContinuousAt x ∧ H.isRightContinuousAt x := by
  intro H h
  constructor <;> infer_continuity

-- Failed projection leaves genuinely one-sided arithmetic available.
example (hF : F.isLeftContinuousAt x) (hG : G.isLeftContinuousAt x) :
    let H := F / G
    G.map x ≠ 0 → H.isLeftContinuousAt x := by
  intro H
  fail_if_success have hbad : H.isLeftContinuousAt x := by infer_continuity
  intro hne
  infer_continuity

example (_h : (F + G).isContinuousAt x) : True := by
  fail_if_success have hbad : F.isLeftContinuousAt x := by infer_continuity
  trivial

-- Whole-function facts must win over unfolding local arithmetic definitions.
example (hab : a < b) :
    let R := F - G
    (∀ t ∈ Icc a b, R.isContinuousAt t) → R.isContinuousInIcc a b := by
  intro R hRc
  infer_continuity

example (f : ℝ → ℝ) :
    let G := total_fun t ↦ f t
    (∀ t, G.isContinuousAt t) → G.isContinuousInIcc a b := by
  intro G hGc
  infer_continuity

-- Altering the domain of a total sum must not trigger proofs for its summands.
example (f g : ℝ → ℝ) (hab : a < b) :
    let H := { total (f + g) with domain := Icc a b }
    (∀ t ∈ Icc a b, H.isContinuousAt t) → H.isContinuousInIcc a b := by
  intro H hH
  infer_continuity

example (h : ∀ {t}, F.isContinuousAt t) : F.isContinuousInIcc a b := by
  infer_continuity

example (hab : a ≤ b) (h : ∀ {t}, t ∈ Icc a b → F.isContinuousAt t) :
    F.isContinuousInIcc a b := by
  aesop (rule_sets := [AutoContinuity]) (config := { terminal := true })

-- A failed bridge must leave the genuine one-sided route available.
example (_h : ∀ t ∈ Icc a b, F.isContinuousAt t)
    (hi : F.isContinuousIn (Ioo a b))
    (ha : F.isRightContinuousAt a) (hb : F.isLeftContinuousAt b) :
    F.isContinuousInIcc a b := by infer_continuity

-- An Icc fact alone gives no endpoint information when the interval is empty.
example (_h : ∀ t ∈ Icc a b, F.isContinuousAt t) : True := by
  fail_if_success have hbad : F.isContinuousInIcc a b := by infer_continuity
  fail_if_success
    have hbad : F.isContinuousInIcc a b := by
      aesop (rule_sets := [AutoContinuity]) (config := { terminal := true })
  trivial

-- The named ruleset is available explicitly without opening a scope.
example : Identity.isContinuousAt x := by
  aesop (config := { terminal := true }) (rule_sets := [AutoContinuity])

example : Identity.isContinuousAt x := by
  infer_continuity

-- The tactic must not silently discard the denominator's nonzero condition.
example (hF : F.isContinuousAt x) (hG : G.isContinuousAt x) :
    G.map x ≠ 0 → (F / G).isContinuousAt x := by
  fail_if_success
    have hbad : (F / G).isContinuousAt x := by infer_continuity
  intro hne
  infer_continuity

-- Constants and Identity remain automatic; elementary facts must be supplied.
example : (Constant c).isContinuous := by infer_continuity
example : Identity.isContinuous := by infer_continuity

example (_hx : x > 0) : True := by
  fail_if_success have h : Sin.isContinuousAt x := by infer_continuity
  fail_if_success have h : Exp.isContinuous := by infer_continuity
  fail_if_success have h : Sqrt.isContinuousAt x := by infer_continuity
  fail_if_success have h : Sqrt.isRightContinuousAt 0 := by infer_continuity
  trivial

example : Sin.isContinuousAt x → (Sin + Identity).isContinuousAt x := by
  fail_if_success have h : (Sin + Identity).isContinuousAt x := by infer_continuity
  intro h
  infer_continuity

example (h : Sqrt.isRightContinuousAt 0) :
    (Sqrt ^ (3 : ℕ)).isRightContinuousAt 0 := by infer_continuity

-- Inversion and natural powers use genuinely one-sided hypotheses at endpoints.
example (hF : F.isContinuousAt x) (hne : F.map x ≠ 0) :
    F⁻¹.isContinuousAt x := by infer_continuity
example (hF : F.isContinuousAt x) (n : ℕ) :
    (F ^ n).isContinuousAt x := by infer_continuity
example (hF : F.isLeftContinuousAt x) (hne : F.map x ≠ 0) :
    F⁻¹.isLeftContinuousAt x := by infer_continuity
example (hF : F.isRightContinuousAt x) (hne : F.map x ≠ 0) :
    F⁻¹.isRightContinuousAt x := by infer_continuity
example (hF : F.isLeftContinuousAt x) (n : ℕ) :
    (F ^ n).isLeftContinuousAt x := by infer_continuity
example (hF : F.isRightContinuousAt x) (n : ℕ) :
    (F ^ n).isRightContinuousAt x := by infer_continuity
example (hF : F.isContinuousInIcc a b) (hne : ∀ y, F.map y ≠ 0) :
    F⁻¹.isContinuousInIcc a b := by infer_continuity
example (hF : F.isContinuousInIcc a b) (n : ℕ) :
    (F ^ n).isContinuousInIcc a b := by infer_continuity
example (hF : F.isContinuousInIcc a b)
    (hne : ∀ y ∈ Ioo a b, F.map y ≠ 0)
    (ha : F.map a ≠ 0) (hb : F.map b ≠ 0) :
    F⁻¹.isContinuousInIcc a b := by infer_continuity
example (hF : F.isContinuousInIcc a b) :
    F.isRightContinuousAt a := by infer_continuity
example (hF : F.isContinuousInIcc a b) :
    F.isLeftContinuousAt b := by infer_continuity

-- Bounded search regression: nested endpoint arithmetic needs no limit search.
example (hF : F.isContinuousInIcc a b) (hG : G.isContinuousInIcc a b)
    (hne : ∀ y, G.map y ≠ 0) :
    (((k • (-F) + G * F - Constant c) ^ (4 : ℕ)) / G).isContinuousInIcc a b := by
  aesop (rule_sets := [AutoContinuity])
    (config := { useSimpAll := false, terminal := true, maxRuleApplications := 300 })

-- Missing conditions must fail, not be erased by elementary/operation rules.
example (hF : F.isContinuousAt x) : F.map x ≠ 0 → F⁻¹.isContinuousAt x := by
  fail_if_success have hbad : F⁻¹.isContinuousAt x := by infer_continuity
  intro hne
  infer_continuity

example (hF : F.isLeftContinuousAt x) : F.map x ≠ 0 → F⁻¹.isLeftContinuousAt x := by
  fail_if_success have hbad : F⁻¹.isLeftContinuousAt x := by infer_continuity
  intro hne
  infer_continuity

example (hF : F.isRightContinuousAt x) : F.map x ≠ 0 → F⁻¹.isRightContinuousAt x := by
  fail_if_success have hbad : F⁻¹.isRightContinuousAt x := by infer_continuity
  intro hne
  infer_continuity

example : True := by
  fail_if_success have hbad : Ln.isContinuousAt x := by infer_continuity
  fail_if_success have hbad : (Log a).isContinuousAt x := by infer_continuity
  fail_if_success have hbad : (Expow a).isContinuousAt x := by infer_continuity
  fail_if_success have hbad : Sqrt.isContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : Sqrt.isLeftContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : (Power a).isRightContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : (Power a).isContinuousAt x := by infer_continuity
  fail_if_success have hbad : (NPower 0).isContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : (NPower (-1)).isContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : Tan.isContinuousAt x := by infer_continuity
  fail_if_success have hbad : Cot.isContinuousAt x := by infer_continuity
  fail_if_success have hbad : Sec.isContinuousAt x := by infer_continuity
  fail_if_success have hbad : Csc.isContinuousAt x := by infer_continuity
  fail_if_success have hbad : Coth.isContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : Csch.isContinuousAt 0 := by infer_continuity
  fail_if_success have hbad : Arcsin.isContinuousAt 1 := by infer_continuity
  fail_if_success have hbad : Arccos.isLeftContinuousAt (-1) := by infer_continuity
  fail_if_success have hbad : Arcsec.isRightContinuousAt (-1) := by infer_continuity
  fail_if_success have hbad : Arccsc.isContinuousAt 1 := by infer_continuity
  trivial

-- Even the zeroth power retains the original function's domain.
example : True := by
  fail_if_success have hbad : (F ^ (0 : ℕ)).isContinuousAt x := by infer_continuity
  fail_if_success have hbad : (F ^ (0 : ℕ)).isLeftContinuousAt x := by infer_continuity
  fail_if_success have hbad : (F ^ (0 : ℕ)).isRightContinuousAt x := by infer_continuity
  trivial

-- Projections still work on demand, without populating every arithmetic branch.
example (hF : F.isContinuousAt x) : x ∈ F.domain := by infer_continuity
example (hF : F.isLeftContinuousAt x) : x ∈ F.domain := by infer_continuity
example (hF : F.isRightContinuousAt x) : x ∈ F.domain := by infer_continuity
example (hF : F.isContinuousAt x) : FuncLimit F x (F.map x) := by infer_continuity
example (hF : F.isLeftContinuousAt x) : LeftLimit F x (F.map x) := by infer_continuity
example (hF : F.isRightContinuousAt x) : RightLimit F x (F.map x) := by infer_continuity

example (_hx : x > 0) (_ha : a > 0 ∧ a ≠ 1) : True := by
  fail_if_success have hbad : (Log a).isContinuousAt x := by infer_continuity
  trivial

example (_hF : F.isContinuousInIcc a b) : True := by
  fail_if_success have hbad : F.isLeftContinuousAt a := by infer_continuity
  fail_if_success have hbad : F.isRightContinuousAt b := by infer_continuity
  fail_if_success have hbad : F⁻¹.isContinuousInIcc a b := by infer_continuity
  trivial
