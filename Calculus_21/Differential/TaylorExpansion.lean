/-
    «Calculus_21».Differential.TaylorExpansion
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Infinitesimal.Higher
import «Calculus_21».Limit.L'Hospital
import «Calculus_21».Differential.Tactics.Derivability
set_option linter.style.header false


/-- Taylor's Polynomial -/
noncomputable def TaylorPolynomial (F : RFunction) (x₀ : ℝ) (N : ℕ) : RFunction :=
  ⟨fun x ↦ ∑ k ∈ range (N + 1),
    (((NthDiff k F).map x₀ / k !) * (x - x₀) ^ k), Iii⟩

lemma _deriv_sum (n : ℕ) {fₙ : ℕ → ℝ → ℝ} {dₙ : ℕ → ℝ} {a : ℝ}
    (h : ∀ k < n, Deriv (total (fₙ k)) a (dₙ k))
  : Deriv (total_fun t ↦ ∑ k ∈ range n, fₙ k t) a (∑ k ∈ range n, dₙ k)
:= script
  induction n
  | zero =>
    simp_only [Finset.range_zero, Finset.sum_empty]
    exact Deriv.Constant a
  | succ n ih =>
    use_expr
    | calculation =>
      claim h₁ : Deriv (total_fun t ↦ ∑ k ∈ range n, fₙ k t) a (∑ k ∈ range n, dₙ k)
      · exact ih (fun k hk => h k (by omega))
      claim h₂ : Deriv (total (fₙ n)) a (dₙ n)
      · exact h n (by omega)
      simp_only [Finset.sum_range_succ]
      calc
        _  =. D (fun t ↦ ∑ k ∈ range n, fₙ k t) a + D (fₙ n) a
              := by deriv_add
        _  =  the ((∑ k ∈ range n, dₙ k) + dₙ n)
              := by poly_rw [h₁.toDerivExpr, h₂.toDerivExpr]
    | side =>
      exists 1 with zero_lt_one
      apply subset_univ _

lemma cont_sum (n : ℕ) (fₙ : ℕ → ℝ → ℝ) (a : ℝ)
    (h : ∀ k < n, (total (fₙ k)).isContinuousAt a)
  : (total_fun t ↦ ∑ k ∈ range n, fₙ k t).isContinuousAt a
:= by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    change (Constant 0).isContinuousAt a
    infer_continuity
  | succ n ih =>
    have heq : (total_fun t ↦ ∑ k ∈ range n, fₙ k t) + total (fₙ n)
        = total_fun t ↦ ∑ k ∈ range (n + 1), fₙ k t := by
      apply RFunction.ext
      · funext t
        symm
        apply Finset.sum_range_succ _ _
      · tauto_set
    script_infer
        ∀ k < n, (total (fₙ k)).isContinuousAt a
     => (total_fun t ↦ ∑ k ∈ range n, fₙ k t).isContinuousAt a
        := ih (fun k hk => h k (by omega))
     => ((total_fun t ↦ ∑ k ∈ range n, fₙ k t) + total (fₙ n)).isContinuousAt a
        := by infer_continuity
     => (total_fun t ↦ ∑ k ∈ range (n + 1), fₙ k t).isContinuousAt a
        := heq ▸ ?_

lemma lemma₁ {a x₀ : ℝ} {n : ℕ}
  : Deriv (total_fun x ↦ (a - x) ^ n) x₀ (-n * (a - x₀) ^ (n - 1))
:= script
  use_expr
  | calculation =>
    given_proper
    calc
      _  =? the n * D (a - ·) x₀ * the ((a - x₀) ^ (n - 1))
            := by deriv_mspow
      _  =  the n * the (-1) * the ((a - x₀) ^ (n - 1))
            := by deriv_calc
      _  =  the (-n * (a - x₀) ^ (n - 1))
            := by
              change the (n * (-1) * (a - x₀) ^ (n - 1)) = _
              ring_nf
  | side =>
    exists 1 with zero_lt_one
    tauto_set

lemma cont_power {n : ℕ} {a x₀ : ℝ}
  : (total_fun s ↦ (a - s) ^ n).isContinuousAt x₀
:= script
  claim heq : (Constant a - Identity) ^ n = total_fun s ↦ (a - s) ^ n
  · apply RFunction.ext
    · rfl
    · tauto_set
  rw [← heq]
  infer_continuity

noncomputable def moving (F : RFunction) (x : ℝ) (n : ℕ) : RFunction :=
  total_fun t ↦ ∑ k ∈ range (n + 1), (NthDiff k F).map t / k ! * (x - t) ^ k

lemma moving_deriv {F : RFunction} {x t : ℝ} {n : ℕ}
    (h : ∀ k ≤ n, (NthDiff k F).isDerivableAt t) :
    Deriv (moving F x n) t ((NthDiff (n + 1) F).map t / n ! * (x - t) ^ n) := by
  let A := fun k ↦ (NthDiff (k + 1) F).map t / k ! * (x - t) ^ k
  have terms : ∀ k ≤ n,
      Deriv (total_fun s ↦ (NthDiff k F).map s / k ! * (x - s) ^ k) t
        (A k - if k = 0 then 0 else A (k - 1)) := by
    intro k hk
    refine Deriv.fromDerivExpr ⟨1, zero_lt_one, subset_univ _⟩ ?_
    script_given_proper
    calc
      D (fun s ↦ (NthDiff k F).map s / k ! * (x - s) ^ k) t
          =? D (fun s ↦ (NthDiff k F).map s / k !) t * the ((x - t) ^ k) +
              D (fun s ↦ (x - s) ^ k) t * the ((NthDiff k F).map t / k !)
             := by deriv_mul
      _ =  D (fun s ↦ (k ! : ℝ)⁻¹ * (NthDiff k F).map s) t * the ((x - t) ^ k) +
              D (fun s ↦ (x - s) ^ k) t * the ((NthDiff k F).map t / k !)
             := by rw [show (fun s ↦ (NthDiff k F).map s / k !) =
                 (fun s ↦ (k ! : ℝ)⁻¹ * (NthDiff k F).map s) by funext s; ring]
      _ =. (the (k ! : ℝ)⁻¹ * D (NthDiff k F).map t) * the ((x - t) ^ k) +
              D (fun s ↦ (x - s) ^ k) t * the ((NthDiff k F).map t / k !)
             := by deriv_smul
      _ = the ((k ! : ℝ)⁻¹ * (NthDiff (k + 1) F).map t * (x - t) ^ k +
              (-(k : ℝ) * (x - t) ^ (k - 1)) * ((NthDiff k F).map t / k !)) := by
        poly_rw [(h k hk).toDeriv.toDerivExpr, lemma₁.toDerivExpr]
      _ = the (A k - if k = 0 then 0 else A (k - 1)) := by
        congr 1
        cases k with
        | zero => grind
        | succ k =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, A,
            Nat.factorial_succ, Nat.cast_mul]
          field
  have telescoping : ∑ k ∈ range (n + 1), (A k - if k = 0 then 0 else A (k - 1)) = A n := by
    clear h terms
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      grind
  script_infer
    (∀ k < n + 1, Deriv
      (total_fun s ↦ (NthDiff k F).map s / k ! * (x - s) ^ k) t
      (A k - if k = 0 then 0 else A (k - 1)))
      => Deriv (moving F x n) t
           (∑ k ∈ range (n + 1), (A k - if k = 0 then 0 else A (k - 1)))
         := _deriv_sum (n + 1) (fun k hk => terms k (by omega))
      => Deriv (moving F x n) t (A n)
         := telescoping ▸ ?_

lemma moving_cont {F : RFunction} {x t : ℝ} {n : ℕ}
    (h : ∀ k ≤ n, (NthDiff k F).isContinuousAt t) :
    (moving F x n).isContinuousAt t := by
  apply cont_sum
  intro k hk
  have hpower : (total_fun s ↦ (x - s) ^ k).isContinuousAt t := cont_power
  have heq : (k ! : ℝ)⁻¹ • total (NthDiff k F).map *
      (total_fun s ↦ (x - s) ^ k) =
      total_fun s ↦ (NthDiff k F).map s / k ! * (x - s) ^ k := by
    apply RFunction.ext
    · funext s
      change (k ! : ℝ)⁻¹ * (NthDiff k F).map s * (x - s) ^ k = _
      dsimp [total]
      ring_nf
    · tauto_set
  script_infer
    (NthDiff k F).isContinuousAt t
      => (total (NthDiff k F).map).isContinuousAt t
         := Continuity.total (h k (by omega))
      => ((k ! : ℝ)⁻¹ • total (NthDiff k F).map *
           total_fun s ↦ (x - s) ^ k).isContinuousAt t
         := by infer_continuity
      => (total_fun s ↦ (NthDiff k F).map s / k ! * (x - s) ^ k).isContinuousAt t
         := heq ▸ ?_

lemma moving_self (F : RFunction) (x : ℝ) (n : ℕ) :
    (moving F x n).map x = F.map x := by
  simp [moving, total, Finset.sum_range_succ', NthDiff]

/-- The moving-center sum plus a correcting power has equal endpoint values.
Rolle's theorem then identifies the correcting coefficient. -/
lemma lagrange {F : RFunction} {x x₀ a b : ℝ} {n : ℕ}
    (hab : a < b) (hend : (a = x₀ ∧ b = x) ∨ (a = x ∧ b = x₀))
    (hc : ∀ k ≤ n, ∀ t ∈ Icc a b, (NthDiff k F).isContinuousAt t)
    (hd : ∀ k ≤ n, ∀ t ∈ Ioo a b, (NthDiff k F).isDerivableAt t) :
    ∃ ξ ∈ Ioo a b, F.map x = (TaylorPolynomial F x₀ n).map x +
      (NthDiff (n + 1) F).map ξ / (n + 1)! * (x - x₀) ^ (n + 1) := by
  let P := (TaylorPolynomial F x₀ n).map x
  let c := (F.map x - P) / (x - x₀) ^ (n + 1)
  let H := moving F x n + c • total_fun t ↦ (x - t) ^ (n + 1)
  have hne : x - x₀ ≠ 0 := by grind
  have hx : H.map x = F.map x := by
    change (moving F x n).map x + c * (x - x) ^ (n + 1) = _
    simp [moving_self]
  have hx₀ : H.map x₀ = F.map x := by
    change P + c * (x - x₀) ^ (n + 1) = _
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hne)]
    ring_nf
  have hcont : ∀ t ∈ Icc a b, H.isContinuousAt t := by
    intro t ht
    have hmoving := moving_cont (x := x) (fun k hk => hc k hk t ht)
    have hpower : (total_fun s ↦ (x - s) ^ (n + 1)).isContinuousAt t := cont_power
    infer_continuity
  have hderiv : ∀ t ∈ Ioo a b, Deriv H t
      (((NthDiff (n + 1) F).map t / (n)! - c * (n + 1)) * (x - t) ^ n) := by
    intro t ht
    script_use_expr
    case side =>
      script_exists 1 with zero_lt_one
      intro _ _
      trivial
    case calculation => calc
      D H.map t =. D (moving F x n).map t + D (fun s ↦ c * (x - s) ^ (n + 1)) t
                   := by deriv_add
      _ =. D (moving F x n).map t + the c * D (fun s ↦ (x - s) ^ (n + 1)) t
                   := by deriv_smul
      _ = the ((NthDiff (n + 1) F).map t / n ! * (x - t) ^ n +
            c * (-((n + 1 : ℕ) : ℝ) * (x - t) ^ (n + 1 - 1))) := by
        dsimp only [moving, total]
        poly_rw [(moving_deriv (fun k hk => hd k hk t ht)).toDerivExpr,
          lemma₁.toDerivExpr]
      _ = the (((NthDiff (n + 1) F).map t / (n)! - c * (n + 1)) * (x - t) ^ n) := by
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring_nf
  script_claim_exist ⟨ξ, hξ, hzero⟩ : ∃ ξ ∈ Ioo a b, Deriv H ξ 0
  · apply Rolle_MeanValue
    · exact hab
    · intro t ht
      script_exact_proj hcont t ht
    · rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hx, hx₀]
    · refine ⟨fun t ht => hcont t ⟨ht.1.le, ht.2.le⟩, ?_, ?_⟩
      · have ha := hcont a ⟨le_rfl, hab.le⟩
        infer_continuity
      · have hb := hcont b ⟨hab.le, le_rfl⟩
        infer_continuity
    · intro t ht
      have htDeriv := hderiv t ht
      infer_derivability
  script_exists ξ with hξ
  have hp : (x - ξ) ^ n ≠ 0 := by
    apply pow_ne_zero
    script_cases_by hend
    · linarith [hξ.2]
    · linarith [hξ.1]
  have hcval : c = (NthDiff (n + 1) F).map ξ / (n + 1)! := by
    script_infer
      ξ ∈ Ioo a b  => Deriv H ξ <| ((NthDiff (n + 1) F).map ξ / (n)! - c * (n + 1))
                        * (x - ξ) ^ n
                      := hderiv ξ hξ
                   => ((NthDiff (n + 1) F).map ξ / (n)! - c * (n + 1))
                        * (x - ξ) ^ n = 0
                      := (?_).unique hzero
                   => (NthDiff (n + 1) F).map ξ / (n)! - c * (n + 1) = 0
                      := (mul_eq_zero.mp ?_).resolve_right hp
                   => (NthDiff (n + 1) F).map ξ / n ! = c * (n + 1)
                      := sub_eq_zero.mp ?_
                   => (NthDiff (n + 1) F).map ξ = c * (n + 1) * n !
                      := (div_eq_iff (by positivity)).mp ?_
                   => c * ((n + 1) * n !) = (NthDiff (n + 1) F).map ξ
                      := by linarith
                   => c = (NthDiff (n + 1) F).map ξ / ((n + 1) * n !)
                      := (eq_div_iff (by positivity)).mpr ?_
                    => c = (NthDiff (n + 1) F).map ξ / (n + 1)!
                       := by
                         rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
                         exact this
  rw [← hcval]
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hne)]
  change F.map x = P + _
  ring_nf

lemma nth_shift {F : RFunction} {a : ℝ} {n : ℕ}
  : isNthDerivableAt (n + 1) F a → isNthDerivableAt n (Diff F) a
:= by
  let f' := (Diff F).map
  intro h
  induction n with
  | zero =>
    exists f' a
    constructor
    · rfl
    · exact h.mem_domain
  | succ n ih =>
    obtain ⟨d, hd⟩ := h
    script_exists d with ih hd.lower
    rw [nthDiff_diff]
    exact hd.deriv

lemma polynomial_self (F : RFunction) (a : ℝ) (n : ℕ)
  : (TaylorPolynomial F a n).map a = F.map a := by
  exact moving_self F a n

lemma polynomial_deriv (F : RFunction) (a t : ℝ) (n : ℕ)
  : Deriv (TaylorPolynomial F a (n + 1)) t ((TaylorPolynomial (Diff F) a n).map t)
:= by
  let F' := Diff F
  have terms : ∀ k : ℕ, Deriv
      (total_fun s ↦ (NthDiff k F).map a / k ! * (s - a) ^ k) t
      ((NthDiff k F).map a / k ! * k * (t - a) ^ (k - 1)) := by
    intro k
    refine Deriv.fromDerivExpr ⟨1, zero_lt_one, subset_univ _⟩ ?_
    script_given_proper
    calc
      D (fun s ↦ (NthDiff k F).map a / k ! * (s - a) ^ k) t
          =. the ((NthDiff k F).map a / k !) * D (fun s ↦ (s - a) ^ k) t
             := by deriv_smul
      _ =? the ((NthDiff k F).map a / k !) *
              (the k * D (fun s ↦ s - a) t * the ((t - a) ^ (k - 1)))
             := by
               intro hproper
               gcongr
               apply DerivExpr.MSPow
               have hbase : D (fun s ↦ s - a) t =. the 1 := by deriv_calc; norm_num; rfl
               poly_rw [hbase]
               trivial
      _ = the ((NthDiff k F).map a / k !) *
              (the k * the 1 * the ((t - a) ^ (k - 1))) := by deriv_calc
      _ = the ((NthDiff k F).map a / k ! * k * (t - a) ^ (k - 1)) := by
        change the ((NthDiff k F).map a / k ! * (k * 1 * (t - a) ^ (k - 1))) = _
        ring_nf
  have hd := _deriv_sum (n + 1 + 1) (fun k _ ↦ terms k)
  convert hd using 1
  · rfl
  change (∑ k ∈ range (n + 1), (NthDiff k F').map a / k ! * (t - a) ^ k) = _
  rw [Finset.sum_range_succ' (fun k ↦
    (NthDiff k F).map a / k ! * k * (t - a) ^ (k - 1))]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [nthDiff_diff]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

lemma lagrange_cauchy {F : RFunction} {x x₀ a b : ℝ} {n : ℕ}
    (hab : a < b) (hend : (a = x₀ ∧ b = x) ∨ (a = x ∧ b = x₀))
    (hc : ∀ k ≤ n, ∀ t ∈ Icc a b, (NthDiff k F).isContinuousAt t)
    (hd : ∀ k ≤ n, ∀ t ∈ Ioo a b, (NthDiff k F).isDerivableAt t) :
    ∃ ξ ∈ Ioo a b, F.map x = (TaylorPolynomial F x₀ n).map x +
      (NthDiff (n + 1) F).map ξ / (n + 1)! * (x - x₀) ^ (n + 1)
:= by
  let f := F.map
  let F' := Diff F
  let f' := F'.map
  induction n generalizing F x a b with
  | zero =>
    have hcont : F.isContinuousInIcc a b := by
      refine ⟨fun t ht => hc 0 le_rfl t ⟨ht.1.le, ht.2.le⟩, ?_, ?_⟩
      · have ha := hc 0 le_rfl a ⟨le_rfl, hab.le⟩
        infer_continuity
      · have hb := hc 0 le_rfl b ⟨hab.le, le_rfl⟩
        infer_continuity
    obtain ⟨ξ, hξ, heq⟩ := Lagrange_MeanValue hab
      (fun t ht => (hc 0 le_rfl t ht).1) hcont (hd 0 le_rfl)
    refine ⟨ξ, hξ, ?_⟩
    script_infer
      (f b - f a) / (b - a) = f' ξ
        => f b - f a = f' ξ * (b - a)
           := (div_eq_iff (sub_ne_zero.mpr (ne_of_gt hab))).mp heq
        => f x = f x₀ + f' ξ * (x - x₀)
           := by
            rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
        => f x = (TaylorPolynomial F x₀ 0).map x +
             (NthDiff (0 + 1) F).map ξ / (0 + 1)! * (x - x₀) ^ (0 + 1)
           := by
             simp only [TaylorPolynomial, Nat.zero_add, Finset.range_one,
               Finset.sum_singleton, NthDiff, Nat.factorial_zero, Nat.factorial_one,
               Nat.cast_one, div_one, pow_zero, mul_one, pow_one]
             exact this
  | succ n ih =>
    let R := F - TaylorPolynomial F x₀ (n + 1)
    let G := total_fun t ↦ (t - x₀) ^ (n + 1 + 1)
    let g := G.map
    have hR : ∀ t ∈ Ioo a b, Deriv R t
        (f' t - (TaylorPolynomial F' x₀ n).map t) := by
      intro t ht
      script_infer
        t ∈ Ioo a b => F.isDerivableAt t
                       := hd 0 (by omega) t ht
                    => Deriv F t (f' t)
                       := (?_).toDeriv
                    => Deriv R t
                         (f' t - (TaylorPolynomial F' x₀ n).map t)
                       := Deriv.Sub ?_ (polynomial_deriv F x₀ t n)
    have hG : ∀ t, Deriv G t ((n + 1 + 1 : ℕ) * (t - x₀) ^ (n + 1)) := by
      intro t
      use_expr
      case calculation =>
        script_given_proper
        calc
          D g t  =? the (n + 1 + 1 : ℕ) * D (fun s ↦ s - x₀) t *
                      the ((t - x₀) ^ (n + 1 + 1 - 1))
                    := by deriv_mspow
          _      =  the (n + 1 + 1 : ℕ) * the 1 * the ((t - x₀) ^ (n + 1 + 1 - 1))
                    := by deriv_calc
          _      =  the ((n + 1 + 1 : ℕ) * (t - x₀) ^ (n + 1))
                    := by
                      change the ((n + 1 + 1 : ℕ) * 1 * (t - x₀) ^ (n + 1 + 1 - 1)) = _
                      rw [mul_one, Nat.add_sub_cancel]
      case side =>
        script_exists 1 with zero_lt_one
        apply subset_univ _
    have hRc : ∀ t ∈ Icc a b, R.isContinuousAt t := by
      intro t ht
      have hF := hc 0 (by omega) t ht
      have hP : (TaylorPolynomial F x₀ (n + 1)).isContinuousAt t := by
        have hp := polynomial_deriv F x₀ t n
        exact ⟨trivial, FuncLimit.fromFuncLimitExpr
          ⟨1, zero_lt_one, subset_univ _⟩ (DerivExpr.toCont ⟨_, hp.toDerivExpr⟩)⟩
      exact Continuity.Sub hF hP
    have hGc : ∀ t, G.isContinuousAt t := by
      intro t
      have hg := hG t
      exact ⟨trivial, FuncLimit.fromFuncLimitExpr
        ⟨1, zero_lt_one, subset_univ _⟩ (DerivExpr.toCont ⟨_, hg.toDerivExpr⟩)⟩
    obtain ⟨y, hy, heq⟩ : ∃ ξ ∈ Ioo a b,
        (Diff R).map ξ * (G.map b - G.map a) =
        (Diff G).map ξ * (R.map b - R.map a) := by
      apply Cauchy_MeanValue (F := R) (G := G) hab
      · intro t ht
        exact ⟨(hRc t ht).1, trivial⟩
      · infer_continuity
      · infer_continuity
      · exact (fun t ht => ⟨_, hR t ht⟩)
      · exact (fun t _ => ⟨_, hG t⟩)
    have hRzero : R.map x₀ = 0 := by
      change f x₀ - (TaylorPolynomial F x₀ (n + 1)).map x₀ = 0
      rw [polynomial_self, sub_self]
    have hGzero : G.map x₀ = 0 := by simp [G, total]
    have hstep : (f' y - (TaylorPolynomial F' x₀ n).map y) *
        (x - x₀) ^ (n + 1 + 1) =
        ((n + 1 + 1 : ℕ) * (y - x₀) ^ (n + 1)) * R.map x := by
      script_infer
        (Diff R).map y * (G.map b - G.map a) =
          (Diff G).map y * (R.map b - R.map a)
          => (f' y - (TaylorPolynomial F' x₀ n).map y) *
               (G.map b - G.map a) =
               ((n + 1 + 1 : ℕ) * (y - x₀) ^ (n + 1)) * (R.map b - R.map a)
             := by
               rw [(RFunction.isDerivableAt.toDeriv ⟨_, hR y hy⟩).unique (hR y hy),
                 (RFunction.isDerivableAt.toDeriv ⟨_, hG y⟩).unique (hG y)] at heq
               exact heq
          => (f' y - (TaylorPolynomial F' x₀ n).map y) *
               (x - x₀) ^ (n + 1 + 1) =
               ((n + 1 + 1 : ℕ) * (y - x₀) ^ (n + 1)) * R.map x
             := by
               rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
               · rw [hRzero, hGzero, sub_zero, sub_zero] at this
                 exact this
               · rw [hRzero, hGzero, zero_sub, zero_sub, mul_neg, mul_neg,
                   neg_inj] at this
                 exact this
    script_claim_exist ⟨ξ, hξ, hval⟩ : ∃ ξ ∈ Ioo a b, f' y =
        (TaylorPolynomial F' x₀ n).map y +
        (NthDiff (n + 1) F').map ξ / (n + 1)! * (y - x₀) ^ (n + 1)
    · rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨ξ, hξ, hval⟩ := ih hy.1 (Or.inl ⟨rfl, rfl⟩)
          (fun k hk t ht => by
            rw [nthDiff_diff]
            exact hc (k + 1) (by omega) t ⟨ht.1, ht.2.trans hy.2.le⟩)
          (fun k hk t ht => by
            rw [nthDiff_diff]
            exact hd (k + 1) (by omega) t ⟨ht.1, ht.2.trans hy.2⟩)
        exact ⟨ξ, ⟨hξ.1, hξ.2.trans hy.2⟩, hval⟩
      · obtain ⟨ξ, hξ, hval⟩ := ih hy.2 (Or.inr ⟨rfl, rfl⟩)
          (fun k hk t ht => by
            rw [nthDiff_diff]
            exact hc (k + 1) (by omega) t ⟨hy.1.le.trans ht.1, ht.2⟩)
          (fun k hk t ht => by
            rw [nthDiff_diff]
            exact hd (k + 1) (by omega) t ⟨hy.1.trans ht.1, ht.2⟩)
        exact ⟨ξ, ⟨hy.1.trans hξ.1, hξ.2⟩, hval⟩
    script_exists ξ with hξ
    have hp : (y - x₀) ^ (n + 1) ≠ 0 := by
      suffices h : y - x₀ ≠ 0 from pow_ne_zero _ h
      grind
    script_infer
      f' y = (TaylorPolynomial F' x₀ n).map y +
        (NthDiff (n + 1) F').map ξ / (n + 1)! * (y - x₀) ^ (n + 1)
        => f' y - (TaylorPolynomial F' x₀ n).map y =
             (NthDiff (n + 1 + 1) F).map ξ / (n + 1)! * (y - x₀) ^ (n + 1)
           := by
             rw [nthDiff_diff] at hval
             exact sub_eq_iff_eq_add.mpr (hval.trans (add_comm _ _))
        => ((NthDiff (n + 1 + 1) F).map ξ / (n + 1)! *
             (x - x₀) ^ (n + 1 + 1)) * (y - x₀) ^ (n + 1) =
             ((n + 1 + 1 : ℕ) * R.map x) * (y - x₀) ^ (n + 1)
           := by
             rw [this] at hstep
             calc
               _ = ((NthDiff (n + 1 + 1) F).map ξ / (n + 1)! *
                     (y - x₀) ^ (n + 1)) * (x - x₀) ^ (n + 1 + 1)
                   := mul_right_comm _ _ _
               _ = ((n + 1 + 1 : ℕ) * (y - x₀) ^ (n + 1)) * R.map x := hstep
               _ = _ := mul_right_comm _ _ _
        => (NthDiff (n + 1 + 1) F).map ξ / (n + 1)! *
             (x - x₀) ^ (n + 1 + 1) = (n + 1 + 1 : ℕ) * R.map x
           := mul_right_cancel₀ hp ?_
        => R.map x = ((NthDiff (n + 1 + 1) F).map ξ / (n + 1)! *
             (x - x₀) ^ (n + 1 + 1)) / (n + 1 + 1 : ℕ)
           := by
             apply (eq_div_iff (by positivity)).mpr
             rw [mul_comm]
             exact this.symm
        => R.map x = (NthDiff (n + 1 + 1) F).map ξ / (n + 1 + 1)! *
             (x - x₀) ^ (n + 1 + 1)
           := by
             rw [this, Nat.factorial_succ (n + 1), Nat.cast_mul]
             simp only [div_eq_mul_inv, mul_inv_rev]
             ring
        => f x = (TaylorPolynomial F x₀ (n + 1)).map x +
             (NthDiff (n + 1 + 1) F).map ξ / (n + 1 + 1)! * (x - x₀) ^ (n + 1 + 1)
           := by
             change f x - (TaylorPolynomial F x₀ (n + 1)).map x = _ at this
             rw [← this]
             symm
             apply add_sub_cancel _ _

lemma deriv_limit {F : RFunction} {a d : ℝ} (hd : Deriv F a d) :
    FuncLimit F a (F.map a) := by
  apply FuncLimit.fromFuncLimitExpr
  · obtain ⟨δ, hδ, hdom⟩ := hd.1
    script_exists δ with hδ
    intro t ht
    script_exact_proj hdom ht
  · script_infer
      Deriv F a d => D F.map a =. the d
                     := hd.toDerivExpr
                  => ∃ d, D F.map a =. the d
                     := ⟨d, ?_⟩
                  => lim a F.map =. the (F.map a)
                     := DerivExpr.toCont ?_

lemma power_limit (a : ℝ) {n : ℕ} (hn : 0 < n)
  : FuncLimit (total_fun t ↦ (t - a) ^ n) a 0
:= script
  use_expr
  | calculation =>
    calc
      lim a (fun t ↦ (t - a) ^ n) =. the ((a - a) ^ n) := by
        lim_cont
        rw [sub_eq_add_neg]
      _ = the 0 := by rw [sub_self, zero_pow (Nat.ne_of_gt hn)]
  | side =>
    exists 1 with zero_lt_one
    apply subset_univ _

lemma remainder_limit {F : RFunction} {a : ℝ} {n : ℕ}
    (h : isNthDerivableAt (n + 1) F a)
  : FuncLimit (F - TaylorPolynomial F a (n + 1)) a 0
:= by
  script_claim_exist ⟨d, hd⟩ : ∃ d, NthDeriv 1 F a d
  · exact h.mono (by omega)
  script_infer
    Deriv F a d  => FuncLimit F a (F.map a)
                    := deriv_limit hd.deriv
                 => FuncLimit (F - TaylorPolynomial F a (n + 1)) a
                      (F.map a - (TaylorPolynomial F a (n + 1)).map a)
                    := FuncLimit.Sub ?_ (deriv_limit (polynomial_deriv F a a n))
                 => FuncLimit (F - TaylorPolynomial F a (n + 1)) a 0
                    := by
                      rw [polynomial_self, sub_self] at this
                      exact this

/- Repeated L'Hospital, stopping at the first-order definition of derivative.
The successor step uses the framework's currently admitted L'Hospital rule. -/


/-! # Taylor's Formula -/

section
variable {N : ℕ} {F : RFunction} {x₀ x : ℝ}

/-- Taylor's Expansion with Peano's Remainder Term -/
theorem TaylorExpansion_Peano
    (h_N : N > 0)
    (h_deriv : isNthDerivableAt N F x₀)
  : ∃ R : RFunction,
      F = TaylorPolynomial F x₀ N + R
      ∧ isHigherInfinitesimal R ⟨fun x ↦ (x - x₀) ^ N, Iii⟩ x₀
:= by
  let F' := Diff F
  let f' := F'.map
  script_obtain_exist ⟨n, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_N)
  script_provide F - TaylorPolynomial F x₀ (n + 1)
  subst N
  script_split_and
  · apply RFunction.ext
    · funext t
      change F.map t = (TaylorPolynomial F x₀ (n + 1)).map t +
        (F.map t - (TaylorPolynomial F x₀ (n + 1)).map t)
      ring_nf
    · change F.domain = Iii ∩ (F.domain ∩ Iii)
      tauto_set -- simp only [Set.inter_univ, Set.univ_inter]
  · script_split_and
    · exact remainder_limit h_deriv
    · script_split_and
      · exact power_limit x₀ (by omega)
      · induction n generalizing F with
        | zero =>
          let R := F - TaylorPolynomial F x₀ 1
          script_obtain_exist ⟨d, hd⟩ := h_deriv
          script_infer
            Deriv F x₀ d => F.isDerivableAt x₀
                          := ⟨d, hd.deriv⟩
                        => hdF : Deriv F x₀ (f' x₀)
                          := (?_).toDeriv
          script_claim hdR : Deriv R x₀ 0
          · script_infer
              Deriv F x₀ (f' x₀)
                => Deriv R x₀ (f' x₀ - (TaylorPolynomial F' x₀ 0).map x₀)
                  := hdF.Sub (polynomial_deriv F x₀ x₀ 0)
                => Deriv R x₀ 0
                  := by
                    rw [polynomial_self, sub_self] at this
                    exact this
          have hRa : R.map x₀ = 0 := by
            change F.map x₀ - (TaylorPolynomial F x₀ 1).map x₀ = 0
            rw [polynomial_self, sub_self]
          script_obtain_exist ⟨δ, hδ, hdom⟩ := hdR.1
          apply hdR.Congr
          script_exists δ with hδ
          constructor
          · intro t ht
            script_split_and
            · script_split_and
              · script_exact_proj hdom ht
              · trivial
            · change (t - x₀) ^ (0 + 1) ≠ 0
              suffices t ≠ x₀ by grind
              script_exact_proj ht
          · intro t ht
            change (R.map t - R.map x₀) / (t - x₀) = R.map t / (t - x₀) ^ (0 + 1)
            rw [hRa]
            simp
        | succ n ih =>
          let R := F - TaylorPolynomial F x₀ (n + 1 + 1)
          let R' := Diff R
          let r' := R'.map
          let G := total_fun t ↦ (t - x₀) ^ (n + 1 + 1)
          let G' := Diff G
          let g' := G'.map
          let S := F' - TaylorPolynomial F' x₀ (n + 1)
          let Q := total_fun t ↦ (t - x₀) ^ (n + 1)
          script_infer
            isNthDerivableAt (n + 1 + 1) F x₀
              => isNthDerivableAt (n + 1) F' x₀ := nth_shift h_deriv
              => hsmall : FuncLimit (S / Q) x₀ 0 := ih (by omega) ?_
              => FuncLimit (((n + 1 + 1 : ℕ) : ℝ)⁻¹ • (S / Q)) x₀
                  (((n + 1 + 1 : ℕ) : ℝ)⁻¹ * 0)
                := FuncLimit.SMul ?_
              => hscaled : FuncLimit (((n + 1 + 1 : ℕ) : ℝ)⁻¹ • (S / Q)) x₀ 0
                := by
                  rw [mul_zero] at this
                  exact this
          have hG : ∀ t, Deriv G t ((n + 1 + 1 : ℕ) * (t - x₀) ^ (n + 1)) := by
            intro t
            use_expr
            case calculation =>
              script_given_proper
              calc
                D G.map t =? the (n + 1 + 1 : ℕ) * D (fun s ↦ s - x₀) t *
                              the ((t - x₀) ^ (n + 1 + 1 - 1)) := DerivExpr.MSPow
                _ = the (n + 1 + 1 : ℕ) * the 1 * the ((t - x₀) ^ (n + 1 + 1 - 1))
                    := by deriv_calc
                _ = the ((n + 1 + 1 : ℕ) * (t - x₀) ^ (n + 1)) := by
                  change the ((n + 1 + 1 : ℕ) * 1 * (t - x₀) ^ (n + 1 + 1 - 1)) = _
                  rw [mul_one, Nat.add_sub_cancel]
            case side =>
              script_exists 1 with zero_lt_one
              apply subset_univ _
          script_claim hquot : FuncLimit (R' / G') x₀ 0
          · script_obtain_exist ⟨δ, hδ, hdom⟩ := hsmall.1
            have hR : ∀ t ∈ Nbhd x₀ δ, Deriv R t (S.map t) := by
              intro t ht
              script_infer
                t ∈ Nbhd x₀ δ => t ∈ F'.domain
                                := (hdom ht).1.1.1
                            => Deriv F t (f' t)
                                := RFunction.isDerivableAt.toDeriv ?_
                            => Deriv R t (S.map t)
                                := Deriv.Sub ?_ (polynomial_deriv F x₀ t (n + 1))
            have hGne : ∀ t ∈ Nbhd x₀ δ, (n + 1 + 1 : ℕ) * (t - x₀) ^ (n + 1) ≠ (0 : ℝ) := by
              intro t ht
              exact mul_ne_zero (by positivity) (pow_ne_zero _ (sub_ne_zero.mpr ht.2.2))
            apply hscaled.Congr
            script_exists δ with hδ
            constructor
            · intro t ht
              refine ⟨⟨⟨_, hR t ht⟩, ⟨_, hG t⟩⟩, ?_⟩
              change (Diff G).map t ≠ 0
              rw [(RFunction.isDerivableAt.toDeriv ⟨_, hG t⟩).unique (hG t)]
              exact hGne t ht
            · intro t ht
              change ((n + 1 + 1 : ℕ) : ℝ)⁻¹ * (S.map t / (t - x₀) ^ (n + 1))
                  = (Diff R).map t / (Diff G).map t
              rw [(RFunction.isDerivableAt.toDeriv ⟨_, hR t ht⟩).unique (hR t ht),
                (RFunction.isDerivableAt.toDeriv ⟨_, hG t⟩).unique (hG t)]
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
          script_claim hR_limit : FuncLimit R x₀ 0
          · exact remainder_limit h_deriv
          script_claim hG_limit : FuncLimit G x₀ 0
          · exact power_limit x₀ (by omega)
          script_infer
            FuncLimit (R' / G') x₀ 0 => FuncLimit (R / G) x₀ 0
              := FuncLimit.L'Hospital_x₀_zero hR_limit hG_limit hquot

/-- Taylor's Expansion with Lagrange's Remainder Term (for `x < x₀`) -/
theorem TaylorExpansion_Lagrange_left
    (h_x_lt_x₀ : x < x₀)
    (h_deriv₁ : ∀ k ≤ N,
      Icc x x₀ ⊆ (NthDiff k F).domain ∧ (NthDiff k F).isContinuous)
    (h_deriv₂ : Ioo x x₀ ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x x₀,
      F.map x = (TaylorPolynomial F x₀ N).map x +
      (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1))
:= by
  apply lagrange_cauchy h_x_lt_x₀ (Or.inr ⟨rfl, rfl⟩)
  · intro k hk t ht
    script_infer
      t ∈ Icc x x₀ => t ∈ (NthDiff k F).domain
                      := (h_deriv₁ k hk).1 ht
                   => (NthDiff k F).isContinuousAt t
                      := (h_deriv₁ k hk).2 t ?_
  · intro k hk t ht
    by_cases heq : k = N
    · rw [heq]
      script_infer
        t ∈ Ioo x x₀ => t ∈ (NthDiff (N + 1) F).domain
                        := h_deriv₂ ht
                     => (NthDiff N F).isDerivableAt t
                        := ?_
    · script_infer
        t ∈ Ioo x x₀ => t ∈ Icc x x₀
                        := ⟨ht.1.le, ht.2.le⟩
                     => t ∈ (NthDiff (k + 1) F).domain
                        := (h_deriv₁ (k + 1) (by omega)).1 ?_
                     => (NthDiff k F).isDerivableAt t
                        := ?_

/-- Taylor's Expansion with Lagrange's Remainder Term (for `x > x₀`) -/
theorem TaylorExpansion_Lagrange_right
    (h_x_gt_x₀ : x > x₀)
    (h_deriv₁ : ∀ k ≤ N,
      Icc x₀ x ⊆ (NthDiff k F).domain ∧ (NthDiff k F).isContinuous)
    (h_deriv₂ : Ioo x₀ x ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x₀ x,
      F.map x = (TaylorPolynomial F x₀ N).map x +
      (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1))
:= by
  apply lagrange_cauchy h_x_gt_x₀ (Or.inl ⟨rfl, rfl⟩)
  · intro k h_k t h_t
    script_infer
      t ∈ Icc x₀ x => t ∈ (NthDiff k F).domain
                      := (h_deriv₁ k h_k).1 h_t
                   => (NthDiff k F).isContinuousAt t
                      := (h_deriv₁ k h_k).2 t ?_
  · intro k h_k t h_t
    by_cases heq : k = N
    · rw [heq]
      script_infer
        t ∈ Ioo x₀ x => t ∈ (NthDiff (N + 1) F).domain
                        := h_deriv₂ h_t
                     => (NthDiff N F).isDerivableAt t
                        := ?_
    · script_infer
        t ∈ Ioo x₀ x => t ∈ Icc x₀ x
                        := script
                          split_and
                          · apply le_of_lt
                            exact_proj h_t
                          · apply le_of_lt
                            exact_proj h_t
                     => t ∈ (NthDiff (k + 1) F).domain
                        := (h_deriv₁ (k + 1) (by omega)).1 ?_
                     => (NthDiff k F).isDerivableAt t
                        := ?_

end


page_end
