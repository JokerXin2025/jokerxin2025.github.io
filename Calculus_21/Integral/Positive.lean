/-
    «Calculus_21».Integral.Positive
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.RiemannSum
set_option linter.style.header false


/-! # Positive-Orientation Riemann Integrals -/

namespace Integral
open PartitionNet

/-- Domain coverage and convergence of all tagged Riemann sums. -/
def PositiveIntegral (F : RFunction) (a b value : ℝ) : Prop :=
  ∃ h_ab : a < b, Icc a b ⊆ F.domain ∧ NetLimit (riemannNet F h_ab) value

namespace PositiveIntegral
variable {F G : RFunction} {a b v w : ℝ}

theorem endpoints_lt (h : PositiveIntegral F a b v)
  : a < b
:= h.1

theorem domain (h : PositiveIntegral F a b v)
  : Icc a b ⊆ F.domain
:= h.2.1

theorem unique (h₁ : PositiveIntegral F a b v) (h₂ : PositiveIntegral F a b w)
  : v = w
:= h₁.2.2.unique h₂.2.2

theorem mesh_iff
  : PositiveIntegral F a b v ↔ a < b ∧ Icc a b ⊆ F.domain ∧
      ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
        P.mesh < δ → |P.sum F - v| < ε
:= by
  constructor
  · rintro ⟨hab, hdom, hlim⟩
    exact ⟨hab, hdom, (riemannNet_limit_iff hab).mp hlim⟩
  · rintro ⟨hab, hdom, hlim⟩
    exact ⟨hab, hdom, (riemannNet_limit_iff hab).mpr hlim⟩

theorem congr (h : PositiveIntegral F a b v)
    (h_dom : Icc a b ⊆ G.domain)
    (h_eq : ∀ x ∈ Icc a b, F.map x = G.map x)
  : PositiveIntegral G a b v
:= by
  refine ⟨h.1, h_dom, h.2.2.Congr ?_⟩
  obtain ⟨P⟩ := (TaggedPartition.directedSet h.1).nonempty
  exact ⟨P, fun Q _ => Q.sum_congr h_eq⟩

theorem const (c : ℝ) (h_ab : a < b)
  : PositiveIntegral (Constant c) a b (c * (b - a))
:= by
  refine ⟨h_ab, fun _ _ => trivial, ?_⟩
  apply (NetLimit.Const (D := TaggedPartition.directedSet h_ab) (c * (b - a))).Congr
  obtain ⟨P⟩ := (TaggedPartition.directedSet h_ab).nonempty
  exact ⟨P, fun Q _ => (Q.sum_const c).symm⟩

theorem add (hF : PositiveIntegral F a b v) (hG : PositiveIntegral G a b w)
  : PositiveIntegral (F + G) a b (v + w)
:= by
  refine ⟨hF.1, fun x hx => ⟨hF.domain hx, hG.domain hx⟩, ?_⟩
  apply (hF.2.2.Add hG.2.2).Congr
  obtain ⟨P⟩ := (TaggedPartition.directedSet hF.1).nonempty
  exact ⟨P, fun Q _ => (Q.sum_add F G).symm⟩

theorem smul (c : ℝ) (h : PositiveIntegral F a b v)
  : PositiveIntegral (c • F) a b (c * v)
:= by
  refine ⟨h.1, h.domain, ?_⟩
  apply (h.2.2.SMul c).Congr
  obtain ⟨P⟩ := (TaggedPartition.directedSet h.1).nonempty
  exact ⟨P, fun Q _ => (Q.sum_smul c F).symm⟩

theorem mono (hF : PositiveIntegral F a b v) (hG : PositiveIntegral G a b w)
    (h_le : ∀ x ∈ Icc a b, F.map x ≤ G.map x)
  : v ≤ w
:= by
  apply hF.2.2.Mono hG.2.2
  obtain ⟨P⟩ := (TaggedPartition.directedSet hF.1).nonempty
  exact ⟨P, fun Q _ => Q.sum_mono h_le⟩

theorem cauchy_iff (h_ab : a < b) (h_dom : Icc a b ⊆ F.domain)
  : (∃ v, PositiveIntegral F a b v) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P Q : TaggedPartition a b,
        P.mesh < δ → Q.mesh < δ → |P.sum F - Q.sum F| < ε
:= by
  constructor
  · rintro ⟨v, hv⟩
    exact (riemannNet_cauchy_iff h_ab).mp hv.2.2.Cauchy
  · intro h
    obtain ⟨v, hv⟩ := ((riemannNet_cauchy_iff h_ab).mpr h).Converges
    exact ⟨v, h_ab, h_dom, hv⟩

/-- Convergence for all tags forces boundedness on the entire closed interval. -/
theorem bounded (h : PositiveIntegral F a b v)
  : ∃ M > 0, ∀ x ∈ Icc a b, |F.map x| < M
:= by
  classical
  obtain ⟨δ, hδ, h_near⟩ := (mesh_iff.mp h).2.2 1 zero_lt_one
  obtain ⟨P, hP⟩ := TaggedPartition.exists_mesh_lt h.1 hδ
  let bound : Fin P.count → ℝ := fun i => |F.map (P.tag i)| + 2 / P.width i
  have h_ne : (Finset.univ : Finset (Fin P.count)).Nonempty :=
    ⟨⟨0, P.count_pos⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ bound h_ne
  refine ⟨bound k + 1, ?_, ?_⟩
  · dsimp [bound]
    have hw := P.width_pos k
    positivity
  · intro x hx
    obtain ⟨i, hi⟩ := P.exists_cell_of_mem hx
    let Q := P.replaceTag i x hi
    have hQ : Q.mesh < δ := hP
    have hp := abs_lt.mp (h_near P hP)
    have hq := abs_lt.mp (h_near Q hQ)
    have hdiff : |Q.sum F - P.sum F| < 2 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    change |(P.replaceTag i x hi).sum F - P.sum F| < 2 at hdiff
    rw [P.sum_replaceTag, abs_mul, abs_of_pos (P.width_pos i)] at hdiff
    have hd := (lt_div_iff₀ (P.width_pos i)).mpr hdiff
    have htri : |F.map x| ≤ |F.map x - F.map (P.tag i)| + |F.map (P.tag i)| := by
      calc
        |F.map x| = |(F.map x - F.map (P.tag i)) + F.map (P.tag i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hmax := hk i (Finset.mem_univ i)
    change |F.map (P.tag i)| + 2 / P.width i ≤ bound k at hmax
    linarith

end PositiveIntegral
end Integral


page_end
