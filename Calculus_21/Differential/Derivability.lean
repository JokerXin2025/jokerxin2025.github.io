import Calculus_21.Differential.Elementary


/-! # First-order derivability rules

These rules use the project's punctured-neighborhood derivative. In particular,
derivability does not imply membership of the center in the function's domain.
-/

theorem Deriv.isDerivableAt {F : RFunction} {x d : ℝ}
    (h : Deriv F x d) : F.isDerivableAt x := ⟨d, h⟩

namespace RFunction

theorem isDerivableIn.at {F : RFunction} {I : Set ℝ} {x : ℝ}
    (h : F.isDerivableIn I) (hx : x ∈ I) : F.isDerivableAt x := h x hx

theorem isDerivable.at {F : RFunction} {x : ℝ}
    (h : F.isDerivable) (hx : x ∈ F.domain) : F.isDerivableAt x := h x hx

theorem isDerivableIn.mono {F : RFunction} {I J : Set ℝ}
    (h : F.isDerivableIn I) (hJI : J ⊆ I) : F.isDerivableIn J :=
  fun _ hx => h _ (hJI hx)

end RFunction

variable {F G : RFunction} {x₀ k c : ℝ} {n : ℕ}

theorem Derivability.Neg
  : F.isDerivableAt x₀ → (-F).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩
  exact hd.Neg.isDerivableAt

theorem Derivability.SMul
  : F.isDerivableAt x₀ → (k • F).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩
  exact hd.SMul.isDerivableAt

theorem Derivability.Add
  : F.isDerivableAt x₀ → G.isDerivableAt x₀ → (F + G).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩ ⟨e, he⟩
  exact (hd.Add he).isDerivableAt

theorem Derivability.Sub
  : F.isDerivableAt x₀ → G.isDerivableAt x₀ → (F - G).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩ ⟨e, he⟩
  exact (hd.Sub he).isDerivableAt

theorem Derivability.Mul
  : F.isDerivableAt x₀ → G.isDerivableAt x₀ → (F * G).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩ ⟨e, he⟩
  exact (hd.Mul he).isDerivableAt

theorem Derivability.Div
    (h_dom : G.map x₀ ≠ 0)
  : F.isDerivableAt x₀ → G.isDerivableAt x₀ → (F / G).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩ ⟨e, he⟩
  exact (Deriv.Div h_dom hd he).isDerivableAt

theorem Derivability.Inv
    (h_dom : F.map x₀ ≠ 0)
  : F.isDerivableAt x₀ → F⁻¹.isDerivableAt x₀
:= by
  intro ⟨d, hd⟩
  exact (hd.Inv h_dom).isDerivableAt

theorem Derivability.MSPow
  : F.isDerivableAt x₀ → (F ^ n).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩
  exact hd.MSPow.isDerivableAt

/-- The outer center must be in the outer domain, even for a constant inner map.
No membership assumption on the inner center is needed. -/
theorem Derivability.Comp
    (h_dom : G.map x₀ ∈ F.domain)
  : F.isDerivableAt (G.map x₀) → G.isDerivableAt x₀ → (F ⊙ G).isDerivableAt x₀
:= by
  intro ⟨d, hd⟩ ⟨e, he⟩
  exact (Deriv.Comp he hd h_dom).isDerivableAt

theorem Derivability.Constant
  : (Constant c).isDerivableAt x₀
:= (Deriv.Constant x₀).isDerivableAt

theorem Derivability.Identity
  : Identity.isDerivableAt x₀
:= (Deriv.Identity x₀).isDerivableAt
