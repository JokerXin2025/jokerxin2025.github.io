/-
    «Calculus_21».Ind_Integral.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Differential.Defs
set_option linter.style.header false


/-! # Antiderivative & Integrability (RFunction-based, `Deriv` relation) -/

/-- **Core concept**: `F` is an antiderivative of `f` (RFunction-based, with domain).

    Uses `RFunction` and the `Deriv` relation (not `D` expression), mirroring:
    * `Deriv (F : RFunction) (x₀ D : ℝ) : Prop`
    * `FuncLimit (F : RFunction) (x₀ L : ℝ) : Prop`

    Semantics: for every `x` in `F.domain`, **if** `F` has a derivative `d` at `x`,
    then `d` must equal `f.map x`.  Formally:
    `∀ x ∈ F.domain, ∀ d, Deriv F x d → d = f.map x`

    This is relaxed: `F` does NOT have to be differentiable everywhere on its
    domain — only that wherever it IS differentiable, the derivative matches `f`.
    This allows e.g. `ln` (domain `Ioi 0`) to be an antiderivative of `1/x`. -/
def HasAntideriv (f F : RFunction) : Prop :=
  ∀ x ∈ F.domain, ∀ d, Deriv F x d → d = f.map x

/-- `f` has an antiderivative (RFunction version) -/
abbrev isIntegrable (f : RFunction) : Prop :=
  ∃ F : RFunction, HasAntideriv f F

/-! # Properties of `HasAntideriv` (RFunction version) -/

lemma HasAntideriv.add_const {f F : RFunction} {C : ℝ}
    (h_F : HasAntideriv f F)
  : HasAntideriv f ⟨F.map + const C, F.domain⟩
:= by sorry

page_end
