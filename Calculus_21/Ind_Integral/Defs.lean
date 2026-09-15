/-
    «Calculus_21».Ind_Integral.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.Defs
import «Calculus_21».Differential.Defs
set_option linter.style.header false


/-! # Antiderivative & Integrability (Function-based, `Deriv` relation) -/

/-- **Core concept**: `F` is an antiderivative of `f` (Function-based, with domain).

    Uses `Function` and the `Deriv` relation (not `D` expression), mirroring:
    * `Deriv (F : Function) (x₀ D : ℝ) : Prop`
    * `FuncLimit (F : Function) (x₀ L : ℝ) : Prop`

    Semantics: for every `x` in `F.domain`, **if** `F` has a derivative `d` at `x`,
    then `d` must equal `f.map x`.  Formally:
    `∀ x ∈ F.domain, ∀ d, Deriv F x d → d = f.map x`

    This is relaxed: `F` does NOT have to be differentiable everywhere on its
    domain — only that wherever it IS differentiable, the derivative matches `f`.
    This allows e.g. `ln` (domain `Ioi 0`) to be an antiderivative of `1/x`. -/
def HasAntideriv (f F : Function) : Prop :=
  ∀ x ∈ F.domain, ∀ d, Deriv F x d → d = f.map x

/-- `f` has an antiderivative (Function version) -/
abbrev isIntegrable (f : Function) : Prop :=
  ∃ F : Function, HasAntideriv f F

/-! # Properties of `HasAntideriv` (Function version) -/

lemma HasAntideriv.add_const {f F : Function} {C : ℝ}
    (h_F : HasAntideriv f F)
  : HasAntideriv f ⟨F.map + const C, F.domain⟩
:= by sorry

page_end
