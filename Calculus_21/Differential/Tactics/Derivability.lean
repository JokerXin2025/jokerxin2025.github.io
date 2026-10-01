/-
    «Calculus_21».Differential.Tactics.Derivability
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Differential.Derivability

open RFunction


/-! # Derivability Inference for `RFunction` -/

namespace AutoDerivability
variable {F G : RFunction} {x : ℝ}

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma identityDomain
  : x ∈ Identity.domain
:= mem_univ _

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma constantDomain {c : ℝ} : x ∈ (Constant c).domain := mem_univ _

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma addDomain
  : x ∈ (F + G).domain ↔ x ∈ F.domain ∧ x ∈ G.domain
:= by rfl

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma subDomain
  : x ∈ (F - G).domain ↔ x ∈ F.domain ∧ x ∈ G.domain
:= by rfl

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma mulDomain
  : x ∈ (F * G).domain ↔ x ∈ F.domain ∧ x ∈ G.domain
:= by rfl

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma divDomain
  : x ∈ (F / G).domain ↔ (x ∈ F.domain ∧ x ∈ G.domain) ∧ G.map x ≠ 0
:= by rfl

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma invDomain
  : x ∈ F⁻¹.domain ↔ x ∈ F.domain ∧ F.map x ≠ 0
:= by rfl

@[aesop norm simp (rule_sets := [AutoDerivability])]
private lemma compDomain
  : x ∈ (F ⊙ G).domain ↔ x ∈ G.domain ∧ G.map x ∈ F.domain
:= by rfl

end AutoDerivability

-- Project existing whole-expression facts before safe operation rules split them.
attribute [aesop safe -10 forward (rule_sets := [AutoDerivability])]
  Deriv.isDerivableAt

attribute [aesop safe forward (rule_sets := [AutoDerivability])]
  isDerivableIn.at isDerivable.at

attribute [aesop safe apply (rule_sets := [AutoDerivability])]
  Derivability.Constant Derivability.Identity
  Derivability.Neg Derivability.SMul Derivability.Inv Derivability.MSPow
  Derivability.Add Derivability.Sub Derivability.Mul Derivability.Div
  Derivability.Comp


macro "infer_derivability" : tactic => `(tactic|
  aesop
    (rule_sets := [AutoDerivability])
    (config := { useSimpAll := false, terminal := true })
)
script_macro "infer_derivability" => `(tactic| infer_derivability)
