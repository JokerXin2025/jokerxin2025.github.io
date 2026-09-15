/-
    «Calculus_21».Limit.Tactics.Equiv
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Infinitesimal.Equivalent
import «Calculus_21».Limit.Tactics.Cont
set_option linter.style.header false


/-! # Preparations -/

class AutoEquiv (f : ℝ → ℝ) (f' : outParam (ℝ → ℝ)) (x₀ : ℝ)
    (cond : outParam Prop) where
  equiv : cond → lim (f / f') x₀ =. the 1

class AutoLeftEquiv (f : ℝ → ℝ) (f' : outParam (ℝ → ℝ)) (x₀ : ℝ)
    (cond : outParam Prop) where
  equiv : cond → lim₋ (f / f') x₀ =. the 1

class AutoRightEquiv (f : ℝ → ℝ) (f' : outParam (ℝ → ℝ)) (x₀ : ℝ)
    (cond : outParam Prop) where
  equiv : cond → lim₊ (f / f') x₀ =. the 1

private instance equiv_mul {f f' g g' : ℝ → ℝ} {x₀ : ℝ} {c₁ c₂ : Prop}
    [h_f : AutoEquiv f f' x₀ c₁] [h_g : AutoEquiv g g' x₀ c₂]
  : AutoEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g' x) x₀ (c₁ ∧ c₂) where
  equiv := sorry

private instance equiv_mul' {f f' g : ℝ → ℝ} {x₀ : ℝ} {c₁ : Prop}
    [h_f : AutoEquiv f f' x₀ c₁]
  : AutoEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g x) x₀ c₁ where
  equiv := sorry

private instance equiv_mul'' {f g g' : ℝ → ℝ} {x₀ : ℝ} {c₂ : Prop}
    [h_g : AutoEquiv g g' x₀ c₂]
  : AutoEquiv (fun x ↦ f x * g x) (fun x ↦ f x * g' x) x₀ c₂ where
  equiv := sorry

private instance leftequiv_mul {f f' g g' : ℝ → ℝ} {x₀ : ℝ} {c₁ c₂ : Prop}
    [h_f : AutoLeftEquiv f f' x₀ c₁] [h_g : AutoLeftEquiv g g' x₀ c₂]
  : AutoLeftEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g' x) x₀ (c₁ ∧ c₂) where
  equiv := sorry

private instance leftequiv_mul' {f f' g : ℝ → ℝ} {x₀ : ℝ} {c₁ : Prop}
    [h_f : AutoLeftEquiv f f' x₀ c₁]
  : AutoLeftEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g x) x₀ c₁ where
  equiv := sorry

private instance leftequiv_mul'' {f g g' : ℝ → ℝ} {x₀ : ℝ} {c₂ : Prop}
    [h_g : AutoLeftEquiv g g' x₀ c₂]
  : AutoLeftEquiv (fun x ↦ f x * g x) (fun x ↦ f x * g' x) x₀ c₂ where
  equiv := sorry

private instance rightequiv_mul {f f' g g' : ℝ → ℝ} {x₀ : ℝ} {c₁ c₂ : Prop}
    [h_f : AutoRightEquiv f f' x₀ c₁] [h_g : AutoRightEquiv g g' x₀ c₂]
  : AutoRightEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g' x) x₀ (c₁ ∧ c₂) where
  equiv := sorry

private instance rightequiv_mul' {f f' g : ℝ → ℝ} {x₀ : ℝ} {c₁ : Prop}
    [h_f : AutoRightEquiv f f' x₀ c₁]
  : AutoRightEquiv (fun x ↦ f x * g x) (fun x ↦ f' x * g x) x₀ c₁ where
  equiv := sorry

private instance rightequiv_mul'' {f g g' : ℝ → ℝ} {x₀ : ℝ} {c₂ : Prop}
    [h_g : AutoRightEquiv g g' x₀ c₂]
  : AutoRightEquiv (fun x ↦ f x * g x) (fun x ↦ f x * g' x) x₀ c₂ where
  equiv := sorry

private instance equiv_SqrtEquiv
  : AutoEquiv (fun x ↦ √(1 + x) - 1) (· / 2) 0 True where
  equiv := directly SqrtEquiv (by lim_cont)

private instance equiv_SqrtEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ √(1 + f x) - 1) (fun x ↦ f x / 2) x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SqrtEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_SqrtEquiv
  : AutoLeftEquiv (fun x ↦ √(1 + x) - 1) (· / 2) 0 True where
  equiv := directly SqrtLeftEquiv (by lim_cont)

private instance leftequiv_SqrtEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ √(1 + f x) - 1) (fun x ↦ f x / 2) x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SqrtLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_SqrtEquiv
  : AutoRightEquiv (fun x ↦ √(1 + x) - 1) (· / 2) 0 True where
  equiv := directly SqrtRightEquiv (by lim_cont)

private instance rightequiv_SqrtEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ √(1 + f x) - 1) (fun x ↦ f x / 2) x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SqrtRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_PowerEquiv {a : ℝ}
  : AutoEquiv (fun x ↦ (1 + x) ^ a - 1) (a * ·) 0 (a ≠ 0) where
  equiv := by
    intro h_dom
    apply PowerEquiv
    · exact h_dom
    · lim_cont

private instance equiv_PowerEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ (1 + f x) ^ a - 1) (fun x ↦ a * f x) x₀ (c ∧ L = 0 ∧ a ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply PowerEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance leftequiv_PowerEquiv {a : ℝ}
  : AutoLeftEquiv (fun x ↦ (1 + x) ^ a - 1) (a * ·) 0 (a ≠ 0) where
  equiv := by
    intro h_dom
    apply PowerLeftEquiv
    · exact h_dom
    · lim_cont

private instance leftequiv_PowerEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ (1 + f x) ^ a - 1) (fun x ↦ a * f x) x₀ (c ∧ L = 0 ∧ a ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply PowerLeftEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance rightequiv_PowerEquiv {a : ℝ}
  : AutoRightEquiv (fun x ↦ (1 + x) ^ a - 1) (a * ·) 0 (a ≠ 0) where
  equiv := by
    intro h_dom
    apply PowerRightEquiv
    · exact h_dom
    · lim_cont

private instance rightequiv_PowerEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ (1 + f x) ^ a - 1) (fun x ↦ a * f x) x₀ (c ∧ L = 0 ∧ a ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply PowerRightEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance equiv_NPowerEquiv_ℤ {n : ℤ}
  : AutoEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerEquiv_ℤ
    · exact h_dom
    · lim_cont

private instance equiv_NPowerEquiv_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerEquiv_ℤ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance leftequiv_NPowerEquiv_ℤ {n : ℤ}
  : AutoLeftEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerLeftEquiv_ℤ
    · exact h_dom
    · lim_cont

private instance leftequiv_NPowerEquiv_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerLeftEquiv_ℤ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance rightequiv_NPowerEquiv_ℤ {n : ℤ}
  : AutoRightEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerRightEquiv_ℤ
    · exact h_dom
    · lim_cont

private instance rightequiv_NPowerEquiv_ℤ' {f : ℝ → ℝ} {n : ℤ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerRightEquiv_ℤ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance equiv_NPowerEquiv_ℕ {n : ℕ}
  : AutoEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerEquiv_ℕ
    · exact h_dom
    · lim_cont

private instance equiv_NPowerEquiv_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerEquiv_ℕ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance leftequiv_NPowerEquiv_ℕ {n : ℕ}
  : AutoLeftEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerLeftEquiv_ℕ
    · exact h_dom
    · lim_cont

private instance leftequiv_NPowerEquiv_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerLeftEquiv_ℕ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance rightequiv_NPowerEquiv_ℕ {n : ℕ}
  : AutoRightEquiv (fun x ↦ (1 + x) ^ n - 1) (n * ·) 0 (n ≠ 0) where
  equiv := by
    intro h_dom
    apply NPowerRightEquiv_ℕ
    · exact h_dom
    · lim_cont

private instance rightequiv_NPowerEquiv_ℕ' {f : ℝ → ℝ} {n : ℕ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ (1 + f x) ^ n - 1) (fun x ↦ n * f x) x₀ (c ∧ L = 0 ∧ n ≠ 0) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply NPowerRightEquiv_ℕ
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance equiv_ExpEquiv
  : AutoEquiv (fun x ↦ exp x - 1) (·) 0 True where
  equiv := directly ExpEquiv (by lim_cont)

private instance equiv_ExpEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ exp (f x) - 1) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ExpEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_ExpEquiv
  : AutoLeftEquiv (fun x ↦ exp x - 1) (·) 0 True where
  equiv := directly ExpLeftEquiv (by lim_cont)

private instance leftequiv_ExpEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ exp (f x) - 1) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ExpLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_ExpEquiv
  : AutoRightEquiv (fun x ↦ exp x - 1) (·) 0 True where
  equiv := directly ExpRightEquiv (by lim_cont)

private instance rightequiv_ExpEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ exp (f x) - 1) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ExpRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_ExpowEquiv {a : ℝ}
  : AutoEquiv (fun x ↦ a ^ x - 1) (· * ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply ExpowEquiv
    · exact h_dom
    · lim_cont

private instance equiv_ExpowEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ a ^ f x - 1) (fun x ↦ f x * ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply ExpowEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance leftequiv_ExpowEquiv {a : ℝ}
  : AutoLeftEquiv (fun x ↦ a ^ x - 1) (· * ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply ExpowLeftEquiv
    · exact h_dom
    · lim_cont

private instance leftequiv_ExpowEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ a ^ f x - 1) (fun x ↦ f x * ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply ExpowLeftEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance rightequiv_ExpowEquiv {a : ℝ}
  : AutoRightEquiv (fun x ↦ a ^ x - 1) (· * ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply ExpowRightEquiv
    · exact h_dom
    · lim_cont

private instance rightequiv_ExpowEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ a ^ f x - 1) (fun x ↦ f x * ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply ExpowRightEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance equiv_LnEquiv
  : AutoEquiv (fun x ↦ ln (1 + x)) (·) 0 True where
  equiv := directly LnEquiv (by lim_cont)

private instance equiv_LnEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ ln (1 + f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply LnEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_LnEquiv
  : AutoLeftEquiv (fun x ↦ ln (1 + x)) (·) 0 True where
  equiv := directly LnLeftEquiv (by lim_cont)

private instance leftequiv_LnEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ ln (1 + f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply LnLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_LnEquiv
  : AutoRightEquiv (fun x ↦ ln (1 + x)) (·) 0 True where
  equiv := directly LnRightEquiv (by lim_cont)

private instance rightequiv_LnEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ ln (1 + f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply LnRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_LogEquiv {a : ℝ}
  : AutoEquiv (fun x ↦ log a (1 + x)) (· / ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply LogEquiv
    · exact h_dom
    · lim_cont

private instance equiv_LogEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ log a (1 + f x))
    (fun x ↦ f x / ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply LogEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance leftequiv_LogEquiv {a : ℝ}
  : AutoLeftEquiv (fun x ↦ log a (1 + x)) (· / ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply LogLeftEquiv
    · exact h_dom
    · lim_cont

private instance leftequiv_LogEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ log a (1 + f x))
    (fun x ↦ f x / ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply LogLeftEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance rightequiv_LogEquiv {a : ℝ}
  : AutoRightEquiv (fun x ↦ log a (1 + x)) (· / ln a) 0 (a > 0 ∧ a ≠ 1) where
  equiv := by
    intro h_dom
    apply LogRightEquiv
    · exact h_dom
    · lim_cont

private instance rightequiv_LogEquiv' {f : ℝ → ℝ} {a x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ log a (1 + f x))
    (fun x ↦ f x / ln a) x₀ (c ∧ L = 0 ∧ a > 0 ∧ a ≠ 1) where
  equiv := by
    intro ⟨h_cond, h_L, h_dom⟩
    apply LogRightEquiv
    · exact h_dom
    · rewrite [h_L] at h_ifs
      exact h_ifs.eq h_cond

private instance equiv_SinEquiv
  : AutoEquiv sin (·) 0 True where
  equiv := directly SinEquiv (by lim_cont)

private instance equiv_SinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ sin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SinEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_SinEquiv
  : AutoLeftEquiv sin (·) 0 True where
  equiv := directly SinLeftEquiv (by lim_cont)

private instance leftequiv_SinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ sin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SinLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_SinEquiv
  : AutoRightEquiv sin (·) 0 True where
  equiv := directly SinRightEquiv (by lim_cont)

private instance rightequiv_SinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ sin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply SinRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_TanEquiv
  : AutoEquiv tan (·) 0 True where
  equiv := directly TanEquiv (by lim_cont)

private instance equiv_TanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ tan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply TanEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_TanEquiv
  : AutoLeftEquiv tan (·) 0 True where
  equiv := directly TanLeftEquiv (by lim_cont)

private instance leftequiv_TanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ tan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply TanLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_TanEquiv
  : AutoRightEquiv tan (·) 0 True where
  equiv := directly TanRightEquiv (by lim_cont)

private instance rightequiv_TanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ tan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply TanRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_ArcsinEquiv
  : AutoEquiv arcsin (·) 0 True where
  equiv := directly ArcsinEquiv (by lim_cont)

private instance equiv_ArcsinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ arcsin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArcsinEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_ArcsinEquiv
  : AutoLeftEquiv arcsin (·) 0 True where
  equiv := directly ArcsinLeftEquiv (by lim_cont)

private instance leftequiv_ArcsinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ arcsin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArcsinLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_ArcsinEquiv
  : AutoRightEquiv arcsin (·) 0 True where
  equiv := directly ArcsinRightEquiv (by lim_cont)

private instance rightequiv_ArcsinEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ arcsin (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArcsinRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance equiv_ArctanEquiv
  : AutoEquiv arctan (·) 0 True where
  equiv := directly ArctanEquiv (by lim_cont)

private instance equiv_ArctanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLimit f x₀ L c]
  : AutoEquiv (fun x ↦ arctan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArctanEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance leftequiv_ArctanEquiv
  : AutoLeftEquiv arctan (·) 0 True where
  equiv := directly ArctanLeftEquiv (by lim_cont)

private instance leftequiv_ArctanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoLeftLimit f x₀ L c]
  : AutoLeftEquiv (fun x ↦ arctan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArctanLeftEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

private instance rightequiv_ArctanEquiv
  : AutoRightEquiv arctan (·) 0 True where
  equiv := directly ArctanRightEquiv (by lim_cont)

private instance rightequiv_ArctanEquiv' {f : ℝ → ℝ} {x₀ L : ℝ} {c : Prop}
    [h_ifs : AutoRightLimit f x₀ L c]
  : AutoRightEquiv (fun x ↦ arctan (f x)) f x₀ (c ∧ L = 0) where
  equiv := by
    intro ⟨h_cond, h_L⟩
    apply ArctanRightEquiv
    rewrite [h_L] at h_ifs
    exact h_ifs.eq h_cond

lemma autoEquiv {f f' g : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoEquiv f f' x₀ cond] (h_cond : cond)
  : lim (fun x ↦ f x / g x) x₀ = lim (fun x ↦ f' x / g x) x₀
:= sorry

lemma autoEquiv' {f g g' : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoEquiv g g' x₀ cond] (h_cond : cond)
  : lim (fun x ↦ f x / g x) x₀ = lim (fun x ↦ f x / g' x) x₀
:= sorry

lemma autoLeftEquiv {f f' g : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoLeftEquiv f f' x₀ cond] (h_cond : cond)
  : lim₋ (fun x ↦ f x / g x) x₀ = lim₋ (fun x ↦ f' x / g x) x₀
:= sorry

lemma autoLeftEquiv' {f g g' : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoLeftEquiv g g' x₀ cond] (h_cond : cond)
  : lim₋ (fun x ↦ f x / g x) x₀ = lim₋ (fun x ↦ f x / g' x) x₀
:= sorry

lemma autoRightEquiv {f f' g : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoRightEquiv f f' x₀ cond] (h_cond : cond)
  : lim₊ (fun x ↦ f x / g x) x₀ = lim₊ (fun x ↦ f' x / g x) x₀
:= sorry

lemma autoRightEquiv' {f g g' : ℝ → ℝ} {x₀ : ℝ} {cond : Prop}
    [AutoRightEquiv g g' x₀ cond] (h_cond : cond)
  : lim₊ (fun x ↦ f x / g x) x₀ = lim₊ (fun x ↦ f x / g' x) x₀
:= sorry


/-! # Tactics -/

/-- ## Equivalent Infinitesimal Substitution

    __Usage__ `lim_equiv`

    - Only used for limit expression, including
      - `FuncLimitExpr`
      - `LeftLimitExpr`
      - `RightLimitExpr`

    - `lim_equiv` uses these built-in equivalent infinitesimals to simplify the
      original expression:

      - `√(1 + f x) - 1 ~ f x / 2`
      - `(1 + f x) ^ a - 1 ~ a * f x` when `a ≠ 0`
      - `(1 + f x) ^ n - 1 ~ n * f x` when `n ≠ 0`
      - `exp (f x) - 1 ~ f x`
      - `a ^ f x - 1 ~ f x * ln a` when `a > 0 ∧ a ≠ 1`
      - `ln (1 + f x) ~ f x`
      - `log a (1 + f x) ~ f x / ln a` when `a > 0 ∧ a ≠ 1`
      - `sin (f x) ~ f x`
      - `tan (f x) ~ f x`
      - `arcsin (f x) ~ f x`
      - `arctan (f x) ~ f x`

      , and then uses built-in tactic `auto_eq` to solve the remaining goal.

      The `f` above refers to an infinitesimal (or just `(·)`). This is determined
      automatically by `lim_cont`.

    - Factors in the substituted expression should preferably be provided in the
      original sequence and form, in case `lim_equiv` fails to recognize it.

    - `lim_equiv` can only handle lambda functions. So do not use point-free
      operations like `f + g`, which can be replaced with `(fun x ↦ f x + g x)`.

    __Examples__
    ```lean
    example
      : lim (fun x ↦ sin x / x) 0 =? lim (fun x ↦ x / x) 0
    := by lim_equiv
    example
      : lim (fun x ↦ (ln (1 + (x - π)) * arcsin (x - π)) / (sin (x - π) * cos x)) π
        =? lim (fun x ↦ ((x - π) * (x - π)) / ((x - π) * cos x)) π
    := by lim_equiv
    example
      : lim (fun x ↦  (arctan (exp x - 1) * sin (tan x))
                      / (sin x * arcsin (x ^ 2) * (exp (arcsin x) - 1))) 0
        =? lim (fun x ↦ 1 / x ^ 2) 0
    := by lim_equiv
    ```
-/
macro "lim_equiv" : tactic => `(tactic| (
  intros
  simp (
    discharger := auto_side_condition
  ) only [
    autoEquiv,
    autoEquiv',
    autoLeftEquiv,
    autoLeftEquiv',
    autoRightEquiv,
    autoRightEquiv',
  ]
  try focus auto_eq
  try focus lim_congr_by auto_eq within 1
))

example
  : lim (fun x ↦ sin x / x) 0 =? lim (fun x ↦ x / x) 0
:= by lim_equiv
example
  : lim (fun x ↦ (ln (1 + (x - π)) * arcsin (x - π)) / (sin (x - π) * cos x)) π
    =? lim (fun x ↦ ((x - π) * (x - π)) / ((x - π) * cos x)) π
:= by lim_equiv
example
  : lim (fun x ↦  (arctan (exp x - 1) * sin (tan x))
                  / (sin x * arcsin (x ^ 2) * (exp (arcsin x) - 1))) 0
    =? lim (fun x ↦ 1 / x ^ 2) 0
:= by lim_equiv

page_end
