/-
    «Calculus_21».Expr.EqualIfProper
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Expr.PolyEqual
set_option linter.style.header false


/-! # Equality If Proper `=?` -/

class ProperClass (ExprValue : Type)
    (Equal : outParam (ExprValue → ExprValue → Prop)) where
  isProper : ExprValue → Prop
  equal_refl : ∀ A, Equal A A
  eq_of_proper : ∀ {A B : ExprValue},
    Equal A B → isProper B → A = B

section
variable {ExprValue : Type} {A B C : ExprValue}
variable {Equal : ExprValue → ExprValue → Prop}
variable [ProperClass ExprValue Equal]

def EqualIfProper (A B : ExprValue) : Prop :=
  ProperClass.isProper B → Equal A B

infix:50 " =? " => EqualIfProper

theorem ProperClass.equal_of_eq
  : A = B → Equal A B
:= by
  intro _
  subst B
  exact ProperClass.equal_refl A

theorem EqualIfProper_iff :
    A =? B ↔ (ProperClass.isProper B ∧ Equal A B) ∨
      ¬ ProperClass.isProper B := by
  by_cases hB : ProperClass.isProper B
  · constructor
    · intro h
      exact Or.inl ⟨hB, h hB⟩
    · rintro (⟨_, h⟩ | h)
      · intro
        exact h
      · exact (h hB).elim
  · constructor
    · intro
      exact Or.inr hB
    · intro _ h
      exact (hB h).elim

theorem EqualIfProper.getEqual
  : A =? B → ProperClass.isProper B → Equal A B
:= id

theorem EqualIfProper.getEqual!
  : A =? B → ProperClass.isProper B → A = B
:= fun h₁ h₂ ↦ ProperClass.eq_of_proper (h₁ h₂) h₂

theorem EqualIfProper_of_not_proper
    (hB : ¬ ProperClass.isProper B) : A =? B := by
  intro h
  exfalso
  exact hB h

@[refl]
theorem EqualIfProper_refl
  : A =? A
:= by
  intro _
  exact ProperClass.equal_refl A

@[trans]
theorem EqualIfProper_trans
    (h₁ : A =? B) (h₂ : B =? C)
  : A =? C
:= by
  intro h_C
  have hBC : B = C := ProperClass.eq_of_proper (h₂ h_C) h_C
  subst C
  exact h₁ h_C

/-! The following instances are used to connect `=`, `=?` and `=.` together in `calc` -/

instance : Trans EqualIfProper Eq (@EqualIfProper ExprValue Equal _) where
  trans {A B C} h₁ h₂ := by grind

instance : Trans Eq EqualIfProper (@EqualIfProper ExprValue Equal _) where
  trans {A B C} h₁ h₂ := by grind

instance : Trans EqualIfProper EqualIfProper (@EqualIfProper ExprValue Equal _) where
  trans := EqualIfProper_trans

instance : Trans Equal EqualIfProper (@EqualIfProper ExprValue Equal _) where
  trans {A B C} hAB hBC := by
    intro hC
    have hBC' : B = C := ProperClass.eq_of_proper (hBC hC) hC
    subst C
    exact hAB

instance : Trans EqualIfProper Equal (@EqualIfProper ExprValue Equal _) where
  trans {A B C} hAB hBC := by
    intro hC
    have hBC' : B = C := ProperClass.eq_of_proper hBC hC
    subst C
    exact hAB hC

end
