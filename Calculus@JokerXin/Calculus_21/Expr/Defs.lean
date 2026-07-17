/-
    Calculus_21.Expr.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false

variable {α : Type}


/-! # Definition of UdEqual `=?` -/

/-- Undetermined equality relation -/
-- @[Lean2TeX "@2\\textcolor{lightgrey}{=}@3" Rel]
def UdEqual (A B : Option α) : Prop :=
  match B with
  | none => True
  | some B! => A = the B!

infix:50 " =? " => UdEqual

@[refl]
theorem UdEqual_refl (A : Option α) : A =? A := by
  unfold UdEqual
  cases A with
  | none => trivial
  | some a => rfl

@[trans]
theorem UdEqual_trans {A B C : Option α}
    (h1 : A =? B) (h2 : B =? C) : A =? C := by
  unfold UdEqual at *
  cases C with
  | none => trivial
  | some c =>
    rewrite [h2] at h1
    exact h1

/-! The following instances are used to connect `=?` and `=` together in `calc` -/

instance : Trans (@UdEqual α) (@UdEqual α) (@UdEqual α) where
  trans := UdEqual_trans

instance : Trans (@UdEqual α) (@Eq (Option α)) (@UdEqual α) where
  trans {A B C} h1 h2 := by
    rewrite [← h2]
    exact h1

instance : Trans (@Eq (Option α)) (@UdEqual α) (@UdEqual α) where
  trans {A B C} h1 h2 := by
    rewrite [h1]
    exact h2


/-! # Expression Operations -/

instance [Add α] : Add (Option α) where
  add A B :=  match A, B with
              | the a, the b => the (a + b)
              | _, _ => none

instance [Sub α] : Sub (Option α) where
  sub A B :=  match A, B with
              | the a, the b => the (a - b)
              | _, _ => none

instance [Mul α] : Mul (Option α) where
  mul A B :=  match A, B with
              | the a, the b => the (a * b)
              | _, _ => none

open Classical in
noncomputable instance [Zero α] [Div α] : Div (Option α) where
  div A B :=  if B = the 0 then none
              else  match A, B with
                    | the a, the b => the (a / b)
                    | _, _ => none

open Classical in
noncomputable instance [Pow α α] [Pow α ℤ] [Zero α] [One α] [LT α] [IntCast α] :
    Pow (Option α) (Option α) where
  pow A B :=  match A, B with
              | the a, the b =>
                if a = 0 ∧ b > 0 then the 0
                else if a > 0 then the (a ^ b)
                else if h : a < 0 ∧ (∃ n : ℤ, b = ↑n) then
                the (a ^ (choose h.2))
                else none
              | _, _ => none

instance [Neg α] : Neg (Option α) where
  neg A := Option.map (-·) A

open Classical in
noncomputable instance [Zero α] [Inv α] : Inv (Option α) where
  inv A :=  if A = the 0 then none
            else Option.map (·⁻¹) A


/-! # Lemmas on UdEqual -/

lemma UdEqual.determine {A B : Option α} {B! : α}
    (h_udeq : A =? B) (h_B : B = the B!)
  : A = the B!
:= by
  rewrite [h_B] at h_udeq
  exact h_udeq

lemma UdEqual.calc_div {a b : ℝ}
    (h_b_ne0 : b ≠ 0)
  : the a / the b = the (a / b)
:= by
  change (if the b = the 0 then none else the (a / b)) = the (a / b)
  rw [if_neg (by simp [h_b_ne0])]

lemma UdEqual.calc_inv {a : ℝ}
    (h_a_ne0 : a ≠ 0)
  : (the a)⁻¹ = the a⁻¹
:= by
  change (if the a = the 0 then none else the a⁻¹) = the a⁻¹
  rw [if_neg (by simp [h_a_ne0])]

open Classical in
lemma UdEqual.calc_pow {a b : ℝ}
    (h_a_pos : a > 0)
  : the a ^ the b = the (a ^ b)
:= by
  have h_eq : the a ^ the b =
    if a = 0 ∧ b > 0 then the 0
    else if a > 0 then the (a ^ b)
    else if h : a < 0 ∧ (∃ n : ℤ, b = ↑n) then the (a ^ (choose h.2))
    else none := rfl
  rw [h_eq]
  have h_not : ¬(a = 0 ∧ b > 0) := fun h => by linarith
  rw [if_neg h_not, if_pos h_a_pos]
