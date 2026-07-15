import «Calculus@JokerXin».Prelude
import Mathlib.Tactic.GCongr.Core

variable {α : Type}

/-
  It's assumed that expression's type has instances of the following classes:
  - `Zero`
  - `Add`
  - `Sub`
  - `Mul`
  - `Div`
  - `DecidableEq`
-/

-- @[Lean2TeX "@2\\textcolor{lightgrey}{=}@3" Rel]
def UdEqual (A B : Option α) : Prop :=
  match B with
  | none => True
  | some B! =>
    A = the B!

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
    rw [h2] at h1
    exact h1

instance : Trans (@UdEqual α) (@UdEqual α) (@UdEqual α) where
  trans := UdEqual_trans

instance : Trans (@UdEqual α) (@Eq (Option α)) (@UdEqual α) where
  trans {A B C} h1 h2 := by
    rw [← h2]
    exact h1

instance : Trans (@Eq (Option α)) (@UdEqual α) (@UdEqual α) where
  trans {A B C} h1 h2 := by
    rw [h1]
    exact h2

def Expr_Free₁ (f : α → α) (a : Option α) : Option α := Option.map f a
def Expr_Free₂ (f : α → α → α) (a b : Option α) : Option α :=
  match a, b with
  | some x, some y => some (f x y)
  | _, _ => none

open Classical in
noncomputable def Expr_Div [Zero α] [Div α] (A B : Option α) : Option α :=
  if B = the 0 then none
  else Expr_Free₂ (· / ·) A B

open Classical in
noncomputable def Expr_Pow [Pow α α] [Pow α ℤ] [Zero α] [One α] [LT α]
    [IntCast α] (A B : Option α) : Option α :=
  match A, B with
  | some x, some y =>
    if x = 0 ∧ y > 0 then the 0
    else if x > 0 then the (x ^ y)
    else if h : x < 0 ∧ (∃ n : ℤ, y = ↑n) then
      the (x ^ (choose h.2))
    else none
  | _, _ => none

def Expr_Neg [Neg α] (A : Option α) : Option α := Expr_Free₁ (-·) A

open Classical in
noncomputable def Expr_Inv [Zero α] [Inv α] (A : Option α) : Option α :=
  if A = the 0 then none
  else Expr_Free₁ (·⁻¹) A

instance [Add α]
  : Add (Option α) where add := Expr_Free₂ (· + ·)
instance [Sub α]
  : Sub (Option α) where sub := Expr_Free₂ (· - ·)
instance [Mul α]
  : Mul (Option α) where mul := Expr_Free₂ (· * ·)
noncomputable instance [Zero α] [Div α]
  : Div (Option α) where div := Expr_Div
noncomputable instance [Pow α α] [Pow α ℤ] [Zero α] [One α] [LT α] [IntCast α]
  : Pow (Option α) (Option α) where pow := Expr_Pow
instance [Neg α]
  : Neg (Option α) where neg := Expr_Neg
noncomputable instance [Zero α] [Inv α]
  : Inv (Option α) where inv := Expr_Inv

@[gcongr]
theorem UdEqual_GcongrAdd {A B C : Option α}
    [Add α] (h : A =? B)
  : A + C =? B + C
:= by
  unfold UdEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrAdd' {A B C : Option α}
    [Add α] (h : B =? C)
  : A + B =? A + C
:= by
  unfold UdEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrSub {A B C : Option α}
    [Sub α] (h : A =? B)
  : A - C =? B - C
:= by
  unfold UdEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrSub' {A B C : Option α}
    [Sub α] (h : B =? C)
  : A - B =? A - C
:= by
  unfold UdEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrMul {A B C : Option α}
    [Mul α] (h : A =? B)
  : A * C =? B * C
:= by
  unfold UdEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrMul' {A B C : Option α}
    [Mul α] (h : B =? C)
  : A * B =? A * C
:= by
  unfold UdEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UdEqual_GcongrDiv {A B C : Option α}
    [Zero α] [Div α] (h : A =? B)
  : A / C =? B / C
:= sorry /-by
  cases B with
  | none =>
    have eq_none : none / C = none := by
      simp only [HDiv.hDiv, Div.div]
      split <;> rfl
    rw [eq_none]
    trivial
  | some b => rw [h]-/

@[gcongr]
theorem UdEqual_GcongrDiv' {A B C : Option α}
    [Zero α] [Div α] (h : B =? C)
  : A / B =? A / C
:= by
  cases C with
  | none =>
    have eq_none : A / none = none := by
      cases A <;> rfl
    rw [eq_none]
    trivial
  | some c => rw [h]

lemma UdEqual.determine {A B : Option α} {B! : α}
    (h_udeq : A =? B) (h_B : B = the B!)
  : A = the B!
:= by
  rw [h_B] at h_udeq
  exact h_udeq

lemma UdEqual.calc_div {a b : ℝ}
    (h_b_ne0 : b ≠ 0)
  : the a / the b = the (a / b)
:= by
  change (if the b = the 0 then none
          else Expr_Free₂ (· / ·) (the a) (the b)) = the (a / b)
  have h_cond : the b ≠ the 0 := by simp [h_b_ne0]
  rw [if_neg h_cond]
  rfl

lemma UdEqual.calc_inv {a : ℝ}
    (h_a_ne0 : a ≠ 0)
  : (the a)⁻¹ = the a⁻¹
:= by
  change (if the a = the 0 then none
          else Expr_Free₁ (·⁻¹) (the a)) = the a⁻¹
  have h_cond : the a ≠ the 0 := by simp [h_a_ne0]
  rw [if_neg h_cond]
  rfl

instance : Coe (ℝ → ℝ) (ℝ → Option ℝ) where
  coe := fun f x ↦ some (f x)
instance : Coe (ℕ → ℝ) (ℕ → Option ℝ) where
  coe := fun f n ↦ some (f n)

/-
instance {n : Nat} [OfNat α n] : OfNat (Option α) n where
  ofNat := the (OfNat.ofNat n)
instance [OfScientific α] : OfScientific (Option α) where
  ofScientific := fun m s e ↦ the (OfScientific.ofScientific m s e)

@[simp]
lemma rewriteExpr_coe {a : α}
  : (a : Option α) = the a
:= rfl

@[simp]
lemma rewriteExpr_ofNat {n : ℕ} [OfNat α n]
  : (OfNat.ofNat n : Option α) = the (OfNat.ofNat n)
:= rfl
-/
