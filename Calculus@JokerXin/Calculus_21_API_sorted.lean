-- === 外部依赖 (External Imports) ===
import Aesop.Frontend.Command
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Nat.Factorial.Basic

-- ========================================== --
-- File: Calculus_21/Prelude.lean
-- ========================================== --

/-
    Calculus_21.Prelude
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

-- import Lean2TeX.Register


/-! # Notations -/

export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici
            mem_univ subset_univ mem_setOf_eq)
export Finset (range)
export Real (sqrt exp sin cos tan cot sinh cosh tanh arcsin arccos arctan)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n  -- this is only scoped in Mathlib
macro "the" : term => `(some)
macro "directly" id:ident : term => `(fun _ ↦ $id)


/-! # Supplementary Definitions -/

noncomputable def e : ℝ := Real.exp 1
noncomputable def π : ℝ := Real.pi

def const (C : ℝ) : ℝ → ℝ := Function.const ℝ C
noncomputable abbrev npow (n : ℤ) : ℝ → ℝ := DivInvMonoid.zpow n
noncomputable def pow (a : ℝ) : ℝ → ℝ := (Real.rpow · a)
noncomputable def ln : ℝ → ℝ := Real.log
noncomputable def log : ℝ → ℝ → ℝ := (fun a x ↦ Real.log x / Real.log a)
noncomputable def sec : ℝ → ℝ := (1 / cos ·)
noncomputable def csc : ℝ → ℝ := (1 / sin ·)
noncomputable def coth : ℝ → ℝ := (1 / tanh ·)
noncomputable def sech : ℝ → ℝ := (1 / cosh ·)
noncomputable def csch : ℝ → ℝ := (1 / sinh ·)
noncomputable def arccot : ℝ → ℝ := (π / 2 - arctan ·)
noncomputable def arcsec : ℝ → ℝ := (fun x ↦ arccos (1 / x))
noncomputable def arccsc : ℝ → ℝ := (fun x ↦ arcsin (1 / x))


/-! # Declarations for Aesop -/

declare_aesop_rule_sets [
  ExprInitialize,
  ExprConvert,
  ExprSimplify,
  AutoEquation,
  LimitSimplify,
  LimitEquivalent
]


-- ========================================== --
-- File: Calculus_21/Expr/Defs.lean
-- ========================================== --

/-
    Calculus_21.Expr.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/


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
theorem UdEqual_refl (A : Option α) : A =? A := sorry
@[trans]
theorem UdEqual_trans {A B C : Option α}
    (h1 : A =? B) (h2 : B =? C) : A =? C := sorry
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
:= sorry
lemma UdEqual.calc_div {a b : ℝ}
    (h_b_ne0 : b ≠ 0)
  : the a / the b = the (a / b)
:= sorry
lemma UdEqual.calc_inv {a : ℝ}
    (h_a_ne0 : a ≠ 0)
  : (the a)⁻¹ = the a⁻¹
:= sorry
open Classical in
lemma UdEqual.calc_pow {a b : ℝ}
    (h_a_pos : a > 0)
  : the a ^ the b = the (a ^ b)
:= sorry


-- ========================================== --
-- File: Calculus_21/Sequence/Defs.lean
-- ========================================== --

/-
    Calculus_21.Sequence.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Definition of Sequence -/

/-- Real Number Sequence with Domain
    - `a.map`, `a.init` and `a.final` refer to `a`'s total map, initial item's
    index and the final item's index + 1, respectively
    - for infinite sequence `a`, the value of `a.final` is `none` -/
structure Sequence where
  map : ℕ → ℝ
  init : ℕ
  final : WithTop ℕ


/-! # Sequence Operations -/

/-- Sequence's Addition -/
instance : Add Sequence where
  add A B := ⟨A.map + B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Subtraction -/
instance : Sub Sequence where
  sub A B := ⟨A.map - B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Multiplication -/
instance : Mul Sequence where
  mul A B := ⟨A.map * B.map, max A.init B.init, min A.final B.final⟩

/-- Sequence's Division -/
noncomputable instance : Div Sequence where
  div A B := ⟨A.map / B.map, max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | B.map n = 0 }))⟩

/-- Sequence's Power -/
noncomputable instance : HomogeneousPow Sequence where
  pow A B := ⟨(fun x ↦ A.map x ^ B.map x), max A.init B.init,
              min (min A.final B.final) (some (sInf { n : ℕ | A.map n ≤ 0 }))⟩

/-- Sequence's Scalar Multiplication -/
instance : SMul ℝ Sequence where
  smul k A := ⟨k • A.map, A.init, A.final⟩

/-- Sequence's Additive Inverse -/
instance : Neg Sequence where
  neg A := ⟨- A.map, A.init, A.final⟩

/-- Sequence's Multiplication Scalar Power
    - this may allow `0 ^ 0 = 1` -/
instance : NatPow Sequence where
  pow A n := ⟨A.map ^ n, A.init, A.final⟩

/-- Sequence's Multiplicative Inverse -/
noncomputable instance : Inv Sequence where
  inv A := ⟨A.map⁻¹, A.init, min A.final (some (sInf { n : ℕ | A.map n = 0 }))⟩


-- ========================================== --
-- File: Calculus_21/Sequence/Concepts.lean
-- ========================================== --

/-
    Calculus_21.Sequence.Concepts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Boundedness of Sequence -/

/-- Bounded Sequence -/
def SeqBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, |A.map n| < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, |A.map n| < M

/-- Upper-Bounded Sequence -/
def SeqUpperBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n < M

/-- Lower-Bounded Sequence -/
def SeqLowerBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n > -M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n > -M


-- ========================================== --
-- File: Calculus_21/Function/Defs.lean
-- ========================================== --

/-
    Calculus_21.Function.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Definition of Function -/

/-- Real Function with Domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
structure Function where
  map : ℝ → ℝ
  domain : Set ℝ


/-! # Function Operations -/

/-- Function's Addition -/
instance : Add Function where
  add F G := ⟨F.map + G.map, F.domain ∩ G.domain⟩

/-- Function's Subtraction -/
instance : Sub Function where
  sub F G := ⟨F.map - G.map, F.domain ∩ G.domain⟩

/-- Function's Multiplication -/
instance : Mul Function where
  mul F G := ⟨F.map * G.map, F.domain ∩ G.domain⟩

/-- Function's Division -/
noncomputable instance : Div Function where
  div F G := ⟨F.map / G.map, F.domain ∩ G.domain ∩ { x : ℝ | G.map x ≠ 0}⟩

/-- Function's Power -/
noncomputable instance : HomogeneousPow Function where
  pow F G := ⟨(fun x ↦ F.map x ^ G.map x), F.domain ∩ G.domain ∩ { x : ℝ | F.map x > 0 }⟩

/-- Function's Scalar Multiplication -/
instance : SMul ℝ Function where
  smul k F := ⟨k • F.map, F.domain⟩

/-- Function's Additive Inverse -/
instance : Neg Function where
  neg F := ⟨- F.map, F.domain⟩

/-- Function's Multiplication Scalar Power
    - this may allow `0 ^ 0 = 1` -/
instance : NatPow Function where
  pow F n := ⟨F.map ^ n, F.domain⟩

/-- Function's Multiplicative Inverse -/
noncomputable instance : Inv Function where
  inv F := ⟨F.map⁻¹, F.domain ∩ { x : ℝ | F.map x ≠ 0}⟩

/-- Function's Composition -/
def Function_Comp (F G : Function) : Function :=
  ⟨F.map ∘ G.map, G.domain ∩ { x : ℝ | G.map x ∈ F.domain }⟩

infixr:90 " ⊙ " => (Function_Comp · ·)


/-! # Fundamental Functions -/

/-- Constant Function -/
def Constant (C : ℝ) : Function := ⟨const C, Iii⟩

/-- Identity Function -/
def Identity : Function := ⟨id, Iii⟩

/-- Absolute Value Function -/
def Abs : Function := ⟨abs, Iii⟩

/-- Square Root Function -/
noncomputable def Sqrt : Function := ⟨sqrt, Ici 0⟩

open Classical in
/-- Power Function -/
noncomputable def Power (a : ℝ) : Function :=
  if h : ∃ n : ℤ, a = ↑n then
    if a > 0 then ⟨npow (choose h), Iii⟩
    else ⟨const 1, { x : ℝ | x ≠ 0 }⟩
  else if a > 0 then ⟨pow a, Ici 0⟩
  else ⟨pow a, Ioi 0⟩

/-- Natural Exponential Function -/
noncomputable def Exp : Function := ⟨exp, Iii⟩

/-- Exponential Function
    - **`a > 0` must hold true!**
    - When `a = 1`, it degenerates into a constant function -/
noncomputable def Expow (a : ℝ) : Function := ⟨(a ^ ·), Iii⟩

/-- Natural Logarithm Function -/
noncomputable def Ln : Function := ⟨ln, Ioi 0⟩

/-- Logarithm Function
    - **`a > 0 ∧ a ≠ 1` must hold true!** -/
noncomputable def Log (a : ℝ) : Function := ⟨log a, Ioi 0⟩

/-- Sine Function -/
noncomputable def Sin : Function := ⟨sin, Iii⟩

/-- Cosine Function -/
noncomputable def Cos : Function := ⟨cos, Iii⟩

/-- Tangent Function -/
noncomputable def Tan : Function := ⟨tan, { x : ℝ | cos x ≠ 0 }⟩

/-- Cotangent Function -/
noncomputable def Cot : Function := ⟨cot, { x : ℝ | sin x ≠ 0 }⟩

/-- Secant Function -/
noncomputable def Sec : Function := ⟨sec, { x : ℝ | cos x ≠ 0 }⟩

/-- Cosecant Function -/
noncomputable def Csc : Function := ⟨csc, { x : ℝ | sin x ≠ 0 }⟩

/-- Hyp-Sine Function -/
noncomputable def Sinh : Function := ⟨sinh, Iii⟩

/-- Hyp-Cosine Function -/
noncomputable def Cosh : Function := ⟨cosh, Iii⟩

/-- Hyp-Tangent Function -/
noncomputable def Tanh : Function := ⟨tanh, Iii⟩

/-- Hyp-Cotangent Function -/
noncomputable def Coth : Function := ⟨coth, { x : ℝ | x ≠ 0 }⟩

/-- Hyp-Secant Function -/
noncomputable def Sech : Function := ⟨sech, Iii⟩

/-- Hyp-Cosecant Function -/
noncomputable def Csch : Function := ⟨csch, { x : ℝ | x ≠ 0 }⟩

/-- Arc-Sine Function -/
noncomputable def Arcsin : Function := ⟨arcsin, Icc (-1) 1⟩

/-- Arc-Cosine Function -/
noncomputable def Arccos : Function := ⟨arccos, Icc (-1) 1⟩

/-- Arc-Tangent Function -/
noncomputable def Arctan : Function := ⟨arctan, Iii⟩

/-- Arc-Cotangent Function -/
noncomputable def Arccot : Function := ⟨arccot, Iii⟩

/-- Arc-Secant Function -/
noncomputable def Arcsec : Function := ⟨arcsec, Iic (-1) ∪ Ici 1⟩

/-- Arc-Cosecant Function -/
noncomputable def Arccsc : Function := ⟨arccsc, Iic (-1) ∪ Ici 1⟩


-- ========================================== --
-- File: Calculus_21/Function/Concepts.lean
-- ========================================== --

/-
    Calculus_21.Function.Concepts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Neighborhood -/

/-- Neighborhood -/
abbrev Nbho (x₀ δ : ℝ) : Set ℝ := { x : ℝ | x₀ - δ < x ∧ x < x₀ + δ }

/-- Deleted Neighborhood -/
abbrev Nbhd (x₀ δ : ℝ) : Set ℝ := { x : ℝ | (x₀ - δ) < x ∧ x < (x₀ + δ) ∧ x ≠ x₀ }

/-- Deleted Neighborhood ⊆ Neighborhood -/
lemma Nbhd_subset_Nbho {x₀ δ : ℝ}
  : Nbhd x₀ δ ⊆ Nbho x₀ δ
:= sorry
/-! # Minimum Point & Maximum Point -/

/-- Minimum Point -/
def isMinimumPoint (F : Function) (m : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x > F.map m

/-- Maximum Point -/
def isMaximumPoint (F : Function) (M : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x < F.map M


/-! # Boundedness of Function -/

/-- Bounded Function -/
def FuncBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, |F.map x| < M

/-- Upper-Bounded Function -/
def FuncUpperBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x < M

/-- Lower-Bounded Function -/
def FuncLowerBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x > -M

/-- Locally Bounded Function -/
def FuncLocalBounded (F : Function) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ M > 0, ∀ x ∈ F.domain ∩ Nbho x₀ δ, |F.map x| < M

/-- Locally Bounded Function (at Negative Infinity) -/
def FuncLocalBounded_NegInfty (F : Function) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Iic (-M₁), |F.map x| < M₂

/-- Locally Bounded Function (at Positive Infinity) -/
def FuncLocalBounded_PosInfty (F : Function) : Prop :=
  ∃ M₁ > 0, ∃ M₂ > 0, ∀ x ∈ F.domain ∩ Ici M₁, |F.map x| < M₂


-- ========================================== --
-- File: Calculus_21/Limit/Defs.lean
-- ========================================== --

/-
    Calculus_21.Limit.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Definitions of Limit -/

/-- Sequence Limit -/
-- @[Lean2TeX "数列@1收敛于@2" Text]
def SeqLimit (A : Sequence) (L : ℝ) : Prop :=
  A.final = none
  ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, A.map n ∈ Nbho L ε

abbrev SeqConvergesAt (A : Sequence) : Prop :=
  ∃ L : ℝ, SeqLimit A L

/-- Function Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处收敛于@3" Text]
def FuncLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, F.map x ∈ Nbho L ε)

abbrev FuncConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, FuncLimit F x₀ L

/-- Left Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的左极限为@3" Text]
def LeftLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x ∈ Nbho L ε)

abbrev LeftConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftLimit F x₀ L

/-- Right Limit -/
-- @[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的右极限为@3" Text]
def RightLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x ∈ Nbho L ε)

abbrev RightConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightLimit F x₀ L

/-- Limit at Negative Infinity -/
def NegInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)

abbrev ConvergesAtNegInfty (F : Function) : Prop :=
  ∃ L : ℝ, NegInftyLimit F L

/-- Limit at Positive Infinity -/
def PosInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

abbrev ConvergesAtPosInfty (F : Function) : Prop :=
  ∃ L : ℝ, PosInftyLimit F L

/-- Limit at Infinity -/
def InftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain ∧ Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      (∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)
      ∧ (∀ x ∈ Ioi M, F.map x ∈ Nbho L ε))

abbrev ConvergesAtInfty (F : Function) : Prop :=
  ∃ L : ℝ, InftyLimit F L


/-! # Properties of Limit -/

/-- Uniqueness of Sequence Limit -/
theorem SeqLimit_Unique {A : Sequence} {L₁ L₂ : ℝ}
    (h₁ : SeqLimit A L₁) (h₂ : SeqLimit A L₂)
  : L₁ = L₂
:= sorry
/-- Boundedness of Convergent Sequence -/
theorem SeqLimit_Bounded {A : Sequence}
    (h_conv : SeqConvergesAt A)
  : SeqBounded A
:= sorry
/-- Uniqueness of Function Limit -/
theorem FuncLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : FuncLimit F x₀ L₁) (h₂ : FuncLimit F x₀ L₂)
  : L₁ = L₂
:= sorry
/-- Local Boundedness of Convergent Function -/
theorem FuncLimit_Bounded {F : Function} {x₀ : ℝ}
    (h_conv : FuncConvergesAt F x₀)
  : FuncLocalBounded F x₀
:= sorry
/-- Uniqueness of Left Limit -/
theorem LeftLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : LeftLimit F x₀ L₁) (h₂ : LeftLimit F x₀ L₂)
  : L₁ = L₂
:= sorry
/-- Uniqueness of Right Limit -/
theorem RightLimit_Unique {F : Function} {x₀ L₁ L₂ : ℝ}
    (h₁ : RightLimit F x₀ L₁) (h₂ : RightLimit F x₀ L₂)
  : L₁ = L₂
:= sorry
/-- Uniqueness of Limit at Negative Infinity -/
theorem NegInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : NegInftyLimit F L₁) (h₂ : NegInftyLimit F L₂)
  : L₁ = L₂
:= sorry
/-- Local Boundedness of Function Convergent at Negative Infinity -/
theorem NegInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtNegInfty F)
  : FuncLocalBounded_NegInfty F
:= sorry
/-- Uniqueness of Limit at Positive Infinity -/
theorem PosInftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : PosInftyLimit F L₁) (h₂ : PosInftyLimit F L₂)
  : L₁ = L₂
:= sorry
/-- Local Boundedness of Function Convergent at Positive Infinity -/
theorem PosInftyLimit_Bounded {F : Function}
    (h_conv : ConvergesAtPosInfty F)
  : FuncLocalBounded_PosInfty F
:= sorry
/-- Uniqueness of Limit at Infinity -/
theorem InftyLimit_Unique {F : Function} {L₁ L₂ : ℝ}
    (h₁ : InftyLimit F L₁) (h₂ : InftyLimit F L₂)
  : L₁ = L₂
:= sorry
/-- Congruence of Sequence Limit -/
lemma SeqLimit.Congr {A B : Sequence} {L : ℝ}
    (h_lim : SeqLimit A L)
    (h_B_inf : B.final = none)
    (h_congr : ∃ N : ℕ, ∀ n > N, A.map n = B.map n)
  : SeqLimit B L
:= sorry
/-- Congruence of Function Limit -/
lemma FuncLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
    (h_congr : ∃ δ > 0, Nbhd x₀ δ ⊆ G.domain ∧ ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= sorry
/-- Congruence of Left Limit -/
lemma LeftLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : LeftLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ G.domain
                        ∧ ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= sorry
/-- Congruence of Right Limit -/
lemma RightLimit.Congr {F G : Function} {x₀ L : ℝ}
    (h_lim : RightLimit F x₀ L)
    (h_congr : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ G.domain
                        ∧ ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= sorry
/-- Congruence of Limit at Negative Infinity -/
lemma NegInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : NegInftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain
                        ∧ ∀ x ∈ Iio (-M), F.map x = G.map x)
  : NegInftyLimit G L
:= sorry
/-- Congruence of Limit at Positive Infinity -/
lemma PosInftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : PosInftyLimit F L)
    (h_congr : ∃ M > 0, Ioi M ⊆ G.domain
                        ∧ ∀ x ∈ Ioi M, F.map x = G.map x)
  : PosInftyLimit G L
:= sorry
/-- Congruence of Limit at Infinity -/
lemma InftyLimit.Congr {F G : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
    (h_congr : ∃ M > 0, Iio (-M) ⊆ G.domain ∧ Ioi M ⊆ G.domain
                        ∧ (∀ x ∈ Iio (-M), F.map x = G.map x)
                        ∧ (∀ x ∈ Ioi M, F.map x = G.map x))
  : InftyLimit G L
:= sorry
/-- Function Limit → Left Limit -/
theorem FuncLimit_toLeft {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= sorry
/-- Function Limit → Right Limit -/
theorem FuncLimit_toRight {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= sorry
/-- Limit at Infinity → Limit at Negative Infinity -/
theorem InftyLimit_toNeg {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : NegInftyLimit F L
:= sorry
/-- Limit at Infinity → Limit at Positive Infinity -/
theorem InftyLimit_toPos {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : PosInftyLimit F L
:= sorry


-- ========================================== --
-- File: Calculus_21/Limit/Expr.lean
-- ========================================== --

/-
    Calculus_21.Limit.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Limit Expression -/

noncomputable section

open Classical in
/-- Sequence Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℕ)\\to\\infty}@1" Expr]
def SeqLimitExpr (a : ℕ → ℝ) : Option ℝ :=
  if h : SeqConvergesAt ⟨a, 0, none⟩ then the (choose h)
  else none

open Classical in
/-- Function Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2}@1" Expr]
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : FuncConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Left Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^-}@1" Expr]
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : LeftConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Right Limit Expression -/
-- @[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^+}@1" Expr]
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : RightConvergesAt ⟨f, Iii⟩ x₀ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtNegInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtPosInfty ⟨f, Iii⟩ then the (choose h)
  else none

open Classical in
/-- Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → ℝ) : Option ℝ :=
  if h : ConvergesAtInfty ⟨f, Iii⟩ then the (choose h)
  else none

end

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)
macro "lim₋∞" : term => `(NegInftyLimitExpr)
macro "lim₊∞" : term => `(PosInftyLimitExpr)
macro "lim∞" : term => `(InftyLimitExpr)


/-! # Bridges between Limit & Limit Expression -/

open Classical in
/-- Sequence Limit → Sequence Limit Expression -/
theorem SeqLimit_to_SeqLimitExpr {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : SeqLimit ⟨a, init, none⟩ L)
  : limₙ a = the L
:= sorry
open Classical in
/-- Sequence Limit Expression → Sequence Limit -/
theorem SeqLimitExpr_to_SeqLimit {a : ℕ → ℝ} {L : ℝ} {init : ℕ}
    (h_lim : limₙ a = the L)
  : SeqLimit ⟨a, init, none⟩ L := sorry
open Classical in
/-- Function Limit → Function Limit Expression -/
theorem FuncLimit_to_FuncLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : FuncLimit ⟨f, I⟩ x₀ L)
  : lim f x₀ = the L
:= sorry
open Classical in
/-- Function Limit Expression → Function Limit -/
theorem FuncLimitExpr_to_FuncLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_lim : lim f x₀ = the L)
  : FuncLimit ⟨f, I⟩ x₀ L
:= sorry
open Classical in
/-- Left Limit → Left Limit Expression -/
theorem LeftLimit_to_LeftLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : LeftLimit ⟨f, I⟩ x₀ L)
  : lim₋ f x₀ = the L
:= sorry
open Classical in
/-- Left Limit Expression → Left Limit -/
theorem LeftLimitExpr_to_LeftLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ I)
    (h_lim : lim₋ f x₀ = the L)
  : LeftLimit ⟨f, I⟩ x₀ L
:= sorry
open Classical in
/-- Right Limit → Right Limit Expression -/
theorem RightLimit_to_RightLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : RightLimit ⟨f, I⟩ x₀ L)
  : lim₊ f x₀ = the L
:= sorry
open Classical in
/-- Right Limit Expression → Right Limit -/
theorem RightLimitExpr_to_RightLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ I)
    (h_lim : lim₊ f x₀ = the L)
  : RightLimit ⟨f, I⟩ x₀ L
:= sorry
open Classical in
/-- Limit at Negative Infinity → Expression of Limit at Negative Infinity -/
theorem NegInftyLimit_to_NegInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : NegInftyLimit ⟨f, I⟩ L)
  : lim₋∞ f = the L
:= sorry
open Classical in
/-- Expression of Limit at Negative Infinity → Limit at Negative Infinity -/
theorem NegInftyLimitExpr_to_NegInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I)
    (h_lim : lim₋∞ f = the L)
  : NegInftyLimit ⟨f, I⟩ L
:= sorry
open Classical in
/-- Limit at Positive Infinity → Expression of Limit at Positive Infinity -/
theorem PosInftyLimit_to_PosInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : PosInftyLimit ⟨f, I⟩ L)
  : lim₊∞ f = the L
:= sorry
open Classical in
/-- Expression of Limit at Positive Infinity → Limit at Positive Infinity -/
theorem PosInftyLimitExpr_to_PosInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Ioi M ⊆ I)
    (h_lim : lim₊∞ f = the L)
  : PosInftyLimit ⟨f, I⟩ L
:= sorry
open Classical in
/-- Limit at Infinity → Expression of Limit at Infinity -/
theorem InftyLimit_to_InftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : InftyLimit ⟨f, I⟩ L)
  : lim∞ f = the L
:= sorry
open Classical in
/-- Expression of Limit at Infinity → Limit at Infinity -/
theorem InftyLimitExpr_to_InftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I ∧ Ioi M ⊆ I)
    (h_lim : lim∞ f = the L)
  : InftyLimit ⟨f, I⟩ L
:= sorry
/-! # Properties of Limit Expression -/

open Classical in
/-- Congruence of Sequence Limit (Expression) -/
lemma SeqLimitExpr.Congr {a b : ℕ → ℝ}
    (h_congr : ∃ N : ℕ, ∀ n > N, a n = b n)
  : limₙ a =? limₙ b
:= sorry
/-- Congruence of Function Limit (Expression) -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry
/-- Congruence of Left Limit (Expression) -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= sorry
/-- Congruence of Right Limit (Expression) -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_congr : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= sorry
/-- Congruence of Limit at Negative Infinity (Expression) -/
lemma NegInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Iio (-M), f x = g x)
  : lim₋∞ f =? lim₋∞ g
:= sorry
/-- Congruence of Limit at Positive Infinity (Expression) -/
lemma PosInftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, ∀ x ∈ Ioi M, f x = g x)
  : lim₊∞ f =? lim₊∞ g
:= sorry
/-- Congruence of Limit at Infinity (Expression) -/
lemma InftyLimitExpr.Congr {f g : ℝ → ℝ}
    (h_congr : ∃ M > 0, (∀ x ∈ Iio (-M), f x = g x) ∧ (∀ x ∈ Ioi M, f x = g x))
  : lim∞ f =? lim∞ g
:= sorry
/-- Function Limit → Left Limit (Expression) -/
theorem FuncLimitExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f x₀ =? lim f x₀
:= sorry
/-- Function Limit → Right Limit (Expression) -/
theorem FuncLimitExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f x₀ =? lim f x₀
:= sorry
/-- Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr_toNeg {f : ℝ → ℝ}
  : lim₋∞ f =? lim∞ f
:= sorry
/-- Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr_toPos {f : ℝ → ℝ}
  : lim₊∞ f =? lim∞ f
:= sorry


-- ========================================== --
-- File: Calculus_21/Continuity/Defs.lean
-- ========================================== --

/-
    Calculus_21.Continuity.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Definitions of Function Continuity -/

/-- Continuous at Some Point -/
def isContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ FuncLimit F x₀ (F.map x₀)

/-- Continuous Everywhere -/
abbrev isContinuous (F : Function) : Prop :=
  ∀ x ∈ F.domain, isContinuousAt F x

/-- Continuous on the Interval -/
abbrev isContinuousIn (F : Function) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, isContinuousAt F x

/-- Left Continuous at Some Point -/
def isLeftContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ LeftLimit F x₀ (F.map x₀)

/-- Right Continuous at Some Point -/
def isRightContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  x₀ ∈ F.domain ∧ RightLimit F x₀ (F.map x₀)

/-- Continuous on the Closed Interval
    Similar to `isContinuousIn`, but continuity at the endpoints represents right
    continuity and left continuity respectively.
    - Before using it, please make sure that `l < r` -/
abbrev isContinuousInIcc (F : Function) (l r : ℝ) : Prop :=
  isContinuousIn F (Ioo l r)
  ∧ isRightContinuousAt F l
  ∧ isLeftContinuousAt F r


/-! # Lemmas on Function Continuity -/

/-- Continuous Everywhere ⇒ Continuous at Some Point -/
lemma isContinuous_implies_At {F : Function} {x₀ : ℝ}
    (h_cont : isContinuous F) (h_dom : x₀ ∈ F.domain)
  : isContinuousAt F x₀
:= sorry
/-- Continuous on the Interval ⇒ Continuous at Some Point -/
lemma isContinuousIn_implies_At {F : Function} {x₀ : ℝ} {I : Set ℝ}
    (h_cont : isContinuousIn F I) (h_dom : x₀ ∈ I)
  : isContinuousAt F x₀
:= sorry
/-- Continuous at Some Point ⇒ Left Continuous at Some Point -/
lemma isContinuousAt_implies_LeftAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isLeftContinuousAt F x₀
:= sorry
/-- Continuous at Some Point ⇒ Right Continuous at Some Point -/
lemma isContinuousAt_implies_RightAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isRightContinuousAt F x₀
:= sorry


-- ========================================== --
-- File: Calculus_21/Differential/Defs.lean
-- ========================================== --

/-
    Calculus_21.Differential.Defs
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Definitions of Derivative -/

/-- Derivative -/
def Deriv (F : Function) (x₀ L : ℝ) : Prop :=
  FuncLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

abbrev isDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Deriv F x₀ L

abbrev isDerivable (F : Function) : Prop :=
  ∀ x ∈ F.domain, isDerivableAt F x

open Classical in
/-- Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def Diff (F : Function) : Function where
  map := fun x =>
    if h : isDerivableAt F x then
      Classical.choose h
    else 0
  domain := { x | isDerivableAt F x }

/-- N-th Order Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def NthDiff (n : ℕ) (F : Function) : Function :=
  match n with
  | 0     => F
  | n + 1 => Diff (NthDiff n F)

/-- N-th Order Derivative -/
def NthDeriv (n : ℕ) (F : Function) (x₀ L : ℝ) : Prop :=
  match n with
  | 0     => F.map x₀ = L ∧ x₀ ∈ F.domain
  | n + 1 => Deriv (NthDiff n F) x₀ L

abbrev isNthDerivableAt (n : ℕ) (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, NthDeriv n F x₀ L

abbrev isNthDerivable (n : ℕ) (F : Function) : Prop :=
  ∀ x ∈ F.domain, ∃ L : ℝ, NthDeriv n F x L

/-- Left Derivative -/
def LeftDeriv (F : Function) (x₀ L : ℝ) : Prop :=
  LeftLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

abbrev isLeftDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftDeriv F x₀ L

/-- Right Derivative -/
def RightDeriv (F : Function) (x₀ L : ℝ) : Prop :=
  RightLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

abbrev isRightDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightDeriv F x₀ L


/-! # Lemmas on N-th Order Differential -/

lemma NthDiff_zero {F : Function}
  : NthDiff 0 F = F
:= sorry
lemma NthDiff_succ {n : ℕ} {F : Function}
  : NthDiff (n + 1) F = Diff (NthDiff n F)
:= sorry
lemma NthDeriv_zero {F : Function} {x₀ D : ℝ}
  : NthDeriv 0 F x₀ D ↔ F.map x₀ = D ∧ x₀ ∈ F.domain
:= sorry
lemma NthDeriv_succ {n : ℕ} {F : Function} {x₀ D : ℝ}
  : NthDeriv (n + 1) F x₀ D ↔ Deriv (NthDiff n F) x₀ D
:= sorry
/-- Uniqueness of N-th Order Derivative -/
lemma NthDeriv_Unique {n : ℕ} {F : Function} {x₀ D₁ D₂ : ℝ}
    (h₁ : NthDeriv n F x₀ D₁) (h₂ : NthDeriv n F x₀ D₂) : D₁ = D₂ := sorry


-- ========================================== --
-- File: Calculus_21/Differential/Expr.lean
-- ========================================== --

/-
    Calculus_21.Differential.Expr
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/



/-! # Derivative Expression -/

noncomputable section

open Classical in
/-- Derivative Expression -/
def DerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- Left Derivative Expression -/
def LeftDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₋ (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- Right Derivative Expression -/
def RightDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  lim₊ (fun x ↦ (f x - f x₀) / (x - x₀) : ℝ → ℝ) x₀

open Classical in
/-- N-th Order Derivative Expression -/
def NthDerivExpr (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isNthDerivableAt n ⟨f, Iii⟩ x₀ then the (choose h)
  else none

end

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)
macro "Dₙ" : term => `(NthDerivExpr)


/-! # Bridges between Derivative & Derivative Expression -/

open Classical in
/-- Derivative → Derivative Expression -/
theorem Deriv_to_DerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : Deriv ⟨f, I⟩ x₀ A)
  : D f x₀ = the A
:= sorry
open Classical in
/-- Derivative Expression → Derivative -/
theorem DerivExpr_to_Deriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D f x₀ = the A)
  : Deriv ⟨f, I⟩ x₀ A
:= sorry
open Classical in
/-- Left Derivative → Left Derivative Expression -/
theorem LeftDeriv_to_LeftDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : LeftDeriv ⟨f, I⟩ x₀ A)
  : D₋ f x₀ = the A
:= sorry
open Classical in
/-- Left Derivative Expression → Left Derivative -/
theorem LeftDerivExpr_to_LeftDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₋ f x₀ = the A)
  : LeftDeriv ⟨f, I⟩ x₀ A
:= sorry
open Classical in
/-- Right Derivative → Right Derivative Expression -/
theorem RightDeriv_to_RightDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_deriv : RightDeriv ⟨f, I⟩ x₀ A)
  : D₊ f x₀ = the A
:= sorry
open Classical in
/-- Right Derivative Expression → Right Derivative -/
theorem RightDerivExpr_to_RightDeriv {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_deriv : D₊ f x₀ = the A)
  : RightDeriv ⟨f, I⟩ x₀ A
:= sorry
open Classical in
/-- N-th Order Derivative → N-th Order Derivative Expression -/
theorem NthDeriv_to_NthDerivExpr {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : NthDeriv n ⟨f, Iii⟩ x₀ A)
  : Dₙ n f x₀ = the A
:= sorry
open Classical in
/-- N-th Order Derivative Expression → N-th Order Derivative -/
theorem NthDerivExpr_to_NthDeriv {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Dₙ n f x₀ = the A)
  : NthDeriv n ⟨f, Iii⟩ x₀ A
:= sorry
/-- Derivative → Left Derivative (Expression) -/
theorem DerivExpr_toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : D₋ f x₀ =? D f x₀
:= sorry
/-- Derivative → Right Derivative (Expression) -/
theorem DerivExpr_toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : D₊ f x₀ =? D f x₀
:= sorry


-- ========================================== --
-- File: Calculus_21.lean
-- ========================================== --

/-
    Calculus_21
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

-- import «Calculus_21».Prelude
-- import «Calculus_21».Expr.Tactics
-- import «Calculus_21».Function.Tactics.ToFunction
-- import «Calculus_21».Limit.Infinitesimal.Defs
-- import «Calculus_21».Limit.Infinitesimal.Higher
-- import «Calculus_21».Limit.Infinitesimal.Equivalent
-- import «Calculus_21».Limit.Infinitesimal.Rules
-- import «Calculus_21».Limit.Rules
-- import «Calculus_21».Limit.L'Hospital
-- import «Calculus_21».Continuity.Elementary
-- import «Calculus_21».Continuity.Rules
-- import «Calculus_21».Continuity.ClosedInterval
-- import «Calculus_21».Differential.Rules
-- import «Calculus_21».Differential.Elementary
-- import «Calculus_21».Differential.Tactic
-- import «Calculus_21».Differential.MeanValue
-- import «Calculus_21».Differential.TaylorExpansion
-- import «Calculus_21».Limit.Tactics.Simplify
-- import «Calculus_21».Limit.Tactics.Congr
-- import «Calculus_21».Limit.Tactics.Equiv
-- import «Calculus_21».Limit.Tactics.Rational
-- import «Calculus_21».Limit.Tactics.L'Hospital


