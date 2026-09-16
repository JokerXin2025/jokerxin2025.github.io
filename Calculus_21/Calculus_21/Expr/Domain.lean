/-
    «Calculus_21».Expr.Domain
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Prelude
set_option linter.style.header false


/-! # Abstract Domains -/

namespace Expr

/-- Information precision, directed from more precise to less precise values. -/
class Precision (A : Type u) where
  le : A → A → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

namespace Precision

variable {A : Type u} [Precision A]

abbrev Rel : A → A → Prop := Precision.le

theorem le_refl (a : A) : Rel a a := Precision.refl a

theorem le_trans {a b c : A} : Rel a b → Rel b c → Rel a c :=
  Precision.trans

end Precision

/-- Interpretation of abstract values as sets of concrete outcomes. -/
class Concretization (A : Type u) (C : outParam (Type v)) [Precision A] where
  gamma : A → Set C
  mono : ∀ {a b}, Precision.Rel a b → gamma a ⊆ gamma b

namespace Concretization

variable {A : Type u} {C : Type v} [Precision A] [Concretization A C]

abbrev Gamma (a : A) : Set C := Concretization.gamma a

theorem gamma_mono {a b : A} (h : Precision.Rel a b) : Gamma a ⊆ Gamma b :=
  Concretization.mono h

end Concretization

/-- An abstract value proves a concrete observation when all its outcomes satisfy it. -/
def Proves {A : Type u} {C : Type v} [Precision A] [Concretization A C]
    (a : A) (P : C → Prop) : Prop :=
  ∀ c ∈ Concretization.Gamma a, P c

/-- Proper values are canonical singleton abstract values. -/
class ProperDomain (A : Type u) (C : outParam (Type v))
    [Precision A] [Concretization A C] where
  isProper : A → Prop
  singleton : ∀ {a}, isProper a → ∃ c, Concretization.Gamma a = {c}
  rigid : ∀ {a b}, Precision.Rel a b → isProper b → a = b

namespace ProperDomain

variable {A : Type u} {C : Type v}
variable [Precision A] [Concretization A C] [ProperDomain A C]

theorem getSingleton {a : A} (h : ProperDomain.isProper a) :
    ∃ c, Concretization.Gamma a = {c} :=
  ProperDomain.singleton h

theorem eq_of_le {a b : A} (h : Precision.Rel a b)
    (hb : ProperDomain.isProper b) : a = b :=
  ProperDomain.rigid h hb

end ProperDomain

/-! # Verified abstract transformers -/

/-- A unary abstract transformer preserves information precision. -/
class UnaryTransformer {A : Type u} [Precision A] (op : A → A) : Prop where
  monotone : ∀ {a b}, Precision.Rel a b → Precision.Rel (op a) (op b)

/-- A binary abstract transformer preserves information precision in both inputs. -/
class BinaryTransformer {A : Type u} [Precision A] (op : A → A → A) : Prop where
  monotone_left : ∀ {a a' b}, Precision.Rel a a' →
    Precision.Rel (op a b) (op a' b)
  monotone_right : ∀ {a b b'}, Precision.Rel b b' →
    Precision.Rel (op a b) (op a b')

namespace Transformer

variable {A : Type u} [Precision A]

theorem unary {op : A → A} [UnaryTransformer op] {a b : A}
    (h : Precision.Rel a b) : Precision.Rel (op a) (op b) :=
  UnaryTransformer.monotone h

theorem binary {op : A → A → A} [BinaryTransformer op]
    {a a' b b' : A} (ha : Precision.Rel a a') (hb : Precision.Rel b b') :
    Precision.Rel (op a b) (op a' b') :=
  Precision.le_trans (BinaryTransformer.monotone_left ha)
    (BinaryTransformer.monotone_right hb)

end Transformer

/-- Soundness of a unary abstract transformer for a concrete relation. -/
class UnaryTransformer.Sound {A : Type u} {C : Type v}
    [Precision A] [Concretization A C] (op : A → A)
    (concrete : C → C → Prop) : Prop where
  sound : ∀ {a x y}, x ∈ Concretization.Gamma a → concrete x y →
    y ∈ Concretization.Gamma (op a)

/-- Soundness of a binary abstract transformer for a concrete relation. -/
class BinaryTransformer.Sound {A : Type u} {C : Type v}
    [Precision A] [Concretization A C] (op : A → A → A)
    (concrete : C → C → C → Prop) : Prop where
  sound : ∀ {a b x y z}, x ∈ Concretization.Gamma a →
    y ∈ Concretization.Gamma b → concrete x y z →
    z ∈ Concretization.Gamma (op a b)

namespace Transformer

variable {A : Type u} {C : Type v} [Precision A] [Concretization A C]

theorem unary_sound {op : A → A} {concrete : C → C → Prop}
    [UnaryTransformer.Sound op concrete] {a : A} {x y : C}
    (hx : x ∈ Concretization.Gamma a) (hxy : concrete x y) :
    y ∈ Concretization.Gamma (op a) :=
  UnaryTransformer.Sound.sound hx hxy

theorem binary_sound {op : A → A → A} {concrete : C → C → C → Prop}
    [BinaryTransformer.Sound op concrete] {a b : A} {x y z : C}
    (hx : x ∈ Concretization.Gamma a) (hy : y ∈ Concretization.Gamma b)
    (hxyz : concrete x y z) : z ∈ Concretization.Gamma (op a b) :=
  BinaryTransformer.Sound.sound hx hy hxyz

end Transformer

/-- Necessary conditions for a unary abstract result to be proper. -/
class ProperBackwardUnary {A : Type u} {C : Type v}
    [Precision A] [Concretization A C] [ProperDomain A C]
    (op : A → A) where
  pre : A → Prop
  necessary : ∀ {a}, ProperDomain.isProper (op a) → pre a

/-- Necessary conditions for a binary abstract result to be proper. -/
class ProperBackwardBinary {A : Type u} {C : Type v}
    [Precision A] [Concretization A C] [ProperDomain A C]
    (op : A → A → A) where
  pre : A → A → Prop
  necessary : ∀ {a b}, ProperDomain.isProper (op a b) → pre a b

namespace ProperBackward

variable {A : Type u} {C : Type v}
variable [Precision A] [Concretization A C] [ProperDomain A C]

theorem unary {op : A → A} [spec : ProperBackwardUnary op] {a : A}
    (h : ProperDomain.isProper (op a)) : spec.pre a :=
  spec.necessary h

theorem binary {op : A → A → A} [spec : ProperBackwardBinary op] {a b : A}
    (h : ProperDomain.isProper (op a b)) : spec.pre a b :=
  spec.necessary h

end ProperBackward

end Expr
