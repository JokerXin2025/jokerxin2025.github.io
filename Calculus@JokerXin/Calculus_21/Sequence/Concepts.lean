/-
    Calculus_21.Sequence.Concepts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Sequence.Defs
set_option linter.style.header false


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
