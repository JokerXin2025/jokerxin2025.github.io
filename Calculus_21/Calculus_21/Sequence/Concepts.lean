/-
    «Calculus_21».Sequence.Concepts
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Sequence.Defs
set_option linter.style.header false


/-! # Boundedness of RSequence -/

/-- Bounded RSequence -/
def SeqBounded (A : RSequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, |A.map n| < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, |A.map n| < M

/-- Upper-Bounded RSequence -/
def SeqUpperBounded (A : RSequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n < M

/-- Lower-Bounded RSequence -/
def SeqLowerBounded (A : RSequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n > -M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n > -M

page_end
