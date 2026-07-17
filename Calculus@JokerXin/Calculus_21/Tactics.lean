import «Calculus_21».Prelude


/- # Lemmas for `simp` -/

lemma normalize_ln : ln = Real.log := rfl

lemma normalize_log {a x : ℝ} : log a x = Real.log x / Real.log a := rfl


/-- ## Recover Form
    __Usage__ `recover_form`
-/
macro "recover_form" : tactic => `(tactic|
  simp_all only [
    normalize_ln,
    normalize_log
  ]
)
