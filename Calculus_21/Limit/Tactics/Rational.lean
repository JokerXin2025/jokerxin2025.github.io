/-
    «Calculus_21».Limit.Tactics.Rational
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Cont
set_option linter.style.header false

open Lean Elab Tactic Meta


/-! # Preparations -/

section
variable {x₀ L : ℝ} {f g : ℝ → ℝ} (p q : ℝ → ℝ) (m : ℕ) (h_m : m > 0)

private lemma convergent_helper
    (h_alg : ∀ x, f x * q x = p x * g x)
    (h_lim : lim x₀ (fun x ↦ p x / q x) = the L)
  : lim x₀ (fun x ↦ f x / g x) = the L
:= sorry

private lemma divergent_helper
    (h_alg : ∀ x, f x * q x * (x - x₀) ^ m = p x * g x)
    (h_p_ne0 : p x₀ ≠ 0)
    (h_q_ne0 : q x₀ ≠ 0)
  : lim x₀ (fun x ↦ f x / g x) =. diverg
:= sorry

end

def parseStringToTerm (s : String) : CoreM Term := do
  let env ← getEnv
  match Parser.runParserCategory env `term s "<lim_rational.py>" with
  | Except.ok stx => return ⟨stx⟩
  | Except.error err => throwError
  "Failed to parse the returned expression from Python:
  {err}"


/-! # Tactics -/

/-- ## Rational Limit Calculator

    __Usage__ `lim_rational`

    - Only used for limit expression, including
      - `SeqLimitExpr` (not yet)
      - `FuncLimitExpr`
      - `LeftLimitExpr` (not yet)
      - `RightLimitExpr` (not yet)
      - `NegInftyLimitExpr` (not yet)
      - `PosInftyLimitExpr` (not yet)
      - `InftyLimitExpr` (not yet)

    - `lim_rational` solves limit expressions of rational functions using
      factorization, whether convergent or not.

    __Examples__
    ```lean
    ```
-/
elab "lim_rational" : tactic => do
  let goal ← getMainTarget
  let some (_, lhs, _) := goal.eq?
  | throwError
  "Tactic `lim_rational` failed:
  The current goal is not an equation."
  if lhs.getAppFn.constName? != some ``FuncLimitExpr then throwError
  "Tactic `lim_rational` failed:
  The left-hand side of equation isn't one of the following applications:
  `FuncLimitExpr`
  `LeftLimitExpr`
  `RightLimitExpr`"
  let args := lhs.getAppArgs
  let x₀ := args[args.size - 2]!
  let f := args[args.size - 1]!
  let (numStr, denStr) ← lambdaTelescope f fun _ body => do
    let divFn := body.getAppFn
    if divFn.constName? != some ``HDiv.hDiv
        && divFn.constName? != some ``Div.div then throwError
  "Tactic `lim_rational` failed:
  The function is not a fraction."
    let num ← toString <$> ppExpr body.appFn!.appArg!
    let den ← toString <$> ppExpr body.appArg!
    return (num.replace "\n" "", den.replace "\n" "")
  let x₀Str ← toString <$> ppExpr x₀
  let x₀StrClean := x₀Str.replace "\n" ""
  let out ← IO.Process.output {
    cmd := "python3"
    args := #["lim_rational.py", numStr, denStr, x₀StrClean]
  }
  if out.exitCode != 0 then throwError
  "Error from Python:
  {out.stderr}"
  let res := out.stdout.trimAscii.toString
  let Except.ok json := Lean.Json.parse res
  | throwError "JSON 解析失败，Python 返回值: {res}"
  let Except.ok pJson := json.getObjVal? "p"
  | throwError "Internal error on parameter `p`."
  let Except.ok pStr := pJson.getStr?
  | throwError "Internal error on parameter `p`."
  let Except.ok qJson := json.getObjVal? "q"
  | throwError "Internal error on parameter `q`."
  let Except.ok qStr := qJson.getStr?
  | throwError "Internal error on parameter `q`."
  let Except.ok mJson := json.getObjVal? "m"
  | throwError "Internal error on parameter `m`."
  let Except.ok mVal := mJson.getNat?
  | throwError "Internal error on parameter `m`."
  let Except.ok isDivergJson := json.getObjVal? "is_divergent"
  | throwError "Internal error on parameter `is_divergent`."
  let Except.ok isDiverg := isDivergJson.getBool?
  | throwError "Internal error on parameter `is_divergent`."
  let p ← parseStringToTerm s!"fun x : ℝ ↦ {pStr}"
  let q ← parseStringToTerm s!"fun x : ℝ ↦ {qStr}"
  let m := quote mVal
  if isDiverg then
    evalTactic <| ← `(tactic|
      · apply divergent_helper $p $q $m
        · norm_num
        · intros; ring
        · norm_num
        · norm_num
    )
  else
    evalTactic <| ← `(tactic|
      · apply convergent_helper $p $q
        · intros; ring
        · lim_cont
    )


page_end
