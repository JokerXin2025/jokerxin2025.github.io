/-
    «Calculus_21».Limit.Tactics.Rational
    Released under MIT license as described in the file LICENSE.
    Authors: JokerXin
-/

import «Calculus_21».Limit.Tactics.Cont
set_option linter.style.header false

open Lean Elab Tactic Meta


/-! # Preparations -/

private lemma Limit_Rational_Convergent_Helper {f g : ℝ → ℝ} {x₀ L : ℝ}
    (p q : ℝ → ℝ)
    (h_alg : ∀ x, f x * q x = p x * g x)
    (h_lim : lim (fun x ↦ p x / q x) x₀ = the L) :
    lim (fun x ↦ f x / g x) x₀ = the L := sorry

private lemma Limit_Rational_Divergent_Helper {f g : ℝ → ℝ} {x₀ : ℝ}
    (p q : ℝ → ℝ) (m : ℕ) (h_m_pos : m > 0)
    (h_alg : ∀ x, f x * q x * (x - x₀) ^ m = p x * g x)
    (h_p_ne0 : p x₀ ≠ 0)
    (h_q_ne0 : q x₀ ≠ 0) :
    lim (fun x ↦ f x / g x) x₀ = Except.error .divergent := sorry

def parseStringToTerm (s : String) : CoreM Term := do
  let env ← getEnv
  match Parser.runParserCategory env `term s "<lim_rational.py>" with
  | Except.ok stx => return ⟨stx⟩
  | Except.error err =>
    th_rowError
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
  | th_rowError
  "Tactic `lim_rational` failed:
  The current goal is not an equation."
  if lhs.getAppFn.constName? != some ``FuncLimitExpr then
    th_rowError
  "Tactic `lim_rational` failed:
  The left-hand side of equation isn't one of the following applications:
  `FuncLimitExpr`
  `LeftLimitExpr`
  `RightLimitExpr`"
  let args := lhs.getAppArgs
  let f := args[args.size - 2]!
  let x₀ := args[args.size - 1]!
  let (numStr, denStr) ← lambdaTelescope f fun _ body => do
    let divFn := body.getAppFn
    if  divFn.constName? != some ``HDiv.hDiv
        && divFn.constName? != some ``Div.div then
      th_rowError
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
  if out.exitCode != 0 then
    th_rowError
  "Error from Python:
  {out.stderr}"
  let res := out.stdout.trimAscii.toString
  let Except.ok json := Lean.Json.parse res
  | th_rowError "JSON 解析失败，Python 返回值: {res}"
  let Except.ok pJson := json.getObjVal? "p"
  | th_rowError "Internal error on parameter `p`."
  let Except.ok pStr := pJson.getStr?
  | th_rowError "Internal error on parameter `p`."
  let Except.ok qJson := json.getObjVal? "q"
  | th_rowError "Internal error on parameter `q`."
  let Except.ok qStr := qJson.getStr?
  | th_rowError "Internal error on parameter `q`."
  let Except.ok mJson := json.getObjVal? "m"
  | th_rowError "Internal error on parameter `m`."
  let Except.ok mVal := mJson.getNat?
  | th_rowError "Internal error on parameter `m`."
  let Except.ok isDivJson := json.getObjVal? "is_divergent"
  | th_rowError "Internal error on parameter `is_divergent`."
  let Except.ok isDiv := isDivJson.getBool?
  | th_rowError "Internal error on parameter `is_divergent`."
  let p ← parseStringToTerm s!"fun x : ℝ ↦ {pStr}"
  let q ← parseStringToTerm s!"fun x : ℝ ↦ {qStr}"
  let m := quote mVal
  if isDiv then
    evalTactic (← `(tactic| {
      apply Limit_Rational_Divergent_Helper $p $q $m
      · norm_num; done
      · intros; ring; done
      · norm_num; done
      · norm_num; done
    }))
  else
    evalTactic (← `(tactic| {
      apply Limit_Rational_Convergent_Helper $p $q
      · intros; ring; done
      · lim_cont; done
    }))

page_end
