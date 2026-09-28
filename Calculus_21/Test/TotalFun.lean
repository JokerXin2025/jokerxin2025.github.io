import Calculus_21.Function.Defs

example (f : ℝ → ℝ) : (total f).map = f := rfl

example (f : ℝ → ℝ) : (total f).domain = Iii := rfl

example : (total_fun x => x + 1) = total (fun x => x + 1) := rfl

example : (total_fun x => x + 1).map 2 = 3 := by norm_num [total]

example : (total_fun (x : ℝ) => x ^ 2).domain = Iii := rfl

example : (total_fun x ↦ x).map = id := rfl

example : (total_fun x : ℝ => x + 1) = (⟨fun x => x + 1, Iii⟩ : RFunction) := rfl

example : (total_fun | x => x + 1).map 0 = 1 := by norm_num [total]

example (a : ℝ) : (total_fun x => a * x).map = fun x => a * x := rfl
