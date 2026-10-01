/-
    «Calculus_21».Integral.Partition
    Released under MIT license as described in the file LICENSE.
-/

import «Calculus_21».Integral.PartitionNet
set_option linter.style.header false


/-! # Partitions and Tags -/

namespace Integral

/-- A finite partition with strictly increasing division points. -/
structure Partition (a b : ℝ) where
  count : ℕ
  count_pos : 0 < count
  point : Fin (count + 1) → ℝ
  first_eq : point 0 = a
  last_eq : point (Fin.last count) = b
  increasing : ∀ i j, i < j → point i < point j

/-- Each tag belongs to its closed subinterval. -/
structure TaggedPartition (a b : ℝ) extends Partition a b where
  tag : Fin count → ℝ
  tag_mem : ∀ i, point i.castSucc ≤ tag i ∧ tag i ≤ point i.succ

namespace Partition
variable {a b : ℝ}

def width (P : Partition a b) (i : Fin P.count) : ℝ :=
  P.point i.succ - P.point i.castSucc

theorem width_pos (P : Partition a b) (i : Fin P.count)
  : 0 < P.width i
:= sub_pos.mpr (P.increasing _ _ (by simp))

theorem endpoints_lt (P : Partition a b)
  : a < b
:= by
  have h := P.increasing 0 (Fin.last P.count) (by
    change 0 < P.count
    exact P.count_pos)
  simpa only [P.first_eq, P.last_eq] using h

theorem point_mem (P : Partition a b) (i : Fin (P.count + 1))
  : P.point i ∈ Icc a b
:= by
  constructor
  · by_cases h : i = 0
    · simp [h, P.first_eq]
    · have hi := le_of_lt (P.increasing 0 i (by
        change 0 < i.val
        have : i.val ≠ 0 := fun hi => h (Fin.ext hi)
        omega))
      simpa only [P.first_eq] using hi
  · by_cases h : i = Fin.last P.count
    · simp [h, P.last_eq]
    · have hi := le_of_lt (P.increasing i (Fin.last P.count) (by
        change i.val < P.count
        have : i.val ≠ P.count := fun hi => h (Fin.ext hi)
        omega))
      simpa only [P.last_eq] using hi

theorem point_le (P : Partition a b) {i j : Fin (P.count + 1)} (h : i ≤ j)
  : P.point i ≤ P.point j
:= by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (P.increasing i j hlt)
  · rw [heq]

/-- Join adjacent partitions, representing the shared endpoint only once. -/
noncomputable abbrev append {c : ℝ} (P : Partition a b) (Q : Partition b c)
  : Partition a c
:= {
  count := P.count + Q.count
  count_pos := by have := P.count_pos; omega
  point := fun i =>
    if h : i.val ≤ P.count then P.point ⟨i.val, by omega⟩
    else Q.point ⟨i.val - P.count, by omega⟩
  first_eq := by simp [P.first_eq]
  last_eq := by
    have hq := Q.count_pos
    simp only [Fin.val_last]
    rw [dif_neg (by omega)]
    convert Q.last_eq using 1
    congr 1
    apply Fin.ext
    simp
  increasing := by
    intro i j hij
    have hv : i.val < j.val := hij
    split_ifs with hi hj hj
    · exact P.increasing _ _ hv
    · have hleft : P.point ⟨i.val, by omega⟩ ≤ b := (P.point_mem _).2
      have hright : b < Q.point ⟨j.val - P.count, by omega⟩ := by
        have h := Q.increasing 0 ⟨j.val - P.count, by omega⟩ (by
          change 0 < j.val - P.count
          omega)
        simpa only [Q.first_eq] using h
      exact lt_of_le_of_lt hleft hright
    · omega
    · apply Q.increasing
      change i.val - P.count < j.val - P.count
      omega
}

theorem append_point_left {c : ℝ} (P : Partition a b) (Q : Partition b c)
    (i : Fin (P.count + 1))
  : (P.append Q).point ⟨i.val, by
      change i.val < P.count + Q.count + 1
      have := i.isLt; omega⟩ = P.point i
:= by
  change (if h : i.val ≤ P.count then _ else _) = _
  rw [dif_pos (by have := i.isLt; omega)]

theorem append_point_right {c : ℝ} (P : Partition a b) (Q : Partition b c)
    (i : Fin (Q.count + 1))
  : (P.append Q).point ⟨P.count + i.val, by
      change P.count + i.val < P.count + Q.count + 1
      have := i.isLt; omega⟩ = Q.point i
:= by
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    change (if h : P.count ≤ P.count then _ else _) = Q.point 0
    rw [dif_pos (le_refl _)]
    exact P.last_eq.trans Q.first_eq.symm
  · change (if h : P.count + i.val ≤ P.count then _ else _) = _
    rw [dif_neg (by omega)]
    congr 1
    apply Fin.ext
    simp

theorem append_width_left {c : ℝ} (P : Partition a b) (Q : Partition b c)
    (i : Fin P.count)
  : (P.append Q).width (i.castAdd Q.count) = P.width i
:= by
  unfold width
  rw [show (i.castAdd Q.count).succ =
    (⟨i.succ.val, by have := i.isLt; omega⟩ : Fin (P.count + Q.count + 1)) from rfl]
  rw [P.append_point_left Q i.succ]
  exact congrArg (P.point i.succ - ·) (P.append_point_left Q i.castSucc)

theorem append_width_right {c : ℝ} (P : Partition a b) (Q : Partition b c)
    (i : Fin Q.count)
  : (P.append Q).width (i.natAdd P.count) = Q.width i
:= by
  unfold width
  have hs : (i.natAdd P.count).succ =
      (⟨P.count + i.succ.val, by have := i.isLt; omega⟩ :
        Fin (P.count + Q.count + 1)) := Fin.ext (by simp; omega)
  rw [hs, P.append_point_right Q i.succ]
  exact congrArg (Q.point i.succ - ·) (P.append_point_right Q i.castSucc)

lemma sum_differences (n : ℕ) (p : Fin (n + 1) → ℝ)
  : ∑ i : Fin n, (p i.succ - p i.castSucc) = p (Fin.last n) - p 0
:= by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun i => p i.succ)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at *
    rw [h]
    simp only [Fin.succ_last]
    ring

theorem sum_width (P : Partition a b)
  : ∑ i, P.width i = b - a
:= by
  unfold width
  rw [sum_differences]
  rw [P.last_eq, P.first_eq]

private lemma exists_cell (n : ℕ) (h_n : 0 < n) (p : Fin (n + 1) → ℝ)
    {x : ℝ} (h_left : p 0 ≤ x) (h_right : x ≤ p (Fin.last n))
  : ∃ i : Fin n, p i.castSucc ≤ x ∧ x ≤ p i.succ
:= by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hx : x ≤ p (Fin.succ 0)
    · exact ⟨0, h_left, hx⟩
    · by_cases hn : n = 0
      · subst n
        exact False.elim (hx h_right)
      · obtain ⟨i, hi⟩ := ih (by omega) (fun j => p j.succ)
          (le_of_lt (lt_of_not_ge hx)) h_right
        exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi⟩

theorem exists_cell_of_mem (P : Partition a b) {x : ℝ} (hx : x ∈ Icc a b)
  : ∃ i : Fin P.count, P.point i.castSucc ≤ x ∧ x ≤ P.point i.succ
:= by
  apply exists_cell P.count P.count_pos P.point
  · simpa only [P.first_eq] using hx.1
  · simpa only [P.last_eq] using hx.2

private theorem exists_max_width (P : Partition a b)
  : ∃ i, ∀ j, P.width j ≤ P.width i
:= by
  have h_ne : (Finset.univ : Finset (Fin P.count)).Nonempty :=
    ⟨⟨0, P.count_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ P.width h_ne
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- The actual largest width, not an arbitrary bound supplied with a partition. -/
noncomputable def mesh (P : Partition a b) : ℝ :=
  P.width (Classical.choose P.exists_max_width)

theorem width_le_mesh (P : Partition a b) (i : Fin P.count)
  : P.width i ≤ P.mesh
:= Classical.choose_spec P.exists_max_width i

theorem mesh_pos (P : Partition a b)
  : 0 < P.mesh
:= P.width_pos _

theorem mesh_le (P : Partition a b) {δ : ℝ}
    (h : ∀ i, P.width i ≤ δ)
  : P.mesh ≤ δ
:= h _

/-- Equally spaced points; this construction requires a positive number of cells. -/
noncomputable def uniform (h_ab : a < b) (n : ℕ) (h_n : 0 < n)
  : Partition a b
:= {
  count := n
  count_pos := h_n
  point := fun i => a + (b - a) * (i.val : ℝ) / n
  first_eq := by simp
  last_eq := by
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h_n)
    simp [hn]
  increasing := by
    intro i j hij
    have hn : (0 : ℝ) < n := by exact_mod_cast h_n
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith [div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hij' (sub_pos.mpr h_ab)) hn]
}

theorem uniform_width (h_ab : a < b) (n : ℕ) (h_n : 0 < n)
    (i : Fin n)
  : (uniform h_ab n h_n).width i = (b - a) / n
:= by
  simp only [width, uniform, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem uniform_mesh (h_ab : a < b) (n : ℕ) (h_n : 0 < n)
  : (uniform h_ab n h_n).mesh = (b - a) / n
:= uniform_width h_ab n h_n _

end Partition

namespace TaggedPartition
variable {a b : ℝ}

noncomputable abbrev single (hab : a < b) (x : ℝ) (hx : x ∈ Icc a b)
  : TaggedPartition a b
:= {
  count := 1
  count_pos := by decide
  point := fun i => if i.val = 0 then a else b
  first_eq := rfl
  last_eq := rfl
  increasing := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  tag := fun _ => x
  tag_mem := by intro i; fin_cases i; exact hx
}

theorem single_width (hab : a < b) (x : ℝ) (hx : x ∈ Icc a b) (i : Fin 1)
  : (single hab x hx).width i = b - a
:= by fin_cases i; rfl

theorem single_mesh (hab : a < b) (x : ℝ) (hx : x ∈ Icc a b)
  : (single hab x hx).mesh = b - a
:= single_width hab x hx _

/-- Remove the first cell from a partition with at least two cells. -/
noncomputable abbrev tail (P : TaggedPartition a b) (hn : 1 < P.count)
  : TaggedPartition (P.point ⟨1, by omega⟩) b
:= {
  count := P.count - 1
  count_pos := by omega
  point := fun i => P.point ⟨i.val + 1, by have := i.isLt; omega⟩
  first_eq := rfl
  last_eq := by convert P.last_eq using 1; congr 1; apply Fin.ext; simp; omega
  increasing := by
    intro i j hij
    apply P.increasing
    change i.val + 1 < j.val + 1
    exact Nat.add_lt_add_right hij 1
  tag := fun i => P.tag ⟨i.val + 1, by have := i.isLt; omega⟩
  tag_mem := by
    intro i
    exact P.tag_mem ⟨i.val + 1, by have := i.isLt; omega⟩
}

theorem tail_width (P : TaggedPartition a b) (hn : 1 < P.count)
    (i : Fin (P.count - 1))
  : (P.tail hn).width i = P.width ⟨i.val + 1, by have := i.isLt; omega⟩
:= rfl

theorem tail_mesh_le (P : TaggedPartition a b) (hn : 1 < P.count)
  : (P.tail hn).mesh ≤ P.mesh
:= (P.tail hn).mesh_le (fun i => (P.tail_width hn i).trans_le (P.width_le_mesh _))

/-- Join tagged partitions without changing either family of tags. -/
noncomputable abbrev append {c : ℝ} (P : TaggedPartition a b) (Q : TaggedPartition b c)
  : TaggedPartition a c
:= {
  toPartition := P.toPartition.append Q.toPartition
  tag := Fin.addCases P.tag Q.tag
  tag_mem := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      have hl := P.toPartition.append_point_left Q.toPartition j.castSucc
      have hr := P.toPartition.append_point_left Q.toPartition j.succ
      constructor
      · exact hl.trans_le (P.tag_mem j).1
      · exact (P.tag_mem j).2.trans_eq hr.symm
    · simp only [Fin.addCases_right]
      have hl := P.toPartition.append_point_right Q.toPartition j.castSucc
      have hr := P.toPartition.append_point_right Q.toPartition j.succ
      constructor
      · exact hl.trans_le (Q.tag_mem j).1
      · exact (Q.tag_mem j).2.trans_eq hr.symm
}

theorem append_mesh_le {c δ : ℝ} (P : TaggedPartition a b) (Q : TaggedPartition b c)
    (hP : P.mesh ≤ δ) (hQ : Q.mesh ≤ δ)
  : (P.append Q).mesh ≤ δ
:= by
  apply Partition.mesh_le
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (P.toPartition.append_width_left Q.toPartition j).trans_le
      ((P.width_le_mesh j).trans hP)
  · exact (P.toPartition.append_width_right Q.toPartition j).trans_le
      ((Q.width_le_mesh j).trans hQ)

theorem append_mesh_lt {c δ : ℝ} (P : TaggedPartition a b) (Q : TaggedPartition b c)
    (hP : P.mesh < δ) (hQ : Q.mesh < δ)
  : (P.append Q).mesh < δ
:= lt_of_le_of_lt (P.append_mesh_le Q (le_max_left _ _) (le_max_right _ _))
    (max_lt hP hQ)

/-- Change one tag while retaining the division points. -/
noncomputable def replaceTag (P : TaggedPartition a b) (i : Fin P.count) (x : ℝ)
    (h_x : P.point i.castSucc ≤ x ∧ x ≤ P.point i.succ)
  : TaggedPartition a b
:= {
  toPartition := P.toPartition
  tag := fun j => if j = i then x else P.tag j
  tag_mem := by
    intro j
    by_cases h : j = i
    · subst j
      simpa using h_x
    · simpa [h] using P.tag_mem j
}

/-- Midpoints supply tags for every partition. -/
noncomputable def midpoint (P : Partition a b) : TaggedPartition a b := {
  toPartition := P
  tag := fun i => (P.point i.castSucc + P.point i.succ) / 2
  tag_mem := by
    intro i
    have h := P.increasing i.castSucc i.succ (by simp)
    constructor <;> linarith
}

theorem tag_mem_Icc (P : TaggedPartition a b) (i : Fin P.count)
  : P.tag i ∈ Icc a b
:= ⟨le_trans (P.point_mem i.castSucc).1 (P.tag_mem i).1,
    le_trans (P.tag_mem i).2 (P.point_mem i.succ).2⟩

theorem exists_mesh_lt (h_ab : a < b) {δ : ℝ} (h_δ : 0 < δ)
  : ∃ P : TaggedPartition a b, P.mesh < δ
:= by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hn_pos : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (div_pos (sub_pos.mpr h_ab) h_δ) hn
    exact_mod_cast this
  refine ⟨midpoint (Partition.uniform h_ab n hn_pos), ?_⟩
  change (Partition.uniform h_ab n hn_pos).mesh < δ
  rw [Partition.uniform_mesh]
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  apply (div_lt_iff₀ hn_real).mpr
  have h := (div_lt_iff₀ h_δ).mp hn
  linarith

/-- Information increases as the mesh decreases. -/
def directedSet (h_ab : a < b) : PartitionNet.DirectedSet where
  Index := TaggedPartition a b
  nonempty := ⟨midpoint (Partition.uniform h_ab 1 (by decide))⟩
  rel := fun P Q => Q.mesh ≤ P.mesh
  refl := fun _ => le_refl _
  trans := fun h₁ h₂ => le_trans h₂ h₁
  upper := by
    intro P Q
    obtain ⟨R, hR⟩ := exists_mesh_lt h_ab (lt_min P.mesh_pos Q.mesh_pos)
    exact ⟨R, le_trans (le_of_lt hR) (min_le_left _ _),
      le_trans (le_of_lt hR) (min_le_right _ _)⟩

end TaggedPartition

end Integral


page_end
