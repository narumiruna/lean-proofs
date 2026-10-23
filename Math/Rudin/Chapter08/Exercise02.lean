module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Chapter 8, Exercise 2
Source: book page 196, PDF page 205. Natural indices start at zero here:
`exercise02_array i j` is the printed entry in row i+1, column j+1.
-/

@[expose] public section

open Filter Topology Finset

namespace Rudin.Chapter08

noncomputable def exercise02_array (i j : ℕ) : ℝ :=
  if i < j then 0 else if i = j then -1 else (1 / 2 : ℝ) ^ (i - j)

/-- The power is exactly the printed integer exponent j-i, not its inverse. -/
theorem exercise02_formula (i j : ℕ) :
    exercise02_array i j =
      if i < j then 0 else if i = j then -1 else (2 : ℝ) ^ ((j : ℤ) - (i : ℤ)) := by
  by_cases hij : i < j
  · simp [exercise02_array, hij]
  by_cases heq : i = j
  · simp [exercise02_array, heq]
  simp only [exercise02_array, hij, heq, ite_false]
  rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
  congr 1
  omega

/-- Direct comparison with Rudin's one-based indices. -/
theorem exercise02_source_formula (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    exercise02_array (i - 1) (j - 1) =
      if i < j then 0 else if i = j then -1 else (2 : ℝ) ^ ((j : ℤ) - (i : ℤ)) := by
  rw [exercise02_formula]
  have hlt : i - 1 < j - 1 ↔ i < j := by omega
  have heq : i - 1 = j - 1 ↔ i = j := by omega
  have hexp : ((j - 1 : ℕ) : ℤ) - ((i - 1 : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by omega
  simp only [hlt, heq, hexp]

private theorem array_shift (i j : ℕ) :
    exercise02_array (i + 1) (j + 1) = exercise02_array i j := by
  simp [exercise02_array]

private theorem row_finite (i : ℕ) :
    ∑ j ∈ range (i + 1), exercise02_array i j = -(1 / 2 : ℝ) ^ i := by
  induction i with
  | zero => simp [exercise02_array]
  | succ i ih =>
    rw [sum_range_succ']
    simp_rw [array_shift]
    rw [ih]
    simp only [exercise02_array, Nat.not_lt_zero, Nat.add_one_ne_zero, ite_false,
      Nat.sub_zero, pow_succ]
    ring

private theorem row_hasSum (i : ℕ) :
    HasSum (exercise02_array i) (-(1 / 2 : ℝ) ^ i) := by
  rw [← row_finite i]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hij : i < j := by
    simp only [mem_range] at hj
    omega
  simp [exercise02_array, hij]

private theorem column_prefix (j : ℕ) :
    ∑ i ∈ range (j + 1), exercise02_array i j = -1 := by
  rw [sum_range_succ]
  have hz : ∑ i ∈ range j, exercise02_array i j = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [exercise02_array, mem_range.mp hi]
  rw [hz]
  simp [exercise02_array]

private theorem column_hasSum (j : ℕ) : HasSum (fun i ↦ exercise02_array i j) 0 := by
  have hg : HasSum (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) 1 := by
    have h := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_right (1 / 2)
    convert h using 1
    · ext n
      exact pow_succ _ _
    · norm_num
  have ht : HasSum (fun n ↦ exercise02_array (n + (j + 1)) j) 1 := by
    convert hg using 1
    ext n
    have hlt : ¬ n + (j + 1) < j := by omega
    have hne : n + (j + 1) ≠ j := by omega
    simp [exercise02_array, hlt, hne, show n + (j + 1) - j = n + 1 by omega]
  have h := HasSum.sum_range_add (f := fun i ↦ exercise02_array i j) (k := j + 1) ht
  rw [column_prefix] at h
  norm_num at h
  exact h

/-- Each row converges in the printed, ordered sense. -/
theorem exercise02_rows (i : ℕ) :
    Tendsto (fun N ↦ ∑ j ∈ range N, exercise02_array i j) atTop
      (𝓝 (-(1 / 2 : ℝ) ^ i)) := (row_hasSum i).tendsto_sum_nat

/-- Each column converges in the printed, ordered sense. -/
theorem exercise02_columns (j : ℕ) :
    Tendsto (fun N ↦ ∑ i ∈ range N, exercise02_array i j) atTop (𝓝 0) :=
  (column_hasSum j).tendsto_sum_nat

theorem exercise02_row_then_outer :
    Tendsto (fun N ↦ ∑ i ∈ range N, ∑' j, exercise02_array i j) atTop (𝓝 (-2)) := by
  simp_rw [(row_hasSum _).tsum_eq]
  have h : HasSum (fun i : ℕ ↦ -(1 / 2 : ℝ) ^ i) (-2) := by
    convert (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).neg using 1
    norm_num
  exact h.tendsto_sum_nat

theorem exercise02_column_then_outer :
    Tendsto (fun N ↦ ∑ j ∈ range N, ∑' i, exercise02_array i j) atTop (𝓝 0) := by
  simp_rw [(column_hasSum _).tsum_eq, sum_const_zero]
  exact tendsto_const_nhds

end Rudin.Chapter08
