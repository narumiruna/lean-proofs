module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic

/-!
# Irrationality of the exponential at one

The factorial bounds for `Real.exp` give a positive remainder smaller than
`1 / n!`. If `Real.exp 1` were rational, multiplication by a sufficiently
large factorial would make that remainder an integer.
-/

@[expose] public section

namespace Rudin.Support.EulerIrrational

open Finset

private theorem remainder_pos (n : ℕ) :
    0 < Real.exp 1 - ∑ k ∈ range (n + 1), (1 : ℝ) / k.factorial := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (n + 2)
  simp only [one_pow] at h
  rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ] at h
  have hp : (0 : ℝ) < 1 / (n + 1).factorial := by positivity
  linarith

private theorem scaled_remainder_lt_one (n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : ℝ) *
      (Real.exp 1 - ∑ k ∈ range (n + 1), (1 : ℝ) / k.factorial) < 1 := by
  have h := Real.exp_bound (x := 1) (by norm_num) (n := n + 1) (by omega)
  simp only [abs_one, one_pow, one_mul] at h
  have h' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans h)
    (show (0 : ℝ) ≤ n.factorial by positivity)
  refine h'.trans_lt ?_
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp
  nlinarith

private theorem scaled_partial_sum_integer (n : ℕ) :
    ∃ z : ℤ, (n.factorial : ℝ) *
      (∑ k ∈ range (n + 1), (1 : ℝ) / k.factorial) = z := by
  refine ⟨((∑ k ∈ range (n + 1), n.factorial / k.factorial : ℕ) : ℤ), ?_⟩
  rw [Int.cast_natCast, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := mem_range.mp hk; omega
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkn) (by positivity)]
  ring

/-- The value of the real exponential function at one is irrational. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  let n := q.den + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.den_pos (show q.den ≤ n by dsimp [n]; omega)
  have he : (n.factorial : ℝ) * Real.exp 1 = (q.num * (c : ℤ) : ℤ) := by
    rw [← hq, hc, Nat.cast_mul, Rat.cast_def]
    push_cast
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  obtain ⟨z, hz⟩ := scaled_partial_sum_integer n
  have hpos := mul_pos (show (0 : ℝ) < n.factorial by positivity) (remainder_pos n)
  have hlt := scaled_remainder_lt_one n hn
  rw [mul_sub, he, hz, ← Int.cast_sub] at hpos hlt
  have hi : (0 : ℤ) < q.num * (c : ℤ) - z := by exact_mod_cast hpos
  have hj : q.num * (c : ℤ) - z < (1 : ℤ) := by exact_mod_cast hlt
  omega

end Rudin.Support.EulerIrrational
