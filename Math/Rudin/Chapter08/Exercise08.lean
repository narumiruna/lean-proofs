module

public import Mathlib

/-! # Chapter 8, Exercise 8
Source: book page 197, PDF page 206.
-/

@[expose] public section

namespace Rudin.Chapter08

theorem exercise08_integer_bound (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ (n : ℝ) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((n : ℝ) * x) * Real.cos x| +
          |Real.cos ((n : ℝ) * x) * Real.sin x| := abs_add_le _ _
      _ = |Real.sin ((n : ℝ) * x)| * |Real.cos x| +
          |Real.cos ((n : ℝ) * x)| * |Real.sin x| := by rw [abs_mul, abs_mul]
      _ ≤ |Real.sin ((n : ℝ) * x)| * 1 + 1 * |Real.sin x| :=
        add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
      _ ≤ ((n : ℝ) + 1) * |Real.sin x| := by nlinarith

/-- The exact printed noninteger counterexample. -/
theorem exercise08_noninteger_failure :
    |Real.sin ((1 / 2 : ℝ) * Real.pi)| > (1 / 2 : ℝ) * |Real.sin Real.pi| := by
  rw [one_div_mul_eq_div, Real.sin_pi_div_two, Real.sin_pi]
  norm_num

end Rudin.Chapter08
