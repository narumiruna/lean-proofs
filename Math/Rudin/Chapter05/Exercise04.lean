module

public import Mathlib

@[expose] public section

open Set
open scoped BigOperators

namespace Rudin.Chapter05

/-- An antiderivative of the polynomial in Exercise 4. -/
theorem exercise04_antiderivative (n : ℕ) (C : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
      C k / (k + 1 : ℝ) * t ^ (k + 1))
      (∑ k ∈ Finset.range (n + 1), C k * x ^ k) x := by
  convert HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.range (n + 1)) =>
    ((hasDerivAt_pow (k + 1) x).const_mul (C k / (k + 1 : ℝ)))) using 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  field_simp

/-- Exercise 4: Rolle's theorem gives a root in the open interval.
No nonzero-polynomial hypothesis is needed. -/
theorem exercise04_interior_root (n : ℕ) (C : ℕ → ℝ)
    (h : (∑ k ∈ Finset.range (n + 1), C k / (k + 1 : ℝ)) = 0) :
    ∃ x ∈ Ioo (0 : ℝ) 1, (∑ k ∈ Finset.range (n + 1), C k * x ^ k) = 0 := by
  apply exists_hasDerivAt_eq_zero (by norm_num : (0 : ℝ) < 1)
      (f := fun t : ℝ => ∑ k ∈ Finset.range (n + 1), C k / (k + 1 : ℝ) * t ^ (k + 1))
  · exact (continuous_iff_continuousAt.mpr
      (fun x => (exercise04_antiderivative n C x).continuousAt)).continuousOn
  · simpa using h.symm
  · exact fun x _ => exercise04_antiderivative n C x

end Rudin.Chapter05
