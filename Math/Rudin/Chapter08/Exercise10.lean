module

public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib

/-! # Chapter 8, Exercise 10
The divergence conclusion is for ordered prime reciprocal partial sums.
Source: book page 197, PDF page 206.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter08

noncomputable def exercise10Partial (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime, 1 / (p : ℝ)

theorem exercise10_partial_eq (N : ℕ) :
    exercise10Partial N = ∑ p ∈ Finset.range N, if Nat.Prime p then 1 / (p : ℝ) else 0 := by
  simp [exercise10Partial, Finset.sum_filter]

/-- The source series tends to positive infinity. -/
theorem exercise10_prime_reciprocals : Tendsto exercise10Partial atTop atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n : ℕ => show 0 ≤ (if Nat.Prime n then 1 / (n : ℝ) else 0) by
      split_ifs <;> positivity)).mp (by
        have he : (fun n : ℕ => if Nat.Prime n then 1 / (n : ℝ) else 0) =
            {p : ℕ | Nat.Prime p}.indicator (fun n => 1 / (n : ℝ)) := by
          funext n
          simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [he]
        exact not_summable_one_div_on_primes)
  change Tendsto (fun N => exercise10Partial N) atTop atTop
  simpa only [exercise10_partial_eq] using h

theorem exercise10_unbounded : ∀ M : ℝ, ∃ N : ℕ, M < exercise10Partial N := by
  intro M
  exact (exercise10_prime_reciprocals.eventually (eventually_gt_atTop M)).exists

end Rudin.Chapter08
