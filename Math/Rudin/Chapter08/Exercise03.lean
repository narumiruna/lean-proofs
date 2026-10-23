module

public import Mathlib

/-! # Chapter 8, Exercise 3
Nonnegative sums use extended values, so divergent iterated sums are retained.
Indices start at one in the source; the Lean index `n` denotes source `n+1`.
Source: book page 196, PDF page 205.
-/

@[expose] public section

open Filter
open scoped Topology ENNReal

namespace Rudin.Chapter08

/-- Tonelli for the two nonnegative sums, including the value infinity. -/
theorem exercise03_nonnegative_interchange (a : ℕ → ℕ → ℝ≥0∞) :
    (∑' i, ∑' j, a i j) = ∑' j, ∑' i, a i j := ENNReal.tsum_comm

/-- The sums are limits of the natural ordered partial sums, not default values. -/
theorem exercise03_ordered_sums (a : ℕ → ℕ → ℝ≥0∞) :
    (∀ i, Tendsto (fun N => ∑ j ∈ Finset.range N, a i j) atTop (𝓝 (∑' j, a i j))) ∧
    Tendsto (fun N => ∑ i ∈ Finset.range N, ∑' j, a i j)
      atTop (𝓝 (∑' i, ∑' j, a i j)) :=
  ⟨fun _ => ENNReal.summable.hasSum.tendsto_sum_nat, ENNReal.summable.hasSum.tendsto_sum_nat⟩

/-- Explicitly, an infinite value in one order is infinite in the other. -/
theorem exercise03_infinite_iff (a : ℕ → ℕ → ℝ≥0∞) :
    (∑' i, ∑' j, a i j) = ∞ ↔ (∑' j, ∑' i, a i j) = ∞ := by
  rw [exercise03_nonnegative_interchange]

/-- Apply the extended formula to the source's finite nonnegative real entries. -/
theorem exercise03_real_entries (a : ℕ → ℕ → ℝ) (_ha : ∀ i j, 0 ≤ a i j) :
    (∑' i, ∑' j, ENNReal.ofReal (a i j)) = ∑' j, ∑' i, ENNReal.ofReal (a i j) :=
  exercise03_nonnegative_interchange _

end Rudin.Chapter08
