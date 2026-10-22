module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Filter Finset
open scoped Topology

namespace Rudin.Chapter03

/-- Nonnegative ordinary convergence suffices; unconditional convergence is not assumed.
Here `a n` denotes the source term `a_(n+1)`. -/
theorem exercise07_weighted_roots (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : ∃ s, Tendsto (fun N => ∑ n ∈ range N, a n) atTop (𝓝 s)) :
    Summable (fun n => Real.sqrt (a n) / (n + 1 : ℝ)) := by
  obtain ⟨s, hs⟩ := h
  have hsa : Summable a :=
    ((hasSum_iff_tendsto_nat_of_nonneg ha s).2 hs).summable
  have hp : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hsa.add hp)
  intro n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hsqrt := Real.sq_sqrt (ha n)
  have hsq := sq_nonneg (Real.sqrt (a n) - 1 / (n + 1 : ℝ))
  have hnonneg : 0 ≤ a n + 1 / (n + 1 : ℝ) ^ 2 :=
    add_nonneg (ha n) (by positivity)
  have hid : (1 / (n + 1 : ℝ)) ^ 2 = 1 / (n + 1 : ℝ) ^ 2 := by rw [div_pow, one_pow]
  have hmul : Real.sqrt (a n) / (n + 1 : ℝ) =
      Real.sqrt (a n) * (1 / (n + 1 : ℝ)) := by ring
  rw [hmul]
  nlinarith

end Rudin.Chapter03
