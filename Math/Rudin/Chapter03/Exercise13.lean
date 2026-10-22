module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # R03E13: absolute convergence of the Cauchy product
The indices start at zero, as in the source. Absolute convergence is expressed
by summability of the nonnegative real norms; the conclusion also states
convergence of their ordered natural partial sums.
-/

@[expose] public section

namespace Rudin.Chapter03

open Filter Topology

/-- The Cauchy product of two absolutely convergent complex series is absolutely
convergent. The second conclusion uses ordered partial sums. -/
theorem exercise13_absolute_cauchy_product_of_summable_norm (a b : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    Summable (fun n => ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖) ∧
      ∃ s : ℝ, Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖) atTop (nhds s) := by
  have h := summable_norm_sum_mul_range_of_summable_norm ha hb
  exact ⟨h, ⟨_, h.hasSum.tendsto_sum_nat⟩⟩

/-- Source formulation: the hypotheses themselves use ordered natural partial
sums of absolute values. Nonnegativity supplies the bridge to Mathlib's
summability of the norms. No unconditional summability of a conditional
complex series is assumed. -/
theorem exercise13_absolute_cauchy_product (a b : ℕ → ℂ)
    (ha : ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖a n‖) atTop (nhds s))
    (hb : ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ‖b n‖) atTop (nhds s)) :
    Summable (fun n => ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖) ∧
      ∃ s : ℝ, Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖) atTop (nhds s) := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  have hsa : Summable (fun n => ‖a n‖) :=
    ⟨s, (hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (a n)) s).mpr hs⟩
  have hsb : Summable (fun n => ‖b n‖) :=
    ⟨t, (hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (b n)) t).mpr ht⟩
  exact exercise13_absolute_cauchy_product_of_summable_norm a b hsa hsb

end Rudin.Chapter03
