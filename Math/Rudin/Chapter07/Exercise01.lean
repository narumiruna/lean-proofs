module

public import Mathlib

/-!
# R07E01: a common bound for a uniformly convergent bounded sequence

Source: Rudin, Third Edition, book page 165 (PDF 174).
The domain set may be empty. Individual bounds need not be uniform initially.
-/

@[expose] public section

namespace Rudin.Chapter07

open Set Filter
open scoped Topology

/-- Uniform convergence plus individual boundedness gives one bound for all
indices and all points. This includes real and complex functions. -/
theorem exercise01_uniform_bound {X E : Type*} [NormedAddCommGroup E]
    {F : ℕ → X → E} {f : X → E} {s : Set X}
    (hu : TendstoUniformlyOn F f atTop s)
    (hb : ∀ n, ∃ M : ℝ, ∀ x ∈ s, ‖F n x‖ ≤ M) :
    ∃ M : ℝ, ∀ n x, x ∈ s → ‖F n x‖ ≤ M := by
  choose M hM using hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one)
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |M i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨2 + |M N| + ∑ i ∈ Finset.range N, |M i|, ?_⟩
  intro n x hx
  by_cases hn : n < N
  · have hi := Finset.single_le_sum (s := Finset.range N) (f := fun i => |M i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    linarith [hM n x hx, le_abs_self (M n), abs_nonneg (M N)]
  · have hbase : ‖f x‖ ≤ M N + 1 := by
      have hd : ‖f x - F N x‖ < 1 := by
        simpa only [dist_eq_norm] using hN N le_rfl x hx
      have ht := norm_add_le (f x - F N x) (F N x)
      rw [sub_add_cancel] at ht
      linarith [hM N x hx]
    have hd : ‖F n x - f x‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hN n (Nat.le_of_not_gt hn) x hx
    have ht := norm_add_le (F n x - f x) (f x)
    rw [sub_add_cancel] at ht
    linarith [le_abs_self (M N)]

end Rudin.Chapter07
