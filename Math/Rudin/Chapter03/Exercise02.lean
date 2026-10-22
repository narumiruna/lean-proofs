module

public import Mathlib

/-! # Exercise 3.2: rationalization of a square-root difference. -/

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- Rationalization, for a positive real argument. -/
theorem exercise02_rationalize {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x ^ 2 + x) - x = 1 / (Real.sqrt (1 + 1 / x) + 1) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have harg : 0 ≤ 1 + 1 / x := by positivity
  have hs : (Real.sqrt (1 + 1 / x)) ^ 2 = 1 + 1 / x := Real.sq_sqrt harg
  have hden : Real.sqrt (1 + 1 / x) + 1 ≠ 0 := by positivity
  have heq : x ^ 2 + x = x ^ 2 * (1 + 1 / x) := by field_simp
  rw [heq, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  apply (eq_div_iff hden).2
  have hh : x * ((Real.sqrt (1 + 1 / x)) ^ 2 - 1) = 1 := by
    rw [hs]
    field_simp
    ring
  nlinarith [hh]

/-- The requested limit is one half. The index zero does not affect the limit. -/
theorem exercise02_limit :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) ^ 2 + n) - n) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Tendsto (fun n : ℕ => Real.sqrt (1 + 1 / (n : ℝ)) + 1)
      atTop (𝓝 (2 : ℝ)) := by
    convert (((tendsto_const_nhds (x := (1 : ℝ))).add hi).sqrt.add_const 1) using 1
    norm_num
  have ht : Tendsto (fun n : ℕ => 1 / (Real.sqrt (1 + 1 / (n : ℝ)) + 1))
      atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds.div hs (by norm_num : (2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (exercise02_rationalize (by exact_mod_cast (show 0 < n by omega))).symm

end Rudin.Chapter03
