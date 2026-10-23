module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Chapter 8, Exercise 4
Source: book page 196, PDF page 205. Limits at zero are punctured.
-/

@[expose] public section

open Filter Topology

namespace Rudin.Chapter08

theorem exercise04_a (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ (b ^ x - 1) / x) (𝓝[≠] 0) (𝓝 (Real.log b)) := by
  simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (HasDerivAt.const_rpow hb (hasDerivAt_id (0 : ℝ))).tendsto_slope_zero

theorem exercise04_b :
    Tendsto (fun x : ℝ ↦ Real.log (1 + x) / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (((hasDerivAt_id (0 : ℝ)).const_add 1).log (by norm_num)).tendsto_slope_zero

/-- The natural real domain holds throughout a neighborhood of zero. -/
theorem exercise04_positive_base : ∀ᶠ x : ℝ in 𝓝[≠] 0, 0 < 1 + x := by
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[≠] 0, -1 < x from
    (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono inf_le_left] with x hx
  linarith

theorem exercise04_c :
    Tendsto (fun x : ℝ ↦ (1 + x) ^ (1 / x)) (𝓝[≠] 0) (𝓝 (Real.exp 1)) := by
  apply (Real.continuous_exp.continuousAt.tendsto.comp exercise04_b).congr'
  filter_upwards [exercise04_positive_base] with x hx
  simp [Real.rpow_def_of_pos hx, div_eq_mul_inv]

theorem exercise04_d (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 + x / n) ^ n) atTop (𝓝 (Real.exp x)) :=
  Real.tendsto_one_add_div_pow_exp x

theorem exercise04_d_positive_base (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < 1 + x / n := by
  have h : Tendsto (fun n : ℕ ↦ x / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with n hn
  linarith

end Rudin.Chapter08
