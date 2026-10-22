module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

open Filter
open scoped Topology NNReal ENNReal

namespace Rudin.Chapter03

/-- Radius of the complex power series with real coefficients `c`. -/
def exercise09_radius (c : ℕ → ℝ) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ c).radius

/-- The scalar-series radius used here is for exactly the source's terms. -/
theorem exercise09_terms (c : ℕ → ℝ) (z : ℂ) (n : ℕ) :
    FormalMultilinearSeries.ofScalars ℂ c n (fun _ => z) = (c n : ℂ) * z ^ n := by
  simp [FormalMultilinearSeries.ofScalars_apply_eq, Complex.real_smul]

/-- Part (a): radius one. -/
theorem exercise09_a : exercise09_radius (fun n => (n : ℝ) ^ 3) = 1 := by
  have ht : Tendsto (fun n : ℕ => ((n + 1 : ℝ) / n) ^ 3) atTop (𝓝 1) := by
    simpa using ((tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num)).pow 3
  have hr := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ
    (fun n => (n : ℝ) ^ 3) (by norm_num) ?_
  · simpa [exercise09_radius] using hr
  convert ht using 1
  · ext n
    simp [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), div_pow]
  · norm_num

/-- Part (b): infinite radius. -/
theorem exercise09_b :
    exercise09_radius (fun n => (2 : ℝ) ^ n / n.factorial) = ⊤ := by
  unfold exercise09_radius
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ _
    (Eventually.of_forall (fun n => by positivity))
  have ht : Tendsto (fun n : ℕ => 2 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  apply ht.congr'
  filter_upwards [] with n
  simp only [Nat.succ_eq_add_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- Part (c): radius one half. The zero coefficient at index zero only
extends the series that the source starts at index one. -/
theorem exercise09_c :
    exercise09_radius (fun n => (2 : ℝ) ^ n / (n : ℝ) ^ 2) = (2 : ℝ≥0∞)⁻¹ := by
  have hr := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 2) ℂ
    (fun n => (2 : ℝ) ^ n / (n : ℝ) ^ 2) (by norm_num) ?_
  · simpa [exercise09_radius] using hr
  have ht : Tendsto (fun n : ℕ => 2 * ((n : ℝ) / (n + 1)) ^ 2) atTop (𝓝 2) := by
    simpa using ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow 2).const_mul 2
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simp only [pow_succ]
  field_simp

/-- Part (d): radius three. -/
theorem exercise09_d :
    exercise09_radius (fun n => (n : ℝ) ^ 3 / (3 : ℝ) ^ n) = 3 := by
  unfold exercise09_radius
  apply FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (r := 3) ℂ _ (by norm_num)
  have ht : Tendsto (fun n : ℕ => 3 * ((n : ℝ) / (n + 1)) ^ 3) atTop (𝓝 3) := by
    simpa using ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow 3).const_mul 3
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  simp only [pow_succ]
  field_simp

end Rudin.Chapter03
