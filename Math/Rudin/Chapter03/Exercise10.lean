module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Filter Set
open scoped Topology NNReal

namespace Rudin.Chapter03

/-- The radius is the usual scalar power-series radius, with values in `ℝ≥0∞`.
The library scalar series has terms `(a n : ℂ) * z^n`. -/
theorem exercise10_integer_radius (a : ℕ → ℤ)
    (ha : Set.Infinite {n | a n ≠ 0}) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius ≤ 1 := by
  by_contra! h
  have hs := (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).summable_norm_mul_pow
    (r := 1) (by simpa using h)
  have hz : Tendsto (fun n => ‖(a n : ℂ)‖) atTop (𝓝 0) := by
    simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
      using hs.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  apply ha
  apply (finite_lt_nat N).subset
  intro n hn
  by_contra! hge
  have hsmall := hN n (by simpa using hge)
  rw [Complex.norm_intCast, ← Int.cast_abs] at hsmall
  have hi : |a n| < 1 := by exact_mod_cast hsmall
  have habs := abs_nonneg (a n)
  have hzero : |a n| = 0 := by omega
  have : a n = 0 := abs_eq_zero.mp hzero
  exact hn this

end Rudin.Chapter03
