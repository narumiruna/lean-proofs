module

public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter05

/-- The quadratic difference bound gives a genuine derivative, equal to zero. -/
theorem exercise01_hasDerivAt (f : ℝ → ℝ)
    (h : ∀ x y, |f x - f y| ≤ (x - y) ^ 2) (x : ℝ) :
    HasDerivAt f 0 x := by
  rw [hasDerivAt_iff_tendsto]
  simp only [smul_zero, sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun y => mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _))
  · intro y
    calc
      |y - x|⁻¹ * |f y - f x| ≤ |y - x|⁻¹ * (y - x) ^ 2 :=
        mul_le_mul_of_nonneg_left (h y x) (inv_nonneg.mpr (abs_nonneg _))
      _ ≤ |y - x| := by
        by_cases hy : y - x = 0
        · simp [hy]
        · rw [← sq_abs, pow_two, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hy), one_mul]
  · simpa using ((tendsto_id.sub_const x).abs :
      Tendsto (fun y : ℝ => |y - x|) (𝓝 x) (𝓝 |x - x|))

/-- Exercise 1: a real function with this quadratic difference bound is constant. -/
theorem exercise01_constant (f : ℝ → ℝ)
    (h : ∀ x y, |f x - f y| ≤ (x - y) ^ 2) : ∀ x y, f x = f y := by
  exact is_const_of_deriv_eq_zero
    (fun x => (exercise01_hasDerivAt f h x).differentiableAt)
    (fun x => (exercise01_hasDerivAt f h x).deriv)

end Rudin.Chapter05
