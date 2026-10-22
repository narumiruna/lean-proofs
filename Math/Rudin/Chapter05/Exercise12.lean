module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- The first derivative, including its value at zero. -/
theorem exercise12_first_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => |t| ^ 3) (3 * |x| * x) x := by
  simpa [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_natCast] using
    (hasDerivAt_abs_rpow x (p := 3) (by norm_num))

/-- The derivative of the explicitly computed first derivative. -/
theorem exercise12_second_derivative (x : ℝ) :
    HasDerivAt (fun t : ℝ => 3 * |t| * t) (6 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · convert ((hasDerivAt_abs_neg hx).const_mul 3).mul (hasDerivAt_id x) using 1 <;> try rfl
    simp only [abs_of_neg hx, id_eq]
    ring
  · rw [hasDerivAt_iff_tendsto_slope]
    simp only [abs_zero, mul_zero]
    have h : Tendsto (fun t : ℝ => 3 * |t|) (𝓝[≠] 0) (𝓝 0) := by
      have h : ContinuousAt (fun t : ℝ => 3 * |t|) 0 := by fun_prop
      simpa using h.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 3 * |t| = slope (fun t : ℝ => 3 * |t| * t) 0 t
    simp only [slope_def_field, abs_zero, mul_zero, sub_zero]
    exact (mul_div_cancel_right₀ (3 * |t|) ht).symm
  · convert ((hasDerivAt_abs_pos hx).const_mul 3).mul (hasDerivAt_id x) using 1 <;> try rfl
    simp only [abs_of_pos hx, id_eq]
    ring

/-- Exact values of both genuine derivatives. -/
theorem exercise12_deriv_values :
    deriv (fun t : ℝ => |t| ^ 3) = (fun t => 3 * |t| * t) ∧
    deriv (deriv (fun t : ℝ => |t| ^ 3)) = (fun t => 6 * |t|) := by
  have h : deriv (fun t : ℝ => |t| ^ 3) = (fun t => 3 * |t| * t) :=
    funext (fun x => (exercise12_first_derivative x).deriv)
  exact ⟨h, by rw [h]; exact funext (fun x => (exercise12_second_derivative x).deriv)⟩

/-- The second derivative has no derivative at zero. -/
theorem exercise12_third_derivative_failure :
    ¬ DifferentiableAt ℝ (deriv (deriv (fun t : ℝ => |t| ^ 3))) 0 := by
  rw [exercise12_deriv_values.2]
  intro h
  have ha := h.const_mul (1 / 6 : ℝ)
  have he : (fun t : ℝ => (1 / 6 : ℝ) * (6 * |t|)) = abs := by
    ext t
    ring
  rw [he] at ha
  exact not_differentiableAt_abs_zero ha

end Rudin.Chapter05
