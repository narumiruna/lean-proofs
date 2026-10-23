module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Chapter 8, Exercise 18
Both functions in the source are strictly negative on `(0, π / 2)`.
-/

@[expose] public section

open Real Set

namespace Rudin.Chapter08

private theorem increasing_from_zero {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hc : ContinuousOn f (Icc 0 x))
    (hd : ∀ t ∈ Ioo 0 x, 0 < deriv f t) : f 0 < f x := by
  have hm := strictMonoOn_of_deriv_pos (convex_Icc 0 x) hc (by
    simpa only [interior_Icc] using hd)
  exact hm ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx

private theorem sin_sub_mul_cos_pos {x : ℝ} (hx : 0 < x) (hπ : x < π / 2) :
    0 < sin x - x * cos x := by
  have h := increasing_from_zero (f := fun t ↦ sin t - t * cos t) hx
    (by fun_prop) (by
      intro t ht
      have hd := (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t))
      change HasDerivAt (fun y ↦ sin y - y * cos y) _ t at hd
      rw [hd.deriv]
      dsimp only [id_eq]
      have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
      nlinarith [mul_pos ht.1 hs])
  simpa using h

private theorem rotation_aux_pos {x : ℝ} (hx : 0 < x) (hπ : x < π / 2) :
    0 < x * (1 + 2 * cos x ^ 2) - 3 * sin x * cos x := by
  have h := increasing_from_zero
    (f := fun t ↦ t * (1 + 2 * cos t ^ 2) - 3 * sin t * cos t) hx
    (by fun_prop) (by
      intro t ht
      have hd := ((hasDerivAt_id t).mul
        (((hasDerivAt_cos t).pow 2).const_mul 2 |>.const_add 1)).sub
        (((hasDerivAt_sin t).const_mul 3).mul (hasDerivAt_cos t))
      change HasDerivAt (fun y ↦ y * (1 + 2 * cos y ^ 2) - 3 * sin y * cos y) _ t at hd
      rw [hd.deriv]
      dsimp only [id_eq, Pi.pow_apply]
      norm_num only
      have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
      have hk := sin_sub_mul_cos_pos ht.1 (lt_trans ht.2 hπ)
      have ht := sin_sq_add_cos_sq t
      nlinarith [mul_pos hs hk])
  simpa using h

private theorem sinc_cube_div_cos_derivative {t : ℝ} (ht : 0 < t) (hπ : t < π / 2) :
    HasDerivAt (fun y ↦ sinc y ^ 3 / cos y)
      (sin t ^ 2 * t ^ 2 * (t * (1 + 2 * cos t ^ 2) - 3 * sin t * cos t) /
        (t ^ 3 * cos t) ^ 2) t := by
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hπ⟩
  have hd := ((hasDerivAt_sin t).pow 3).div
    (((hasDerivAt_id t).pow 3).mul (hasDerivAt_cos t)) (by
      change t ^ 3 * cos t ≠ 0
      positivity)
  have he : (fun y ↦ sinc y ^ 3 / cos y) =ᶠ[nhds t]
      (fun y ↦ sin y ^ 3 / (y ^ 3 * cos y)) := by
    filter_upwards [eventually_ne_nhds ht.ne'] with y hy
    rw [sinc_of_ne_zero hy, div_pow, div_div]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp
  have htr := sin_sq_add_cos_sq t
  congr 1
  nlinarith [congrArg (fun z : ℝ ↦ sin t ^ 2 * t ^ 3 * z) htr]

theorem exercise18_first_sign {x : ℝ} (hx : 0 < x) (hπ : x < π / 2) :
    x ^ 3 - sin x ^ 2 * tan x < 0 := by
  have hc : ∀ t ∈ Icc (0 : ℝ) x, cos t ≠ 0 := by
    intro t ht
    exact (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], lt_of_le_of_lt ht.2 hπ⟩).ne'
  have h := increasing_from_zero (f := fun t ↦ sinc t ^ 3 / cos t) hx
    ((continuous_sinc.pow 3).continuousOn.div continuous_cos.continuousOn hc) (by
      intro t ht
      rw [(sinc_cube_div_cos_derivative ht.1 (lt_trans ht.2 hπ)).deriv]
      have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
      have hh := rotation_aux_pos ht.1 (lt_trans ht.2 hπ)
      have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], lt_trans ht.2 hπ⟩
      exact div_pos (mul_pos (mul_pos (sq_pos_of_pos hs) (sq_pos_of_pos ht.1)) hh)
        (sq_pos_of_pos (mul_pos (pow_pos ht.1 3) hc)))
  have hcpos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hπ⟩
  simp only [sinc_zero, one_pow, cos_zero, div_one, sinc_of_ne_zero hx.ne', div_pow,
    div_div] at h
  have hh := (lt_div_iff₀ (show 0 < x ^ 3 * cos x by positivity)).mp h
  rw [tan_eq_sin_div_cos]
  apply (sub_neg).mpr
  rw [← mul_div_assoc, lt_div_iff₀ hcpos]
  nlinarith

theorem exercise18_second_sign {x : ℝ} (hx : 0 < x) (hπ : x < π / 2) :
    2 * x ^ 2 - sin x ^ 2 - x * tan x < 0 := by
  have hf := exercise18_first_sign hx hπ
  have hp : x ^ 4 < sin x ^ 2 * (x * tan x) := by
    nlinarith [mul_pos hx (show 0 < sin x ^ 2 * tan x - x ^ 3 by linarith)]
  have hs := sq_nonneg (sin x ^ 2 - x * tan x)
  have hn : 0 ≤ sin x ^ 2 + x * tan x := by
    have ht : 0 < tan x := tan_pos_of_pos_of_lt_pi_div_two hx hπ
    positivity
  nlinarith [sq_nonneg (sin x ^ 2 + x * tan x - 2 * x ^ 2)]

end Rudin.Chapter08
