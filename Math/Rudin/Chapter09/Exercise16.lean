module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter09

/-- The unconditional formula agrees with the source's value at zero. -/
noncomputable def exercise16F (x : ℝ) : ℝ :=
  x + 2 * x ^ 2 * Real.sin x⁻¹

theorem exercise16_source (x : ℝ) :
    exercise16F x = if x = 0 then 0 else x + 2 * x ^ 2 * Real.sin (1 / x) := by
  by_cases hx : x = 0 <;> simp [exercise16F, hx, one_div]

@[simp] theorem exercise16_zero : exercise16F 0 = 0 := by simp [exercise16F]

theorem exercise16_derivative_at_zero : HasDerivAt exercise16F 1 0 := by
  have hlim : Tendsto (fun x : ℝ => x * Real.sin x⁻¹) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (a := fun x : ℝ => |x|)
    · intro x
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
    · simpa using (continuous_abs.tendsto (0 : ℝ))
  rw [hasDerivAt_iff_tendsto_slope]
  have h : Tendsto (fun x : ℝ => 1 + 2 * (x * Real.sin x⁻¹))
      (𝓝[≠] 0) (𝓝 (1 + 2 * 0)) :=
    tendsto_const_nhds.add ((hlim.mono_left nhdsWithin_le_nhds).const_mul 2)
  apply (show Tendsto (fun x : ℝ => 1 + 2 * (x * Real.sin x⁻¹))
    (𝓝[≠] 0) (𝓝 1) by simpa using h).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  simp only [slope_def_field, sub_zero, exercise16F]
  field_simp [hx']
  ring

theorem exercise16_derivative_nonzero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt exercise16F (1 + 4 * x * Real.sin x⁻¹ - 2 * Real.cos x⁻¹) x := by
  convert (hasDerivAt_id x).add (((hasDerivAt_pow 2 x).const_mul 2).mul
    (((hasDerivAt_id x).inv hx).sin)) using 1
  · rfl
  · simp only [id_eq, Pi.inv_apply]
    field_simp [hx]
    ring

theorem exercise16_differentiable : Differentiable ℝ exercise16F := by
  intro x
  by_cases hx : x = 0
  · subst x; exact exercise16_derivative_at_zero.differentiableAt
  · exact (exercise16_derivative_nonzero hx).differentiableAt

theorem exercise16_bounded_derivative {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |deriv exercise16F x| ≤ 7 := by
  by_cases hz : x = 0
  · subst x; rw [exercise16_derivative_at_zero.deriv]; norm_num
  rw [(exercise16_derivative_nonzero hz).deriv]
  have habs : |x| ≤ 1 := (abs_le.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  calc
    |1 + 4 * x * Real.sin x⁻¹ - 2 * Real.cos x⁻¹| ≤
        |1 + 4 * x * Real.sin x⁻¹| + |2 * Real.cos x⁻¹| := abs_sub _ _
    _ ≤ |(1 : ℝ)| + |4 * x * Real.sin x⁻¹| + |2 * Real.cos x⁻¹| :=
      by gcongr; exact abs_add_le _ _
    _ ≤ 1 + 4 * 1 * 1 + 2 * 1 := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      have hs := mul_le_of_le_one_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (abs_nonneg x)) (Real.abs_sin_le_one x⁻¹)
      have hc := Real.abs_cos_le_one x⁻¹
      linarith
    _ = 7 := by norm_num

/-- Positive points tending to zero where the derivative is negative. -/
noncomputable def exercise16Point (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) * (2 * Real.pi))⁻¹

theorem exercise16Point_pos (n : ℕ) : 0 < exercise16Point n := by
  unfold exercise16Point
  positivity

theorem exercise16Point_limit : Tendsto exercise16Point atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp (tendsto_add_atTop_nat 1)).atTop_mul_const
    (by positivity : 0 < 2 * Real.pi)

theorem exercise16Point_derivative (n : ℕ) :
    deriv exercise16F (exercise16Point n) = -1 := by
  rw [(exercise16_derivative_nonzero (exercise16Point_pos n).ne').deriv]
  have hs : Real.sin ((n + 1 : ℕ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_nat_mul_two_pi_sub 0 (n + 1)
  simp only [exercise16Point, inv_inv, hs, Real.cos_nat_mul_two_pi,
    mul_zero, add_zero, mul_one]
  norm_num

theorem exercise16_not_injOn_interval {r : ℝ} (hr : 0 < r) :
    ¬InjOn exercise16F (Ioo (-r) r) := by
  intro hi
  have hc : ContinuousOn exercise16F (Ioo (-r) r) :=
    exercise16_differentiable.continuous.continuousOn
  rcases hc.strictMonoOn_of_injOn_Ioo (by linarith : -r < r) hi with hm | ha
  · have he : ∀ᶠ n in atTop, exercise16Point n ∈ Ioo (-r) r :=
      exercise16Point_limit.eventually (Ioo_mem_nhds (by linarith) hr)
    obtain ⟨n, hn⟩ := he.exists
    have hd := hm.monotoneOn.derivWithin_nonneg (x := exercise16Point n)
    rw [derivWithin_of_isOpen isOpen_Ioo hn, exercise16Point_derivative] at hd
    norm_num at hd
  · have hd := ha.antitoneOn.derivWithin_nonpos (x := (0 : ℝ))
    rw [derivWithin_of_isOpen isOpen_Ioo (show (0 : ℝ) ∈ Ioo (-r) r from
      ⟨by linarith, hr⟩), exercise16_derivative_at_zero.deriv] at hd
    norm_num at hd

/-- The invertible derivative at zero does not give local injectivity. -/
theorem exercise16_not_locally_injective {s : Set ℝ} (hs : s ∈ 𝓝 (0 : ℝ)) :
    ¬InjOn exercise16F s := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  intro hi
  apply exercise16_not_injOn_interval hr
  apply hi.mono
  intro x hx
  apply hrs
  simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using hx

end Rudin.Chapter09
