module

public import Math.Rudin.Chapter08.Exercise04
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-! # Chapter 8, Exercise 5
Source: book page 197, PDF page 206. All four printed limits use their natural domains.
-/

@[expose] public section

open Filter Topology

namespace Rudin.Chapter08

private theorem punctured_ne : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 :=
  self_mem_nhdsWithin

private theorem id_zero : Tendsto (fun x : ℝ ↦ x) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

private theorem exp_slope_limit : Tendsto (dslope Real.exp 0) (𝓝 0) (𝓝 1) := by
  simpa using (continuousAt_dslope_same.mpr (Real.differentiableAt_exp (x := 0))).tendsto

private theorem log_remainder :
    Tendsto (fun x : ℝ ↦ (Real.log (1 + x) - x) / x ^ 2) (𝓝[≠] 0) (𝓝 (-(1 / 2))) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun x ↦ 1 / (1 + x) - 1) (g' := fun x ↦ 2 * x)
  · filter_upwards [exercise04_positive_base] with x hx
    convert (((hasDerivAt_id x).const_add 1).log (ne_of_gt hx)).sub (hasDerivAt_id x) using 1
    · ext y
      simp
    · simp
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa [Pi.pow_def, id_eq] using (hasDerivAt_id x).pow 2
  · filter_upwards [punctured_ne] with x hx
    exact mul_ne_zero (by norm_num) hx
  · have h := (((tendsto_const_nhds (x := (1 : ℝ))).add id_zero).log (by norm_num)).sub id_zero
    simpa using h
  · simpa using id_zero.pow 2
  · have h : Tendsto (fun x : ℝ ↦ -(1 / (2 * (1 + x)))) (𝓝[≠] 0) (𝓝 (-(1 / 2))) := by
      convert (tendsto_const_nhds.div
        (tendsto_const_nhds.mul (tendsto_const_nhds.add id_zero)) (by norm_num : (2 : ℝ) * (1 + 0) ≠ 0)).neg using 1
      norm_num
    apply h.congr'
    filter_upwards [punctured_ne, exercise04_positive_base] with x hx hp
    field_simp
    ring

private theorem log_slope_remainder :
    Tendsto (fun x : ℝ ↦ (Real.log (1 + x) / x - 1) / x) (𝓝[≠] 0) (𝓝 (-(1 / 2))) := by
  apply log_remainder.congr'
  filter_upwards [punctured_ne] with x hx
  field_simp

theorem exercise05_a :
    Tendsto (fun x : ℝ ↦ (Real.exp 1 - (1 + x) ^ (1 / x)) / x)
      (𝓝[≠] 0) (𝓝 (Real.exp 1 / 2)) := by
  have ht : Tendsto (fun x : ℝ ↦ Real.log (1 + x) / x - 1) (𝓝[≠] 0) (𝓝 0) := by
    simpa using exercise04_b.sub_const 1
  have h := ((exp_slope_limit.comp ht).mul log_slope_remainder).const_mul (-Real.exp 1)
  have hv : -Real.exp 1 * (1 * -(1 / 2)) = Real.exp 1 / 2 := by ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [exercise04_positive_base] with x hx
  rw [Real.rpow_def_of_pos hx]
  have hs := sub_smul_dslope Real.exp 0 (Real.log (1 + x) / x - 1)
  simp only [sub_zero, smul_eq_mul, Real.exp_zero] at hs
  have he : Real.exp (Real.log (1 + x) * (1 / x)) =
      Real.exp 1 * Real.exp (Real.log (1 + x) / x - 1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  simp only [Function.comp_apply]
  linear_combination -Real.exp 1 / x * hs

theorem exercise05_b :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) / Real.log n) * ((n : ℝ) ^ (1 / (n : ℝ)) - 1))
      atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply (exp_slope_limit.comp ht).congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hn')
  have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn')
  simp only [Function.comp_apply]
  rw [dslope_of_ne _ (div_ne_zero hl hn0), slope_def_field,
    Real.rpow_def_of_pos (lt_trans (by norm_num) hn')]
  simp only [Real.exp_zero, sub_zero]
  field_simp

private theorem cosine_remainder :
    Tendsto (fun x : ℝ ↦ (1 - Real.cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := Real.sin) (g' := fun x ↦ 2 * x)
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa using (Real.hasDerivAt_cos x).const_sub 1
  · exact Filter.Eventually.of_forall fun x ↦ by simpa [Pi.pow_def, id_eq] using (hasDerivAt_id x).pow 2
  · filter_upwards [punctured_ne] with x hx
    exact mul_ne_zero (by norm_num) hx
  · simpa using (Real.continuous_cos.continuousAt.tendsto.comp id_zero).const_sub 1
  · simpa using id_zero.pow 2
  · convert Real.tendsto_sin_div_nhdsNE_zero.div_const 2 using 1
    simp [div_mul_eq_div_div, mul_comm]

private theorem sine_remainder :
    Tendsto (fun x : ℝ ↦ (x - Real.sin x) / x ^ 3) (𝓝[≠] 0) (𝓝 (1 / 6)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x ↦ 1 - Real.cos x)
    (g' := fun x ↦ 3 * x ^ 2)
  · exact Filter.Eventually.of_forall fun x ↦ (hasDerivAt_id x).sub (Real.hasDerivAt_sin x)
  · exact Filter.Eventually.of_forall fun x ↦ by simpa [Pi.pow_def, id_eq] using (hasDerivAt_id x).pow 3
  · filter_upwards [punctured_ne] with x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hx)
  · simpa using id_zero.sub (Real.continuous_sin.continuousAt.tendsto.comp id_zero)
  · simpa using id_zero.pow 3
  · convert cosine_remainder.div_const 3 using 1 <;> norm_num [div_mul_eq_div_div, mul_comm]

private theorem cosine_ne : ∀ᶠ x : ℝ in 𝓝[≠] 0, Real.cos x ≠ 0 := by
  have h := (Real.continuous_cos.continuousAt.tendsto.comp id_zero).eventually
    (eventually_ne_nhds (by norm_num : Real.cos 0 ≠ 0))
  simpa only [Function.comp_apply] using h

private theorem tangent_remainder :
    Tendsto (fun x : ℝ ↦ (Real.tan x - x) / x ^ 3) (𝓝[≠] 0) (𝓝 (1 / 3)) := by
  have h := (cosine_remainder.sub sine_remainder).div
    (Real.continuous_cos.continuousAt.tendsto.comp id_zero) (by norm_num : Real.cos 0 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [punctured_ne, cosine_ne] with x hx hc
  simp only [Pi.div_apply, Function.comp_apply]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem exercise05_c :
    Tendsto (fun x : ℝ ↦ (Real.tan x - x) / (x * (1 - Real.cos x)))
      (𝓝[≠] 0) (𝓝 (2 / 3)) := by
  have h := tangent_remainder.div cosine_remainder (by norm_num : (1 / 2 : ℝ) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [punctured_ne] with x hx
  simp only [Pi.div_apply]
  field_simp

theorem exercise05_d :
    Tendsto (fun x : ℝ ↦ (x - Real.sin x) / (Real.tan x - x))
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h := sine_remainder.div tangent_remainder (by norm_num : (1 / 3 : ℝ) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [punctured_ne] with x hx
  simp only [Pi.div_apply]
  exact div_div_div_cancel_right₀ (pow_ne_zero 3 hx) _ _

/-- No totalized logarithm, power, tangent, or quotient is needed near the limits. -/
theorem exercise05_domains :
    (∀ᶠ x : ℝ in 𝓝[≠] 0,
      x ≠ 0 ∧ 0 < 1 + x ∧ Real.cos x ≠ 0 ∧
        1 - Real.cos x ≠ 0 ∧ Real.tan x - x ≠ 0) ∧
    (∀ᶠ n : ℕ in atTop, 1 < n ∧ 0 < (n : ℝ) ∧ Real.log n ≠ 0) := by
  constructor
  · have hc := cosine_remainder.eventually (eventually_ne_nhds (by norm_num : (1 / 2 : ℝ) ≠ 0))
    have ht := tangent_remainder.eventually (eventually_ne_nhds (by norm_num : (1 / 3 : ℝ) ≠ 0))
    filter_upwards [punctured_ne, exercise04_positive_base, cosine_ne, hc, ht] with x hx hp hcos hc ht
    exact ⟨hx, hp, hcos, (div_ne_zero_iff.mp hc).1, (div_ne_zero_iff.mp ht).1⟩
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    exact ⟨hn, lt_trans (by norm_num) hn', ne_of_gt (Real.log_pos hn')⟩

end Rudin.Chapter08
