module

public import Math.Rudin.Chapter08.Exercise11
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Chapter 8, Exercise 19

Source: book page 200, PDF page 209. Geometric sums prove the claim for Fourier
monomials. Uniform bounds on the averaging operators and density of their
linear span extend the result to every continuous periodic complex function.
The source Riemann integral is constructed separately and agrees with the mean.
-/

@[expose] public section

noncomputable section
open Filter Topology MeasureTheory Finset AddCircle

namespace Rudin.Chapter08

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private abbrev PeriodCircle := AddCircle (2 * Real.pi)
private abbrev PeriodFunction := C(PeriodCircle, ℂ)

private def rotationAverage (a x : PeriodCircle) (N : ℕ) (f : PeriodFunction) : ℂ :=
  (1 / (N + 1 : ℂ)) * ∑ j ∈ range (N + 1), f (x + (j + 1) • a)

private def periodMean (f : PeriodFunction) : ℂ := ∫ t, f t ∂haarAddCircle

private theorem periodFunction_integrable (f : PeriodFunction) : Integrable f haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem periodMean_add (f g : PeriodFunction) : periodMean (f + g) = periodMean f + periodMean g :=
  integral_add (periodFunction_integrable f) (periodFunction_integrable g)

private theorem periodMean_smul (c : ℂ) (f : PeriodFunction) : periodMean (c • f) = c * periodMean f :=
  integral_const_mul c f

private theorem periodMean_norm (f : PeriodFunction) : ‖periodMean f‖ ≤ ‖f‖ := by
  simpa [periodMean] using
    norm_integral_le_of_norm_le_const (μ := haarAddCircle) (Filter.Eventually.of_forall f.norm_coe_le_norm)

private theorem rotationAverage_add (a x : PeriodCircle) (N : ℕ) (f g : PeriodFunction) :
    rotationAverage a x N (f + g) = rotationAverage a x N f + rotationAverage a x N g := by
  simp [rotationAverage, sum_add_distrib, mul_add]

private theorem rotationAverage_smul (a x : PeriodCircle) (N : ℕ) (c : ℂ) (f : PeriodFunction) :
    rotationAverage a x N (c • f) = c * rotationAverage a x N f := by
  simp [rotationAverage, ← mul_sum, mul_left_comm]

private theorem rotationAverage_norm (a x : PeriodCircle) (N : ℕ) (f : PeriodFunction) :
    ‖rotationAverage a x N f‖ ≤ ‖f‖ := by
  rw [rotationAverage, norm_mul]
  have hsum : ‖∑ j ∈ range (N + 1), f (x + (j + 1) • a)‖ ≤ (N + 1 : ℝ) * ‖f‖ := by
    calc
      _ ≤ ∑ j ∈ range (N + 1), ‖f (x + (j + 1) • a)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (N + 1), ‖f‖ := sum_le_sum fun j _ ↦ f.norm_coe_le_norm _
      _ = _ := by simp
  have hN : 0 < (N + 1 : ℝ) := by positivity
  calc
    _ ≤ ‖1 / (N + 1 : ℂ)‖ * ((N + 1 : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = _ := by
      rw [norm_div, norm_one]
      have he : ‖(N + 1 : ℂ)‖ = (N + 1 : ℝ) := by norm_cast
      rw [he]
      field_simp

private theorem rotation_error_lipschitz (a x : PeriodCircle) (N : ℕ) :
    LipschitzWith 2 (fun f : PeriodFunction ↦ rotationAverage a x N f - periodMean f) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro f g
  have ha : rotationAverage a x N (f - g) = rotationAverage a x N f - rotationAverage a x N g := by
    simp [rotationAverage, sum_sub_distrib, mul_sub]
  have hm : periodMean (f - g) = periodMean f - periodMean g :=
    integral_sub (periodFunction_integrable f) (periodFunction_integrable g)
  calc
    _ = ‖rotationAverage a x N (f - g) - periodMean (f - g)‖ := by rw [ha, hm]; congr 1; ring
    _ ≤ ‖rotationAverage a x N (f - g)‖ + ‖periodMean (f - g)‖ := norm_sub_le _ _
    _ ≤ ‖f - g‖ + ‖f - g‖ := add_le_add (rotationAverage_norm a x N _) (periodMean_norm _)
    _ = _ := by norm_num; ring

private theorem fourier_point_add (k : ℤ) (a x : PeriodCircle) :
    fourier k (a + x) = fourier k a * fourier k x := by
  simp [fourier_apply, AddCircle.toCircle_add]

private theorem fourier_point_nsmul (k : ℤ) (a : PeriodCircle) (n : ℕ) :
    fourier k (n • a) = fourier k a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, fourier_point_add, ih, pow_succ]

private theorem rotationAverage_fourier (a x : PeriodCircle) (k : ℤ) (hk : fourier k a ≠ 1) :
    Tendsto (fun N ↦ rotationAverage a x N (fourier k)) atTop (𝓝 0) := by
  have hz : ‖fourier k a‖ = 1 := by simp [fourier_apply, Circle.norm_coe]
  have hbound : IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ ↦ ‖fourier k x * fourier k a *
        ((fourier k a ^ (N + 1) - 1) / (fourier k a - 1))‖) := by
    apply isBoundedUnder_of
    refine ⟨2 / ‖fourier k a - 1‖, fun N ↦ ?_⟩
    rw [norm_mul, norm_mul, norm_div, hz]
    have hx : ‖fourier k x‖ = 1 := by simp [fourier_apply, Circle.norm_coe]
    rw [hx, one_mul, one_mul]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖fourier k a ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).zero_mul_isBoundedUnder_le hbound
  convert h using 1
  ext N
  simp only [rotationAverage, fourier_point_add, fourier_point_nsmul, pow_succ]
  rw [← mul_sum]
  simp_rw [mul_comm _ (fourier k a)]
  rw [← mul_sum, geom_sum_eq hk]
  ring

private def rotationConvergence (a x : PeriodCircle) : Submodule ℂ PeriodFunction where
  carrier := {f | Tendsto (fun N ↦ rotationAverage a x N f - periodMean f) atTop (𝓝 0)}
  zero_mem' := by simp [rotationAverage, periodMean]
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun N ↦ rotationAverage a x N (f + g) - periodMean (f + g)) atTop (𝓝 0)
    convert hf.add hg using 1
    · ext N
      rw [rotationAverage_add, periodMean_add]
      ring
    · simp
  smul_mem' := by
    intro c f hf
    change Tendsto (fun N ↦ rotationAverage a x N (c • f) - periodMean (c • f)) atTop (𝓝 0)
    convert hf.const_mul c using 1
    · ext N
      rw [rotationAverage_smul, periodMean_smul]
      ring
    · simp

private theorem rotationConvergence_closed (a x : PeriodCircle) :
    IsClosed (rotationConvergence a x : Set PeriodFunction) :=
  ((LipschitzWith.uniformEquicontinuous _ 2 (rotation_error_lipschitz a x)).equicontinuous).isClosed_setOfPred_tendsto continuous_const

private theorem mean_fourier (k : ℤ) :
    periodMean (fourier k) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) k) 0
  by_cases hk : k = 0
  · subst k
    simp [periodMean]
  · simpa [fourierCoeff, periodMean, Pi.single_apply, hk, eq_comm] using h

private theorem circle_rotation_mean (a x : PeriodCircle)
    (ha : ∀ k : ℤ, k ≠ 0 → fourier k a ≠ 1) (f : PeriodFunction) :
    Tendsto (fun N ↦ rotationAverage a x N f) atTop (𝓝 (periodMean f)) := by
  have hgen : ∀ k : ℤ, fourier k ∈ rotationConvergence a x := by
    intro k
    change Tendsto (fun N ↦ rotationAverage a x N (fourier k) - periodMean (fourier k)) atTop (𝓝 0)
    rw [mean_fourier]
    by_cases hk : k = 0
    · subst k
      have havg (N : ℕ) : rotationAverage a x N (fourier 0) = 1 := by
        have hN : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
        simp [rotationAverage, hN]
      simp only [havg, ite_true, sub_self]
      exact tendsto_const_nhds
    · simp only [hk, ite_false, sub_zero]
      exact rotationAverage_fourier a x k (ha k hk)
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi))) ≤ rotationConvergence a x :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hgen k)
  have htop := (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure_minimal
    hspan (rotationConvergence_closed a x)
  rw [span_fourier_closure_eq_top] at htop
  have hf : f ∈ rotationConvergence a x := htop (Submodule.mem_top)
  simpa using hf.add_const (periodMean f)

private theorem irrational_fourier_nonresonance {a : ℝ} (ha : Irrational (a / Real.pi))
    (k : ℤ) (hk : k ≠ 0) : fourier k (a : PeriodCircle) ≠ 1 := by
  intro he
  have hexp : Complex.exp (Complex.I * (k : ℂ) * a) = 1 := by
    convert he using 1
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
  have him := congrArg Complex.im hm
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im] at him
  norm_num at him
  apply ha.ne_rat ((2 * m : ℤ) / (k : ℚ))
  push_cast
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp
  nlinarith

theorem exercise19_irrational_rotation_mean {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) {a : ℝ} (ha : Irrational (a / Real.pi)) (x : ℝ) :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℂ)) * ∑ j ∈ range N, f (x + (j + 1 : ℕ) * a))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℝ) • ∫ t in -Real.pi..Real.pi, f t)) := by
  let F : PeriodFunction := ⟨hp.lift, by exact continuous_quot_lift _ hf⟩
  have h := circle_rotation_mean (a : PeriodCircle) (x : PeriodCircle)
    (irrational_fourier_nonresonance ha) F
  have hm : periodMean F = (1 / (2 * Real.pi) : ℝ) • ∫ t in -Real.pi..Real.pi, f t := by
    have he := fourierCoeff_eq_intervalIntegral (f := (F : PeriodCircle → ℂ)) 0 (-Real.pi)
    have hleft : fourierCoeff (F : PeriodCircle → ℂ) 0 = periodMean F := by
      simp [fourierCoeff, periodMean]
    have hF (y : ℝ) : F (y : PeriodCircle) = f y := hp.lift_coe y
    rw [hleft] at he
    simpa only [neg_zero, fourier_zero, one_smul, hF,
      show -Real.pi + 2 * Real.pi = Real.pi by ring] using he
  rw [hm] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert h using 1
  ext N
  simp only [rotationAverage, Nat.cast_add, Nat.cast_one]
  congr 1
  apply sum_congr rfl
  intro j hj
  change f (x + ((j : ℝ) + 1) * a) = hp.lift ((x : PeriodCircle) + (j + 1) • (a : PeriodCircle))
  rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_add, hp.lift_coe]
  congr 1
  simp [nsmul_eq_mul]

theorem exercise19_real {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) {a : ℝ} (ha : Irrational (a / Real.pi)) (x : ℝ) :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℝ)) * ∑ j ∈ range N, f (x + (j + 1 : ℕ) * a))
      atTop (𝓝 ((1 / (2 * Real.pi)) * ∫ t in -Real.pi..Real.pi, f t)) := by
  have h := exercise19_irrational_rotation_mean (Complex.continuous_ofReal.comp hf)
    (fun t ↦ congrArg Complex.ofReal (hp t)) ha x
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa [Function.comp_def, intervalIntegral.integral_ofReal, Complex.mul_re] using hr

theorem exercise19_riemann_integral {f : ℝ → ℂ} (hf : Continuous f) :
    Rudin.Support.StieltjesComplex.HasComplexRSIntegral f id (-Real.pi) Real.pi
      (∫ t in -Real.pi..Real.pi, f t) := by
  obtain ⟨z, hz⟩ := continuous_riemannIntegrableComplex
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hf.continuousOn
  rw [(complex_riemann_bridge (by linarith [Real.pi_pos]) hz).2]
  exact hz

end Rudin.Chapter08
