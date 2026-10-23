module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Chapter 8, Exercise 22

The coefficients are the falling products divided by factorials. Convergence is
proved from the radius of convergence, including terminating series. The sum is
then differentiated term by term and identified by solving its differential equation.
-/

@[expose] public section

open Filter Topology Finset

namespace Rudin.Chapter08

noncomputable def binomialSum (a x : ℝ) : ℝ := (binomialSeries ℝ a).sum x

theorem exercise22_coefficient (a : ℝ) (n : ℕ) :
    Ring.choose a n = (∏ k ∈ range n, (a - k)) / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul]
  have hp : (descPochhammer ℤ n).smeval a = ∏ k ∈ range n, (a - k) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
        Polynomial.smeval_X, Polynomial.smeval_natCast, ih, prod_range_succ]
  rw [hp, smul_eq_mul]
  ring

private theorem binomial_mem_radius (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    x ∈ Metric.eball 0 (binomialSeries ℝ a).radius := by
  apply lt_of_lt_of_le _ (binomialSeries_radius_ge_one (a := a))
  simpa [edist_dist, Real.dist_eq, ENNReal.ofReal_lt_one] using hx

private theorem binomial_power_series (a : ℝ) :
    HasFPowerSeriesOnBall (binomialSum a) (binomialSeries ℝ a) 0
      (binomialSeries ℝ a).radius :=
  (binomialSeries ℝ a).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) binomialSeries_radius_ge_one)

theorem exercise22_hasSum (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ ↦ Ring.choose a n * x ^ n) (binomialSum a x) := by
  simpa [binomialSum, binomialSeries, FormalMultilinearSeries.ofScalars,
    mul_comm] using (binomialSeries ℝ a).hasSum (binomial_mem_radius a hx)

theorem exercise22_ordered_convergence (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N,
      ((∏ k ∈ range n, (a - k)) / (n.factorial : ℝ)) * x ^ n)
      atTop (𝓝 (binomialSum a x)) := by
  simpa only [← exercise22_coefficient] using (exercise22_hasSum a hx).tendsto_sum_nat

theorem exercise22_terminates (m n : ℕ) (hmn : m < n) :
    Ring.choose (m : ℝ) n = 0 := by
  simp [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hmn]

private theorem binomial_coefficient_recurrence (a : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * Ring.choose a (n + 1) = (a - n) * Ring.choose a n := by
  rw [exercise22_coefficient, exercise22_coefficient, prod_range_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem binomial_derivative_series (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℝ) * Ring.choose a (n + 1)) * x ^ n)
      (deriv (binomialSum a) x) := by
  have h := ((binomial_power_series a).fderiv.hasSum (binomial_mem_radius a hx))
  have h' := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasSum h
  simp only [ContinuousLinearMap.apply_apply, zero_add,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_apply,
    FormalMultilinearSeries.derivSeries_coeff_one, binomialSeries,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, fderiv_apply_one_eq_deriv] at h'
  convert h' using 1
  ext n
  ring

theorem exercise22_differentiable (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    DifferentiableAt ℝ (binomialSum a) x :=
  ((binomial_power_series a).analyticAt_of_mem (binomial_mem_radius a hx)).differentiableAt

theorem exercise22_series_ode (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    (1 + x) * deriv (binomialSum a) x = a * binomialSum a x := by
  have hd := binomial_derivative_series a hx
  have hxd : HasSum (fun n : ℕ ↦ (n : ℝ) * Ring.choose a n * x ^ n)
      (x * deriv (binomialSum a) x) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hd.mul_left x
  have h := hd.add hxd
  have he : HasSum (fun n : ℕ ↦ ((n + 1 : ℝ) * Ring.choose a (n + 1)) * x ^ n +
      (n : ℝ) * Ring.choose a n * x ^ n) (a * binomialSum a x) := by
    convert (exercise22_hasSum a hx).mul_left a using 1
    ext n
    rw [binomial_coefficient_recurrence]
    ring
  nlinarith [h.unique he]

theorem exercise22_initial_value (a : ℝ) : binomialSum a 0 = 1 := by
  exact FormalMultilinearSeries.ofScalarsSum_zero (Ring.choose a) |>.trans (by simp)

/-- The integrating factor solves the differential equation on the whole interval. -/
theorem exercise22_ode_unique (a : ℝ) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, DifferentiableAt ℝ f x)
    (hode : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, (1 + x) * deriv f x = a * f x)
    (hzero : f 0 = 1) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x = (1 + x) ^ a := by
  let g : ℝ → ℝ := fun t ↦ f t * (1 + t) ^ (-a)
  have hg : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt g 0 t := by
    intro t ht
    have htpos : 0 < 1 + t := by linarith [ht.1]
    have hp := (((hasDerivAt_id t).const_add 1).rpow_const
      (p := -a) (Or.inl htpos.ne'))
    convert (hf t ht).hasDerivAt.mul hp using 1
    · rfl
    · dsimp only [id]
      rw [Real.rpow_sub_one htpos.ne']
      have he := hode t ht
      field_simp
      rw [← he]
      ring
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
    (fun t ht ↦ (hg t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hg t ht).deriv) hx (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
  have he : f x * (1 + x) ^ (-a) = 1 := by simpa [g, hzero] using hconst
  have hxpos : 0 < 1 + x := by linarith [hx.1]
  rw [Real.rpow_neg hxpos.le, ← div_eq_mul_inv] at he
  exact (div_eq_one_iff_eq (Real.rpow_pos_of_pos hxpos a).ne').mp he

theorem exercise22_binomial_identity (a : ℝ) {x : ℝ} (hx : -1 < x ∧ x < 1) :
    binomialSum a x = (1 + x) ^ a := by
  apply exercise22_ode_unique a
    (fun t ht ↦ exercise22_differentiable a (abs_lt.mpr ht))
    (fun t ht ↦ exercise22_series_ode a (abs_lt.mpr ht)) (exercise22_initial_value a) hx

/-- Newton's formula, with the source falling-product coefficients and ordered partial sums. -/
theorem exercise22_newton (a : ℝ) {x : ℝ} (hx : -1 < x ∧ x < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ∑ n ∈ range N,
      ((∏ k ∈ range (n + 1), (a - k)) / ((n + 1).factorial : ℝ)) * x ^ (n + 1))
      atTop (𝓝 ((1 + x) ^ a)) := by
  have h := (exercise22_hasSum a (abs_lt.mpr hx))
  rw [exercise22_binomial_identity a hx] at h
  have ht := ((hasSum_nat_add_iff' 1).mpr h).tendsto_sum_nat
  simpa [← exercise22_coefficient] using ht.const_add 1

private theorem gamma_binomial_coefficient {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Ring.choose (-a) n * (-1 : ℝ) ^ n =
      Real.Gamma (n + a) / ((n.factorial : ℝ) * Real.Gamma a) := by
  induction n with
  | zero => simp [(Real.Gamma_pos_of_pos ha).ne']
  | succ n ih =>
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hg : (n : ℝ) + a ≠ 0 := by positivity
    have hr := binomial_coefficient_recurrence (-a) n
    have hΓ := Real.Gamma_add_one hg
    rw [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + a = (n + a) + 1 by ring,
      hΓ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show Ring.choose (-a) (n + 1) =
      ((-a - n) * Ring.choose (-a) n) / (n + 1) from (eq_div_iff hn).mpr (by nlinarith [hr])]
    calc
      _ = ((n : ℝ) + a) / (n + 1) * (Ring.choose (-a) n * (-1 : ℝ) ^ n) := by ring
      _ = _ := by rw [ih]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem exercise22_gamma_hasSum {a x : ℝ} (ha : 0 < a) (hx : -1 < x ∧ x < 1) :
    HasSum (fun n : ℕ ↦ Real.Gamma (n + a) * x ^ n /
      ((n.factorial : ℝ) * Real.Gamma a)) ((1 - x) ^ (-a)) := by
  have h := exercise22_hasSum (-a) (x := -x) (by simpa using abs_lt.mpr hx)
  rw [exercise22_binomial_identity (-a) (by constructor <;> linarith)] at h
  convert h using 1
  ext n
  rw [neg_eq_neg_one_mul x, mul_pow,
    show Real.Gamma (n + a) * x ^ n / ((n.factorial : ℝ) * Real.Gamma a) =
      (Real.Gamma (n + a) / ((n.factorial : ℝ) * Real.Gamma a)) * x ^ n by ring,
    ← gamma_binomial_coefficient ha]
  ring

theorem exercise22_gamma_series {a x : ℝ} (ha : 0 < a) (hx : -1 < x ∧ x < 1) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, Real.Gamma (n + a) * x ^ n /
      ((n.factorial : ℝ) * Real.Gamma a)) atTop (𝓝 ((1 - x) ^ (-a))) :=
  (exercise22_gamma_hasSum ha hx).tendsto_sum_nat

end Rudin.Chapter08
