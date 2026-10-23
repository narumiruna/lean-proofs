module

public import Math.Rudin.Chapter08.Exercise13
public import Mathlib.NumberTheory.ZetaValues

/-! # Chapter 8, Exercise 14
The cosine expansion and reciprocal-square and reciprocal-fourth-power identities.
The fourth-power identity is derived from the computed Fourier data and Parseval.
Source: book page 199, PDF page 208. -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Rudin.Chapter08

/-- The frequency change is explicit: the period-one coordinate is `|x|/(2π)`. -/
theorem exercise14_frequency (n : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * n * (|x| / (2 * Real.pi))) = Real.cos (n * x) := by
  have he : 2 * Real.pi * n * (|x| / (2 * Real.pi)) = n * |x| := by
    field_simp
  rw [he]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, Real.cos_neg]

theorem exercise14_cosine_hasSum {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    HasSum (fun n : ℕ => 4 * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2)
      ((Real.pi - |x|) ^ 2 - Real.pi ^ 2 / 3) := by
  have hp := Real.pi_pos
  have ha : |x| ≤ Real.pi := abs_le.mpr hx
  have hy : |x| / (2 * Real.pi) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith
  have h := (hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) hy).mul_left 4
  simp only [exercise14_frequency] at h
  convert h using 1
  · ext n
    norm_num
    ring
  · norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
      Polynomial.eval_add, Polynomial.eval_monomial, bernoulli_two, bernoulli_one,
      bernoulli_zero]
    field_simp
    <;> ring

/-- The series starts at the first positive frequency; it is absolutely summable. -/
theorem exercise14_fourier_expansion {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    HasSum (fun n : ℕ => 4 * Real.cos (((n + 1 : ℕ) : ℝ) * x) /
      ((n + 1 : ℕ) : ℝ) ^ 2) ((Real.pi - |x|) ^ 2 - Real.pi ^ 2 / 3) := by
  apply (hasSum_nat_add_iff (f := fun n : ℕ =>
    4 * Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2) 1).mpr
  simpa using exercise14_cosine_hasSum hx

/-- Evaluation at zero gives the reciprocal-square identity. -/
theorem exercise14_square_sum :
    HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (exercise14_fourier_expansion (x := 0) (by
    constructor <;> linarith [Real.pi_pos])).div_const 4
  convert h using 1
  · ext n
    simp only [mul_zero, Real.cos_zero, mul_one]
    ring
  · simp only [abs_zero, sub_zero]
    ring

/-- The same periodic function represented on `[0,2π]`. -/
def exercise14Quadratic (x : ℝ) : ℂ := ((x - Real.pi) ^ 2 : ℝ)

lemma exercise14_linear_coefficient (n : ℤ) (hn : n ≠ 0) :
    fourierCoefficient 0 (fun x : ℝ => ((x - Real.pi : ℝ) : ℂ)) n = Complex.I / n := by
  have hc : fourierCoeffOn (show (0 : ℝ) < 0 + 2 * Real.pi by positivity)
      (fun _ : ℝ => (1 : ℂ)) n = 0 := by
    letI : Fact (0 < (0 + 2 * Real.pi) - 0) := ⟨by linarith [Real.pi_pos]⟩
    change fourierCoeff (fun _ : AddCircle ((0 + 2 * Real.pi) - 0) => (1 : ℂ)) n = 0
    have he : (fun _ : AddCircle ((0 + 2 * Real.pi) - 0) => (1 : ℂ)) = fourier 0 := by
      ext x
      simp
    rw [he, fourierCoeff_fourier]
    simp [hn]
  rw [← fourierCoefficient_bridge]
  rw [fourierCoeffOn_of_hasDerivAt (f := fun x : ℝ => ((x - Real.pi : ℝ) : ℂ))
    (f' := fun _ => (1 : ℂ)) _ hn
    (fun x _ => by simpa using ((hasDerivAt_id x).sub_const Real.pi).ofReal_comp)
    intervalIntegrable_const, hc]
  simp only [zero_add, mul_zero, sub_zero, Complex.ofReal_zero]
  push_cast
  field_simp
  simp [Complex.I_sq]
  <;> ring

lemma exercise14_coefficient (n : ℤ) (hn : n ≠ 0) :
    fourierCoefficient 0 exercise14Quadratic n = 2 / (n : ℂ) ^ 2 := by
  have hc : fourierCoeffOn (show (0 : ℝ) < 0 + 2 * Real.pi by positivity)
      (fun x : ℝ => 2 * ((x - Real.pi : ℝ) : ℂ)) n = 2 * (Complex.I / n) := by
    rw [fourierCoeffOn.const_mul, fourierCoefficient_bridge, exercise14_linear_coefficient n hn]
  rw [← fourierCoefficient_bridge]
  rw [fourierCoeffOn_of_hasDerivAt (f := exercise14Quadratic)
    (f' := fun x => 2 * ((x - Real.pi : ℝ) : ℂ)) _ hn
    (fun x _ => by
      change HasDerivAt (fun y : ℝ => (((y - Real.pi) ^ 2 : ℝ) : ℂ)) _ x
      convert (((hasDerivAt_id x).sub_const Real.pi).pow 2).ofReal_comp using 1 <;> simp)
    (by apply Continuous.intervalIntegrable; fun_prop), hc]
  simp only [exercise14Quadratic, zero_add]
  have he : ((2 * Real.pi - Real.pi) ^ 2 : ℝ) = (0 - Real.pi) ^ 2 := by ring
  rw [he, sub_self, mul_zero, zero_sub]
  push_cast
  field_simp
  simp [Complex.I_sq]
  <;> ring

lemma exercise14_coefficient_zero :
    fourierCoefficient 0 exercise14Quadratic 0 = ((Real.pi ^ 2 / 3 : ℝ) : ℂ) := by
  simp only [fourierCoefficient, fourierMonomial, neg_zero, Int.cast_zero, mul_zero,
    zero_mul, Complex.exp_zero, one_mul, zero_add, exercise14Quadratic]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 2),
    integral_pow]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  <;> ring

lemma exercise14_energy :
    (1 / (2 * Real.pi)) * (∫ x in (0 : ℝ)..0 + 2 * Real.pi, ‖exercise14Quadratic x‖ ^ 2) =
      Real.pi ^ 4 / 5 := by
  simp only [exercise14Quadratic, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← pow_mul,
    zero_add]
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (2 * 2)), integral_pow]
  norm_num
  field_simp
  <;> ring

lemma exercise14_memLp :
    MemLp exercise14Quadratic 2 (volume.restrict (Ioc 0 (0 + 2 * Real.pi))) := by
  apply (memLp_top_of_bound (by unfold exercise14Quadratic; fun_prop) (Real.pi ^ 2) ?_).mono_exponent
    (by simp)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simp only [exercise14Quadratic, Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs]
  nlinarith [Real.pi_pos, hx.1, hx.2]

theorem exercise14_parseval :
    HasSum (fun n : ℤ => ‖fourierCoefficient 0 exercise14Quadratic n‖ ^ 2) (Real.pi ^ 4 / 5) := by
  simpa only [exercise14_energy] using source_parseval 0 exercise14_memLp

lemma exercise14_coeff_norm {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoefficient 0 exercise14Quadratic n‖ ^ 2 = 4 / (n : ℝ) ^ 4 := by
  rw [exercise14_coefficient n hn, norm_div, norm_pow, Complex.norm_intCast, div_pow]
  norm_num
  ring

theorem exercise14_fourth_power_sum :
    HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) := by
  have h := exercise14_parseval.nat_add_neg
  have h0 : ‖fourierCoefficient 0 exercise14Quadratic 0‖ ^ 2 = Real.pi ^ 4 / 9 := by
    rw [exercise14_coefficient_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [h0] at h
  have hshift : HasSum
      (fun n : ℕ => ‖fourierCoefficient 0 exercise14Quadratic ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient 0 exercise14Quadratic (-((n + 1 : ℕ) : ℤ))‖ ^ 2)
      (4 * Real.pi ^ 4 / 45) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ =>
      ‖fourierCoefficient 0 exercise14Quadratic n‖ ^ 2 +
      ‖fourierCoefficient 0 exercise14Quadratic (-n)‖ ^ 2) 1).mpr
    convert h using 1 <;> simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      neg_zero, h0]
    ring
  have he (n : ℕ) :
      ‖fourierCoefficient 0 exercise14Quadratic ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient 0 exercise14Quadratic (-((n + 1 : ℕ) : ℤ))‖ ^ 2 =
        8 * (1 / ((n + 1 : ℕ) : ℝ) ^ 4) := by
    rw [exercise14_coeff_norm (by omega), exercise14_coeff_norm (by omega)]
    push_cast
    ring
  simp_rw [he] at hshift
  convert hshift.div_const 8 using 1
  · ext n
    ring
  · ring

theorem exercise14_ordered_fourier {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    Tendsto (fun N => Real.pi ^ 2 / 3 + ∑ n ∈ Finset.range N,
      4 * Real.cos (((n + 1 : ℕ) : ℝ) * x) / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 ((Real.pi - |x|) ^ 2)) := by
  convert (exercise14_fourier_expansion hx).tendsto_sum_nat.const_add (Real.pi ^ 2 / 3) using 1
  congr 1
  ring

theorem exercise14_ordered_square_sum :
    Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6)) := exercise14_square_sum.tendsto_sum_nat

theorem exercise14_ordered_fourth_power_sum :
    Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 4)
      atTop (𝓝 (Real.pi ^ 4 / 90)) := exercise14_fourth_power_sum.tendsto_sum_nat

/-- The periodic quadratic is exactly the source function on `[-π,π]`. -/
def exercise14Periodic : AddCircle (2 * Real.pi) → ℂ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.liftIco (2 * Real.pi) 0 exercise14Quadratic

lemma exercise14_periodic_value {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    exercise14Periodic (x : AddCircle (2 * Real.pi)) = (((Real.pi - |x|) ^ 2 : ℝ) : ℂ) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  by_cases hx0 : 0 ≤ x
  · unfold exercise14Periodic
    rw [AddCircle.liftIco_coe_apply (show x ∈ Ico 0 (0 + 2 * Real.pi) by
      constructor
      · exact hx0
      · linarith [hx.2, Real.pi_pos])]
    simp only [exercise14Quadratic, abs_of_nonneg hx0]
    congr 1
    ring
  · have hx0' : x < 0 := lt_of_not_ge hx0
    rw [← AddCircle.coe_add_period (2 * Real.pi) x]
    unfold exercise14Periodic
    rw [AddCircle.liftIco_coe_apply (show x + 2 * Real.pi ∈ Ico 0 (0 + 2 * Real.pi) by
      constructor <;> linarith [hx.1, Real.pi_pos])]
    simp only [exercise14Quadratic, abs_of_neg hx0']
    congr 1
    ring

lemma exercise14_periodic_coefficient (n : ℤ) :
    (haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
     fourierCoeff exercise14Periodic n) = fourierCoefficient 0 exercise14Quadratic n := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [exercise14Periodic, fourierCoeff_liftIco_eq, fourierCoefficient_bridge]


end Rudin.Chapter08
