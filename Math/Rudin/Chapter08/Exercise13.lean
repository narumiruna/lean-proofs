module

public import Math.Rudin.Chapter08.Exercise12

/-! # Chapter 8, Exercise 13
The reciprocal-square identity is derived from Parseval for the sawtooth,
not from a precomputed zeta value. Source: book page 198, PDF page 207.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter08

open Set MeasureTheory Filter
open scoped Topology

/-- The sawtooth is the periodic extension of this function from `[0,2π)`. -/
def exercise13Sawtooth : AddCircle (2 * Real.pi) → ℂ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.liftIco (2 * Real.pi) 0 (fun x : ℝ => (x : ℂ))

theorem exercise13_coefficient_zero :
    fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) 0 = Real.pi := by
  simp only [fourierCoefficient, fourierMonomial, neg_zero, Int.cast_zero, mul_zero,
    zero_mul, Complex.exp_zero, one_mul, zero_add]
  rw [intervalIntegral.integral_ofReal, integral_id]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  <;> ring

theorem exercise13_coefficient (n : ℤ) (hn : n ≠ 0) :
    fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) n = Complex.I / n := by
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
  rw [fourierCoeffOn_of_hasDerivAt (f := fun x : ℝ => (x : ℂ))
    (f' := fun _ => (1 : ℂ)) _ hn
    (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp) intervalIntegrable_const, hc]
  simp only [zero_add, zero_sub, mul_zero, sub_zero, Complex.ofReal_zero,
    ← AddCircle.coe_zero, fourier_eval_zero, one_mul]
  push_cast
  field_simp
  simp [Complex.I_sq]

/-- The input of Parseval is verified on the actual representative. -/
theorem exercise13_memLp :
    MemLp (fun x : ℝ => (x : ℂ)) 2 (volume.restrict (Ioc 0 (0 + 2 * Real.pi))) := by
  apply (memLp_top_of_bound (by fun_prop) (2 * Real.pi) ?_).mono_exponent (by simp)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1, zero_add] using hx.2

theorem exercise13_energy :
    (1 / (2 * Real.pi)) * (∫ x in (0 : ℝ)..0 + 2 * Real.pi, ‖(x : ℂ)‖ ^ 2) =
      4 * Real.pi ^ 2 / 3 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, zero_add]
  rw [integral_pow]
  norm_num
  field_simp
  <;> ring

/-- Parseval's identity for the sawtooth with the source normalization. -/
theorem exercise13_parseval :
    HasSum (fun n : ℤ => ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) n‖ ^ 2)
      (4 * Real.pi ^ 2 / 3) := by
  simpa only [exercise13_energy] using source_parseval 0 exercise13_memLp

lemma exercise13_coeff_norm {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) n‖ ^ 2 = 1 / (n : ℝ) ^ 2 := by
  rw [exercise13_coefficient n hn, norm_div, Complex.norm_I, Complex.norm_intCast, div_pow, one_pow,
    sq_abs]

theorem exercise13_square_sum :
    HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := exercise13_parseval.nat_add_neg
  have h0 : ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) 0‖ ^ 2 = Real.pi ^ 2 := by
    rw [exercise13_coefficient_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h0] at h
  have hshift : HasSum
      (fun n : ℕ => ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) (-((n + 1 : ℕ) : ℤ))‖ ^ 2)
      (Real.pi ^ 2 / 3) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ =>
      ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) n‖ ^ 2 +
      ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) (-n)‖ ^ 2) 1).mpr
    convert h using 1 <;> simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      neg_zero, h0]
    ring
  have he (n : ℕ) :
      ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) (-((n + 1 : ℕ) : ℤ))‖ ^ 2 =
        2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [exercise13_coeff_norm (by omega), exercise13_coeff_norm (by omega)]
    push_cast
    ring
  simp_rw [he] at hshift
  convert hshift.div_const 2 using 1
  · ext n
    ring
  · ring

theorem exercise13_ordered_square_sum :
    Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6)) :=
  exercise13_square_sum.tendsto_sum_nat

lemma exercise13_periodic_value {x : ℝ} (hx : x ∈ Ico 0 (2 * Real.pi)) :
    exercise13Sawtooth (x : AddCircle (2 * Real.pi)) = (x : ℂ) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  unfold exercise13Sawtooth
  apply AddCircle.liftIco_coe_apply
  simpa using hx

lemma exercise13_periodic_coefficient (n : ℤ) :
    (haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
     fourierCoeff exercise13Sawtooth n) = fourierCoefficient 0 (fun x : ℝ => (x : ℂ)) n := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [exercise13Sawtooth, fourierCoeff_liftIco_eq, fourierCoefficient_bridge]


end Rudin.Chapter08
