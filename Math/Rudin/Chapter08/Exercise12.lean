module

public import Math.Rudin.Chapter08.Exercise16
public import Math.Rudin.Chapter03.Exercise14

/-! # Chapter 8, Exercise 12
The periodic indicator, its Fourier coefficients, the ordered sine series,
Parseval's sine-square identity, the limiting sinc-square improper integral,
and the odd reciprocal-square sum. Source: book page 198, PDF page 207. -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Rudin.Chapter08

/-- The indicator on the source fundamental interval, before periodic extension. -/
def exercise12Indicator (δ : ℝ) : ℝ → ℂ := (Icc (-δ) δ).indicator (fun _ => 1)

lemma exercise12_integral_restrict {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) (n : ℤ) :
    (∫ x in -Real.pi..-Real.pi + 2 * Real.pi,
      fourierMonomial (-n) x * exercise12Indicator δ x) =
      ∫ x in -δ..δ, fourierMonomial (-n) x := by
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_of_le (by linarith)]
  have hf : (fun x => fourierMonomial (-n) x * exercise12Indicator δ x) =
      (Icc (-δ) δ).indicator (fourierMonomial (-n)) := by
    ext x
    by_cases hx : x ∈ Icc (-δ) δ <;> simp [exercise12Indicator, hx]
  rw [hf, setIntegral_indicator measurableSet_Icc]
  have hs : Ioc (-Real.pi) Real.pi ∩ Icc (-δ) δ = Icc (-δ) δ := by
    apply inter_eq_right.mpr
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  rw [hs, integral_Icc_eq_integral_Ioc]

theorem exercise12_coefficient_zero {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    fourierCoefficient (-Real.pi) (exercise12Indicator δ) 0 = ((δ / Real.pi : ℝ) : ℂ) := by
  unfold fourierCoefficient
  rw [exercise12_integral_restrict hδ hδπ]
  simp only [fourierMonomial, neg_zero, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero,
    intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  field_simp
  <;> ring

theorem exercise12_coefficient {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (n : ℤ) (hn : n ≠ 0) :
    fourierCoefficient (-Real.pi) (exercise12Indicator δ) n =
      ((Real.sin ((n : ℝ) * δ) / ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
  unfold fourierCoefficient
  rw [exercise12_integral_restrict hδ hδπ]
  have hne : Complex.I * (-n : ℤ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast neg_ne_zero.mpr hn)
  simp only [fourierMonomial]
  rw [integral_exp_mul_complex hne]
  change (1 / (2 * Real.pi) : ℝ) •
    ((fourierMonomial (-n) δ - fourierMonomial (-n) (-δ)) / (Complex.I * (-n : ℤ))) = _
  rw [fourierMonomial_trig, fourierMonomial_trig]
  simp only [Int.cast_neg, neg_mul, mul_neg, neg_neg, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg, Complex.real_smul]
  push_cast
  field_simp
  <;> ring

lemma exercise12_memLp (δ : ℝ) :
    MemLp (exercise12Indicator δ) 2
      (volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) := by
  apply (memLp_top_of_bound
    (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable 1 ?_).mono_exponent
      (by simp)
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Icc (-δ) δ <;> simp [exercise12Indicator, hx]

lemma exercise12_energy {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    (1 / (2 * Real.pi)) *
      (∫ x in -Real.pi..-Real.pi + 2 * Real.pi, ‖exercise12Indicator δ x‖ ^ 2) = δ / Real.pi := by
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hf : (fun x => ‖exercise12Indicator δ x‖ ^ 2) =
      (Icc (-δ) δ).indicator (fun _ => (1 : ℝ)) := by
    ext x
    by_cases hx : x ∈ Icc (-δ) δ <;> simp [exercise12Indicator, hx]
  rw [hf, he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    setIntegral_indicator measurableSet_Icc]
  have hs : Ioc (-Real.pi) Real.pi ∩ Icc (-δ) δ = Icc (-δ) δ := by
    apply inter_eq_right.mpr
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  rw [hs, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -δ ≤ δ), intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

lemma exercise12_parseval {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    HasSum (fun n : ℤ => ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) n‖ ^ 2)
      (δ / Real.pi) := by
  simpa only [exercise12_energy hδ hδπ] using
    source_parseval (-Real.pi) (exercise12_memLp δ)

lemma exercise12_coeff_norm {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) n‖ ^ 2 =
      Real.sin ((n : ℝ) * δ) ^ 2 / ((n : ℝ) ^ 2 * Real.pi ^ 2) := by
  rw [exercise12_coefficient hδ hδπ n hn, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- The sine-square identity is obtained from Parseval, not a zeta identity. -/
theorem exercise12_sine_square_sum {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    HasSum (fun n : ℕ => Real.sin (((n + 1 : ℕ) : ℝ) * δ) ^ 2 /
      (((n + 1 : ℕ) : ℝ) ^ 2 * δ)) ((Real.pi - δ) / 2) := by
  have h := (exercise12_parseval hδ hδπ).nat_add_neg
  have h0 : ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) 0‖ ^ 2 = (δ / Real.pi) ^ 2 := by
    rw [exercise12_coefficient_zero hδ hδπ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h0] at h
  have hshift : HasSum
      (fun n : ℕ => ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) (-((n + 1 : ℕ) : ℤ))‖ ^ 2)
      (δ / Real.pi - (δ / Real.pi) ^ 2) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ =>
      ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) n‖ ^ 2 +
      ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) (-n)‖ ^ 2) 1).mpr
    convert h using 1 <;> simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
      neg_zero, h0]
    ring
  have he (n : ℕ) :
      ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖fourierCoefficient (-Real.pi) (exercise12Indicator δ) (-((n + 1 : ℕ) : ℤ))‖ ^ 2 =
      2 * Real.sin (((n + 1 : ℕ) : ℝ) * δ) ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2) := by
    rw [exercise12_coeff_norm hδ hδπ (by omega), exercise12_coeff_norm hδ hδπ (by omega)]
    simp only [Int.cast_neg, neg_mul, Real.sin_neg, neg_sq, Int.cast_natCast]
    ring
  simp_rw [he] at hshift
  convert hshift.mul_left (Real.pi ^ 2 / (2 * δ)) using 1
  · ext n
    field_simp
  · field_simp
    <;> ring

theorem exercise12_odd_square_sum :
    HasSum (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
  let a : ℕ → ℝ := fun n => Real.sin ((n : ℝ) * (Real.pi / 2)) ^ 2 / (n : ℝ) ^ 2
  have htail : HasSum (fun n => a (n + 1)) (Real.pi ^ 2 / 8) := by
    have h := (exercise12_sine_square_sum (δ := Real.pi / 2)
      (by positivity) (by linarith [Real.pi_pos])).mul_right (Real.pi / 2)
    convert h using 1
    · ext n
      dsimp [a]
      field_simp
    · ring
  have ha : HasSum a (Real.pi ^ 2 / 8) := by
    have h := (hasSum_nat_add_iff (f := a) 1).mp htail
    simpa [a] using h
  have he (n : ℕ) : a (2 * n) = 0 := by
    have harg : ((2 * n : ℕ) : ℝ) * (Real.pi / 2) = n * Real.pi := by push_cast; ring
    dsimp [a]
    rw [harg, Real.sin_nat_mul_pi]
    simp
  have ho (n : ℕ) : a (2 * n + 1) = 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    have harg : ((2 * n + 1 : ℕ) : ℝ) * (Real.pi / 2) = n * Real.pi + Real.pi / 2 := by
      push_cast
      ring
    dsimp [a]
    rw [harg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    congr 1
    rw [← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow]
  have hs := ha.summable.comp_injective (i := fun n : ℕ => 2 * n + 1) (by
    intro a b h
    dsimp only at h
    omega)
  have hsum := tsum_even_add_odd
    (ha.summable.comp_injective (i := fun n : ℕ => 2 * n) (by intro a b h; dsimp only at h; omega)) hs
  simp only [he, tsum_zero, zero_add, ha.tsum_eq] at hsum
  have hh : HasSum (fun n => a (2 * n + 1)) (Real.pi ^ 2 / 8) := by
    rw [← hsum]
    exact hs.hasSum
  simpa only [ho] using hh

theorem exercise12_ordered_sine_square_sum {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, Real.sin (((n + 1 : ℕ) : ℝ) * δ) ^ 2 /
      (((n + 1 : ℕ) : ℝ) ^ 2 * δ)) atTop (𝓝 ((Real.pi - δ) / 2)) :=
  (exercise12_sine_square_sum hδ hδπ).tendsto_sum_nat

theorem exercise12_ordered_odd_square_sum :
    Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 8)) := exercise12_odd_square_sum.tendsto_sum_nat

theorem exercise12_riemann (δ : ℝ) (hδ : 0 ≤ δ) :
    RiemannIntegrableComplex (exercise12Indicator δ) (-Real.pi) Real.pi := by
  let u : ℝ → ℝ := fun x => if x ≤ δ then 1 else 0
  let v : ℝ → ℝ := fun x => if x < -δ then 1 else 0
  have hu : AntitoneOn u (Icc (-Real.pi) Real.pi) := by
    intro x hx y hy hxy
    dsimp [u]
    split_ifs <;> norm_num at * <;> linarith
  have hv : AntitoneOn v (Icc (-Real.pi) Real.pi) := by
    intro x hx y hy hxy
    dsimp [v]
    split_ifs <;> norm_num at * <;> linarith
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hu' := Rudin.Support.StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral hab
    (Rudin.Support.RiemannIntegrability.hasDarbouxRSIntegral_of_antitoneOn hab hu)
  have hv' := Rudin.Support.StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral hab
    (Rudin.Support.RiemannIntegrability.hasDarbouxRSIntegral_of_antitoneOn hab hv)
  have hsub := Rudin.Support.StieltjesIntegralLaws.hasRSIntegral_sub hu' hv'
  have he (x : ℝ) : (exercise12Indicator δ x).re = u x - v x := by
    simp only [exercise12Indicator, Set.indicator_apply, Set.mem_Icc, u, v]
    split_ifs <;> simp_all <;> linarith
  have hi (x : ℝ) : (exercise12Indicator δ x).im = 0 := by
    by_cases hx : x ∈ Icc (-δ) δ <;> simp [exercise12Indicator, hx]
  refine ⟨⟨(∫ x in -Real.pi..Real.pi, u x) - (∫ x in -Real.pi..Real.pi, v x), 0⟩,
    Rudin.Support.StieltjesComplex.hasComplexRSIntegral_iff.mpr ⟨?_, ?_⟩⟩
  · simpa only [he] using hsub
  · simp only [hi]
    simpa using Rudin.Support.StieltjesIntegralLaws.hasRSIntegral_constant hab
      (show MonotoneOn id (Icc (-Real.pi) Real.pi) from fun _ _ _ _ h => h) 0

/-- The actual `2π`-periodic indicator, including the common endpoint value zero. -/
def exercise12Periodic (δ : ℝ) (x : ℝ) : ℂ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (exercise12Indicator δ) (x : AddCircle (2 * Real.pi))

lemma exercise12_periodic (δ : ℝ) : Function.Periodic (exercise12Periodic δ) (2 * Real.pi) := by
  intro x
  simp [exercise12Periodic]

lemma exercise12_periodic_eq {δ x : ℝ} (hδπ : δ < Real.pi)
    (hx : x ∈ Icc (-Real.pi) Real.pi) : exercise12Periodic δ x = exercise12Indicator δ x := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  by_cases h : x = -Real.pi
  · subst x
    have hp := exercise12_periodic δ (-Real.pi)
    have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [he] at hp
    rw [← hp]
    have hi : Real.pi ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      constructor <;> linarith [Real.pi_pos]
    unfold exercise12Periodic
    rw [AddCircle.liftIoc_coe_apply hi]
    simp [exercise12Indicator, Set.mem_Icc, not_le.mpr hδπ,
      show ¬ -δ ≤ -Real.pi by linarith]
  · unfold exercise12Periodic
    apply AddCircle.liftIoc_coe_apply
    constructor
    · exact lt_of_le_of_ne hx.1 (Ne.symm h)
    · linarith [hx.2]

lemma exercise12_periodic_riemann {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ < Real.pi) :
    RiemannIntegrableComplex (exercise12Periodic δ) (-Real.pi) Real.pi := by
  obtain ⟨z, hz⟩ := exercise12_riemann δ hδ
  exact ⟨z, Rudin.Support.StieltjesComplex.hasComplexRSIntegral_congr hz
    (fun x hx => (exercise12_periodic_eq hδπ hx).symm)⟩

lemma exercise12_periodic_coefficient {δ : ℝ} (hδπ : δ < Real.pi) (n : ℤ) :
    fourierCoefficient (-Real.pi) (exercise12Periodic δ) n =
      fourierCoefficient (-Real.pi) (exercise12Indicator δ) n := by
  unfold fourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [exercise12_periodic_eq hδπ]
  convert hx using 1
  rw [uIcc_of_le (by linarith [Real.pi_pos])]
  congr 1
  ring

lemma exercise12_limit_at_zero {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    Tendsto (exercise12Periodic δ) (𝓝 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhds (show -δ < (0 : ℝ) by linarith) hδ] with x hx
  rw [exercise12_periodic_eq hδπ (by constructor <;> linarith [hx.1, hx.2])]
  simp [exercise12Indicator, show x ∈ Icc (-δ) δ from ⟨hx.1.le, hx.2.le⟩]

lemma exercise12_partial_zero {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) (N : ℕ) :
    fourierPartialSum (exercise12Periodic δ) N 0 =
      ((δ / Real.pi + (2 / Real.pi) * ∑ n ∈ Finset.range N,
        Real.sin (((n + 1 : ℕ) : ℝ) * δ) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold fourierPartialSum
  simp only [fourierMonomial, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  simp_rw [exercise12_periodic_coefficient hδπ]
  rw [exercise12_coefficient_zero hδ hδπ]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [exercise12_coefficient hδ hδπ _ (by omega), exercise12_coefficient hδ hδπ _ (by omega)]
  simp only [Int.cast_neg, neg_mul, Real.sin_neg, neg_div_neg_eq]
  push_cast
  field_simp
  <;> ring

theorem exercise12_sine_series {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      Real.sin (((n + 1 : ℕ) : ℝ) * δ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 ((Real.pi - δ) / 2)) := by
  let s : ℕ → ℂ := fun N => fourierPartialSum (exercise12Periodic δ) N 0
  have hs : Tendsto (Rudin.Chapter03.exercise14_mean s) atTop (𝓝 1) := by
    have h := exercise16_pointwise_fejer (exercise12_periodic δ)
      (exercise12_periodic_riemann hδ.le hδπ) 0
      ((exercise12_limit_at_zero hδ hδπ).mono_left nhdsWithin_le_nhds)
      ((exercise12_limit_at_zero hδ hδπ).mono_left nhdsWithin_le_nhds)
    convert h using 1
    · ext N
      simp only [Rudin.Chapter03.exercise14_mean, fejerMean, s, Complex.real_smul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast,
        Nat.cast_add, Nat.cast_one, one_div, Complex.ofReal_inv]
    · norm_num
  have hb : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * Rudin.Chapter03.exercise14_diff s k‖ ≤ 2 / Real.pi := by
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have he : ((n + 1 : ℕ) : ℂ) * Rudin.Chapter03.exercise14_diff s (n + 1) =
        (((2 / Real.pi) * Real.sin (((n + 1 : ℕ) : ℝ) * δ) : ℝ) : ℂ) := by
      simp only [Rudin.Chapter03.exercise14_diff, s, Nat.add_sub_cancel,
        exercise12_partial_zero hδ hδπ, Finset.sum_range_succ]
      push_cast
      field_simp
      <;> ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (div_pos (by norm_num) Real.pi_pos)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (mul_one _)
  have hconv := Rudin.Chapter03.exercise14_e_convergence hb hs
  have hreal := Complex.continuous_re.tendsto (1 : ℂ) |>.comp hconv
  have hfin := ((hreal.const_mul Real.pi).sub_const δ).div_const 2
  convert hfin using 1
  · ext N
    dsimp [s]
    rw [exercise12_partial_zero hδ hδπ, Complex.ofReal_re]
    field_simp
    <;> simp [mul_comm]
    <;> ring
  · simp

/-- Right-endpoint step samples for the limiting Riemann sums. -/
def exercise12Sample (δ x : ℝ) : ℝ := δ * ((⌊x / δ⌋₊ : ℝ) + 1)

lemma exercise12_sample_bounds {δ x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x) :
    x < exercise12Sample δ x ∧ exercise12Sample δ x ≤ x + δ := by
  have hfloor := Nat.floor_le (div_nonneg hx hδ.le)
  have hceil := Nat.lt_floor_add_one (x / δ)
  constructor
  · dsimp [exercise12Sample]
    nlinarith [(div_lt_iff₀ hδ).mp hceil]
  · dsimp [exercise12Sample]
    nlinarith [(le_div_iff₀ hδ).mp hfloor]

lemma exercise12_sample_measurable (δ : ℝ) : Measurable (exercise12Sample δ) := by
  unfold exercise12Sample
  fun_prop

lemma exercise12_sinc_dominant {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    Real.sinc y ^ 2 ≤ 4 / (x + 1) ^ 2 := by
  have hb : Real.sinc y ^ 2 ≤ 1 := by
    have h := Real.abs_sinc_le_one y
    nlinarith [sq_abs (Real.sinc y), abs_nonneg (Real.sinc y)]
  have hp : 0 < (x + 1) ^ 2 := sq_pos_of_pos (by linarith)
  apply (le_div_iff₀ hp).mpr
  by_cases hx1 : x ≤ 1
  · have hs : (x + 1) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sinc y))]
  · have hs : (x + 1) ^ 2 ≤ 4 * y ^ 2 := by nlinarith
    have ht : Real.sinc y ^ 2 * y ^ 2 ≤ 1 := by
      rw [Real.sinc_of_ne_zero hy.ne']
      have he : (Real.sin y / y) ^ 2 * y ^ 2 = Real.sin y ^ 2 := by field_simp
      rw [he]
      nlinarith [Real.abs_sin_le_one y, sq_abs (Real.sin y), abs_nonneg (Real.sin y)]
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sinc y))]

lemma exercise12_dominant_integrable :
    IntegrableOn (fun x : ℝ => 4 / (x + 1) ^ 2) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := 1)
    (by norm_num) (by norm_num)).const_mul 4
  have he : (fun x : ℝ => 4 / (x + 1) ^ 2) = (fun x : ℝ => 4 * (x + 1) ^ (-2 : ℝ)) := by
    funext x
    norm_num [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [he]
  exact h

lemma exercise12_steps_integrable {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x => Real.sinc (exercise12Sample δ x) ^ 2) (Ici 0) := by
  apply exercise12_dominant_integrable.mono'
    (((Real.continuous_sinc.measurable.comp (exercise12_sample_measurable δ)).pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact exercise12_sinc_dominant hx (exercise12_sample_bounds hδ hx).1.le
    (hx.trans_lt (exercise12_sample_bounds hδ hx).1)

lemma exercise12_cells_cover {δ : ℝ} (hδ : 0 < δ) :
    (⋃ n : ℕ, Ico ((n : ℝ) * δ) ((n + 1 : ℝ) * δ)) = Ici 0 := by
  ext x
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, hn, _⟩
    exact (mul_nonneg (Nat.cast_nonneg _) hδ.le).trans hn
  · intro hx
    refine ⟨⌊x / δ⌋₊, ?_, ?_⟩
    · exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hx hδ.le))
    · exact (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (x / δ))

lemma exercise12_cells_disjoint {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (Function.onFun Disjoint (fun n : ℕ => Ico ((n : ℝ) * δ) ((n + 1 : ℝ) * δ))) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hlt : n < m ∨ m < n := lt_or_gt_of_ne hnm
  rcases hlt with h | h
  · have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right hh hδ.le
    linarith [hx.2, hy.1]
  · have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right hh hδ.le
    linarith [hy.2, hx.1]

lemma exercise12_cell_integral {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∫ x in Ico ((n : ℝ) * δ) ((n + 1 : ℝ) * δ), Real.sinc (exercise12Sample δ x) ^ 2) =
      δ * Real.sinc ((n + 1 : ℝ) * δ) ^ 2 := by
  have he : ∀ x ∈ Ico ((n : ℝ) * δ) ((n + 1 : ℝ) * δ),
      exercise12Sample δ x = (n + 1 : ℝ) * δ := by
    intro x hx
    have hx0 : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg n) hδ.le).trans hx.1
    have hn : ⌊x / δ⌋₊ = n := (Nat.floor_eq_iff (div_nonneg hx0 hδ.le)).mpr
      ⟨(le_div_iff₀ hδ).mpr hx.1, (div_lt_iff₀ hδ).mpr hx.2⟩
    simp only [exercise12Sample, hn]
    ring
  rw [setIntegral_congr_fun measurableSet_Ico (fun x hx => congrArg (fun y => Real.sinc y ^ 2) (he x hx)),
    setIntegral_const, Real.volume_real_Ico]
  have hlen : ((n : ℝ) + 1) * δ - n * δ = δ := by ring
  rw [hlen, max_eq_left hδ.le, smul_eq_mul]

lemma exercise12_riemann_sum_hasSum {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun n : ℕ => δ * Real.sinc ((n + 1 : ℝ) * δ) ^ 2)
      (∫ x in Ici 0, Real.sinc (exercise12Sample δ x) ^ 2) := by
  have h := hasSum_integral_iUnion (μ := volume)
    (fun n : ℕ => measurableSet_Ico (a := (n : ℝ) * δ) (b := (n + 1 : ℝ) * δ))
    (exercise12_cells_disjoint hδ)
    (show IntegrableOn (fun x => Real.sinc (exercise12Sample δ x) ^ 2)
      (⋃ n : ℕ, Ico ((n : ℝ) * δ) ((n + 1 : ℝ) * δ)) by
        rw [exercise12_cells_cover hδ]
        exact exercise12_steps_integrable hδ)
  simpa only [exercise12_cell_integral hδ, exercise12_cells_cover hδ] using h

lemma exercise12_sinc_sq_integrable : IntegrableOn (fun x : ℝ => Real.sinc x ^ 2) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply (exercise12_dominant_integrable.mono_set Ioi_subset_Ici_self).mono'
    (Real.continuous_sinc.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖Real.sinc x ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact exercise12_sinc_dominant hx.le le_rfl hx

lemma exercise12_sample_limit {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => exercise12Sample (1 / (n + 1 : ℝ)) x) atTop (𝓝 x) := by
  have hb (n : ℕ) := exercise12_sample_bounds (by positivity : 0 < 1 / (n + 1 : ℝ)) hx
  have hlim := tendsto_one_div_add_atTop_nhds_zero_nat.const_add x
  rw [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (hb n).1.le) (fun n => (hb n).2)

lemma exercise12_step_integrals_limit :
    Tendsto (fun n : ℕ => ∫ x in Ici 0, Real.sinc (exercise12Sample (1 / (n + 1 : ℝ)) x) ^ 2)
      atTop (𝓝 (∫ x in Ici 0, Real.sinc x ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 4 / (x + 1) ^ 2)
    (fun n => (exercise12_steps_integrable (by positivity)).aestronglyMeasurable)
    exercise12_dominant_integrable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact exercise12_sinc_dominant hx
      (exercise12_sample_bounds (by positivity) hx).1.le
      (hx.trans_lt (exercise12_sample_bounds (by positivity) hx).1)
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact ((Real.continuous_sinc.pow 2).tendsto x).comp (exercise12_sample_limit hx)

/-- The integral of each step approximation is exactly the sum in part (c). -/
lemma exercise12_step_integral {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    (∫ x in Ici 0, Real.sinc (exercise12Sample δ x) ^ 2) = (Real.pi - δ) / 2 := by
  have h := exercise12_riemann_sum_hasSum hδ
  have he (n : ℕ) : δ * Real.sinc ((n + 1 : ℝ) * δ) ^ 2 =
      Real.sin (((n + 1 : ℕ) : ℝ) * δ) ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2 * δ) := by
    rw [Real.sinc_of_ne_zero (by positivity)]
    push_cast
    field_simp
    <;> ring
  simp_rw [he] at h
  exact h.unique (exercise12_sine_square_sum hδ hδπ)

/-- Letting the mesh tend to zero in part (c) evaluates the integral. -/
theorem exercise12_sinc_square_integral :
    (∫ x in Ici (0 : ℝ), Real.sinc x ^ 2) = Real.pi / 2 := by
  have he (n : ℕ) :
      (∫ x in Ici 0, Real.sinc (exercise12Sample (1 / (n + 1 : ℝ)) x) ^ 2) =
        (Real.pi - 1 / (n + 1 : ℝ)) / 2 := by
    apply exercise12_step_integral (by positivity)
    have hb : 1 / (n + 1 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact hb.trans_lt (by linarith [Real.pi_gt_three])
  have hlim : Tendsto (fun n : ℕ => (Real.pi - 1 / (n + 1 : ℝ)) / 2) atTop (𝓝 (Real.pi / 2)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_sub Real.pi).div_const 2
  exact tendsto_nhds_unique exercise12_step_integrals_limit (by simpa only [he] using hlim)

/-- The source improper integral exists as the limit of proper integrals. -/
theorem exercise12_sinc_square_improper :
    Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x ^ 2) atTop (𝓝 (Real.pi / 2)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (exercise12_sinc_sq_integrable.mono_set Ioi_subset_Ici_self) tendsto_id
  rw [← integral_Ici_eq_integral_Ioi, exercise12_sinc_square_integral] at h
  exact h

theorem exercise12_sinc_square_at_zero : Real.sinc 0 ^ 2 = 1 := by simp

lemma exercise12_sinc_square_riemann (A : ℝ) (hA : 0 ≤ A) :
    Rudin.Support.StieltjesPrototype.HasRSIntegral (fun x => Real.sinc x ^ 2) id 0 A
      (∫ x in 0..A, Real.sinc x ^ 2) := by
  have h := Rudin.Support.StieltjesMeasureBridge.continuous_tagged_bridge
    StieltjesFunction.id hA (f := fun x => Real.sinc x ^ 2) (by fun_prop)
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] using h


end Rudin.Chapter08
