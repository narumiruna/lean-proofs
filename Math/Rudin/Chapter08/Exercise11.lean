module

public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComplex
public import Mathlib

/-! # Chapter 8, Exercise 11
The input is the literal complex tagged Riemann integral. The improper integral
is the limit of integrals on finite intervals, not a total integral used without
an integrability proof. Source: book page 198, PDF page 207.
-/

@[expose] public section

noncomputable section

namespace Rudin.Chapter08

open Set MeasureTheory Filter
open scoped Topology
open Rudin.Support.StieltjesComplex Rudin.Support.StieltjesEquivalence
open Rudin.Support.RiemannIntegrability

/-- The source Riemann predicate on a finite interval. -/
def RiemannIntegrableComplex (f : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ z, HasComplexRSIntegral f id a b z

/-- The tagged integral and the interval Bochner integral have the same value. -/
theorem complex_riemann_bridge {f : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f id a b z) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) = z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨hr, ehr⟩ := intervalIntegrable_and_integral_eq hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hr)
  obtain ⟨hi, ehi⟩ := intervalIntegrable_and_integral_eq hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hi)
  have he : f = fun x => (f x).re + (f x).im * Complex.I := by
    funext x
    exact (Complex.re_add_im (f x)).symm
  have hr' : IntervalIntegrable (fun x => ((f x).re : ℂ)) volume a b :=
    ⟨hr.1.ofReal, hr.2.ofReal⟩
  have hi' : IntervalIntegrable (fun x => ((f x).im : ℂ)) volume a b :=
    ⟨hi.1.ofReal, hi.2.ofReal⟩
  constructor
  · rw [he]
    exact hr'.add (hi'.mul_const _)
  · conv_lhs => rw [he]
    rw [intervalIntegral.integral_add hr' (hi'.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, ehr, ehi, Complex.re_add_im]

/-- Continuous complex functions have literal tagged Riemann integrals. -/
theorem continuous_riemannIntegrableComplex {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    RiemannIntegrableComplex f a b := by
  have hr := Rudin.Support.StieltjesMeasureBridge.continuous_tagged_bridge
    StieltjesFunction.id hab (Complex.continuous_re.comp_continuousOn hf)
  have hi := Rudin.Support.StieltjesMeasureBridge.continuous_tagged_bridge
    StieltjesFunction.id hab (Complex.continuous_im.comp_continuousOn hf)
  exact ⟨⟨_, _⟩, hasComplexRSIntegral_iff.mpr ⟨hr, hi⟩⟩

/-- Each truncated Laplace integral is also a source Riemann integral. -/
theorem exercise11_truncated_riemann {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A) (t : ℝ) {A : ℝ} (hA : 0 < A) :
    HasComplexRSIntegral (fun x => Real.exp (-t * x) • f x) id 0 A
      (∫ x in 0..A, Real.exp (-t * x) • f x) := by
  obtain ⟨z, hz⟩ := hf A hA
  obtain ⟨w, hw⟩ := continuous_riemannIntegrableComplex hA.le
    (f := fun x => (Real.exp (-t * x) : ℂ)) (by fun_prop)
  obtain ⟨v, hv⟩ := exists_product hA.le hw hz
  have he : (fun x => (Real.exp (-t * x) : ℂ) * f x) =
      (fun x => Real.exp (-t * x) • f x) := by
    ext x
    exact Complex.real_smul.symm
  rw [he] at hv
  rw [(complex_riemann_bridge hA.le hv).2]
  exact hv

/-- Riemann integrability supplies measurability; it is not an extra hypothesis. -/
theorem exercise11_measurable {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A) :
    AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  have hs : (Ioi (0 : ℝ)) = ⋃ n : ℕ, Ioc 0 (n + 1 : ℝ) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, hx, by linarith⟩
    · rintro ⟨n, hn, _⟩
      exact hn
  rw [hs, aestronglyMeasurable_iUnion_iff]
  intro n
  obtain ⟨z, hz⟩ := hf (n + 1) (by positivity)
  exact ((complex_riemann_bridge (by positivity) hz).1.1).aestronglyMeasurable

/-- Local source boundedness and the limit give a bound on the whole half-line. -/
theorem exercise11_bounded {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A)
    (hlim : Tendsto f atTop (𝓝 1)) :
    ∃ M : ℝ, ∀ x ∈ Ici 0, ‖f x‖ ≤ M := by
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp hlim) 1 zero_lt_one
  obtain ⟨z, hz⟩ := hf (max A 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  obtain ⟨M, hM⟩ := hz.2.1
  refine ⟨max M 2, fun x hx => ?_⟩
  by_cases h : x ≤ max A 1
  · exact (hM x ⟨hx, h⟩).trans (le_max_left _ _)
  · have hd := hA x ((le_max_left A 1).trans (le_of_not_ge h))
    have hn := norm_add_le (f x - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hn
    rw [dist_eq_norm] at hd
    exact (show ‖f x‖ ≤ 2 by linarith).trans (le_max_right _ _)

/-- Absolute integrability of the Laplace integrand for each positive parameter. -/
theorem exercise11_laplace_integrable {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A)
    (hlim : Tendsto f atTop (𝓝 1)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => Real.exp (-t * x) • f x) (Ioi 0) := by
  obtain ⟨M, hM⟩ := exercise11_bounded hf hlim
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 0).mul_const M).mono'
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-t * x))).aestronglyMeasurable.smul
      (exercise11_measurable hf)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hM x hx.le) (Real.exp_pos _).le

/-- Existence of the actual improper integral as a limit of finite integrals. -/
theorem exercise11_improper_integral {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A)
    (hlim : Tendsto f atTop (𝓝 1)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun A => ∫ x in 0..A, Real.exp (-t * x) • f x) atTop
      (𝓝 (∫ x in Ioi 0, Real.exp (-t * x) • f x)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (exercise11_laplace_integrable hf hlim ht) tendsto_id

/-- Substitution in the actual Laplace integral. -/
theorem exercise11_change_variable (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    t • (∫ x in Ioi 0, Real.exp (-t * x) • f x) =
      ∫ y in Ioi 0, Real.exp (-y) • f (y / t) := by
  have h := integral_comp_mul_left_Ioi'
    (fun y => Real.exp (-y) • f (y / t)) 0 ht
  simpa only [mul_zero, neg_mul, mul_div_cancel_left₀ _ ht.ne'] using h

/-- The Abelian limit, for complex as well as real source functions. -/
theorem exercise11_abelian_limit {f : ℝ → ℂ}
    (hf : ∀ A > 0, RiemannIntegrableComplex f 0 A)
    (hlim : Tendsto f atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => t • (∫ x in Ioi 0, Real.exp (-t * x) • f x))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨M, hM⟩ := exercise11_bounded hf hlim
  have hi (t : ℝ) (ht : 0 < t) :
      IntegrableOn (fun y => Real.exp (-y) • f (y / t)) (Ioi 0) := by
    have hh := (integrableOn_Ioi_comp_mul_left_iff
      (fun x => Real.exp (-t * x) • f x) 0 (inv_pos.mpr ht)).mpr
      (by simpa using exercise11_laplace_integrable hf hlim ht)
    convert hh using 1
    ext y
    congr 2
    · field_simp
    · ring
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (Ioi 0))
    (F := fun t y => Real.exp (-y) • f (y / t))
    (f := fun y => Real.exp (-y) • (1 : ℂ)) (fun y => Real.exp (-y) * M)
    (by filter_upwards [self_mem_nhdsWithin] with t ht; exact (hi t ht).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hM (y / t) (le_of_lt (div_pos hy ht)))
        (Real.exp_pos _).le)
    ((integrableOn_exp_neg_Ioi 0).mul_const M)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      apply Tendsto.const_smul
      apply hlim.comp
      change Tendsto (fun t : ℝ => y / t) (𝓝[>] 0) atTop
      simpa only [div_eq_mul_inv] using
        (tendsto_const_mul_atTop_of_pos hy).mpr tendsto_inv_nhdsGT_zero)
  have he : (∫ y in Ioi (0 : ℝ), Real.exp (-y) • (1 : ℂ)) = 1 := by
    rw [integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]
  rw [he] at hconv
  apply hconv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (exercise11_change_variable f ht).symm

end Rudin.Chapter08
