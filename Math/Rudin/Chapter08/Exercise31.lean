module

public import Math.Rudin.Chapter08.Exercise30
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Math.Rudin.Support.RiemannIntegrability

/-! # Chapter 8, Exercise 31

Theorem 8.20 evaluates a beta integral at the positive arguments `n + 1, n + 1`.
An affine substitution and Gamma duplication give the required integral value.
Exercise 30 with shift `3/2` then gives the limit on positive natural indices.
The literal Darboux and tagged Riemann values agree with the interval integral.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology Real

namespace Rudin.Chapter08.Exercise31

/-- The beta integral in Theorem 8.20, specialized to the positive arguments
`n + 1, n + 1`. Both the integrability and the actual integral value are retained. -/
theorem beta_integral_nat (n : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ n * (1 - t) ^ n) volume 0 1 ∧
    (∫ t : ℝ in 0..1, t ^ n * (1 - t) ^ n) =
      Real.Gamma (n + 1) ^ 2 / Real.Gamma (2 * (n + 1)) := by
  constructor
  · exact (by fun_prop : Continuous (fun t : ℝ ↦ t ^ n * (1 - t) ^ n)).intervalIntegrable _ _
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := ((n : ℝ) + 1 : ℝ)) (t := ((n : ℝ) + 1 : ℝ)) hn hn
  have he : Complex.betaIntegral (((n : ℝ) + 1 : ℝ) : ℂ) (((n : ℝ) + 1 : ℝ) : ℂ) =
      (((∫ t : ℝ in 0..1, t ^ n * (1 - t) ^ n) : ℝ) : ℂ) := by
    simp only [Complex.betaIntegral, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    ext t
    push_cast
    rfl
  rw [he, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  have hr : Real.Gamma (n + 1) ^ 2 = Real.Gamma (2 * (n + 1)) *
      (∫ t : ℝ in 0..1, t ^ n * (1 - t) ^ n) := by
    have h' := congrArg Complex.re h
    simp only [← Complex.ofReal_mul, Complex.ofReal_re] at h'
    convert h' using 1 <;> ring_nf
  have hd : Real.Gamma (2 * (n + 1)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  exact (eq_div_iff hd).2 (by nlinarith [hr])

lemma integral_affine_beta (n : ℕ) :
    (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ n) =
      2 * 4 ^ n * (∫ t : ℝ in 0..1, t ^ n * (1 - t) ^ n) := by
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ ↦ (1 - x ^ 2) ^ n) (c := 2) (by norm_num) (-1)
  norm_num only [mul_zero, zero_add, mul_one, invOf_eq_inv, smul_eq_mul] at h
  have he : (fun t : ℝ ↦ (1 - (2 * t + -1) ^ 2) ^ n) =
      (fun t : ℝ ↦ 4 ^ n * (t ^ n * (1 - t) ^ n)) := by
    funext t
    rw [show 1 - (2 * t + -1) ^ 2 = 4 * (t * (1 - t)) by ring, mul_pow, mul_pow]
  rw [he, intervalIntegral.integral_const_mul] at h
  linarith

lemma doubling_power (n : ℕ) :
    (2 : ℝ) ^ (1 - 2 * ((n : ℝ) + 1)) = (2 * 4 ^ n)⁻¹ := by
  rw [show 1 - 2 * ((n : ℝ) + 1) = -((2 * n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_add, pow_mul]
  norm_num
  ring

/-- The actual Gamma value of the integral follows from Theorem 8.20 and
Legendre's duplication formula. All denominators are nonzero. -/
theorem integral_eq_gamma (n : ℕ) :
    (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ n) =
      Real.sqrt Real.pi * Real.Gamma (n + 1) / Real.Gamma (n + 1 + 1 / 2) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hB : Real.Gamma (2 * (n + 1)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hC : Real.Gamma (n + 1 + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hK : (2 : ℝ) * 4 ^ n ≠ 0 := by positivity
  have hdup := Real.Gamma_mul_Gamma_add_half_of_pos hn
  rw [doubling_power] at hdup
  rw [integral_affine_beta, (beta_integral_nat n).2]
  field_simp at hdup ⊢
  nlinarith [hdup]

/-- The polynomial is interval integrable, not a totalized zero integral. -/
theorem integral_integrable (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (1 - x ^ 2) ^ n) volume (-1) 1 :=
  (by fun_prop : Continuous (fun x : ℝ ↦ (1 - x ^ 2) ^ n)).intervalIntegrable _ _

/-- The value is also the literal Darboux and tagged Riemann integral. -/
theorem integral_riemann_value (n : ℕ) :
    Rudin.Support.StieltjesPrototype.HasDarbouxRSIntegral
      (fun x : ℝ ↦ (1 - x ^ 2) ^ n) id (-1) 1
      (Real.sqrt Real.pi * Real.Gamma (n + 1) / Real.Gamma (n + 1 + 1 / 2)) ∧
    Rudin.Support.StieltjesPrototype.HasRSIntegral
      (fun x : ℝ ↦ (1 - x ^ 2) ^ n) id (-1) 1
      (Real.sqrt Real.pi * Real.Gamma (n + 1) / Real.Gamma (n + 1 + 1 / 2)) := by
  have hf : ContinuousOn (fun x : ℝ ↦ (1 - x ^ 2) ^ n) (Icc (-1) 1) := by fun_prop
  have hd := Rudin.Support.StieltjesMeasureBridge.continuous_bridge
    StieltjesFunction.id (by norm_num : (-1 : ℝ) ≤ 1) hf
  have ht := Rudin.Support.StieltjesMeasureBridge.continuous_tagged_bridge
    StieltjesFunction.id (by norm_num : (-1 : ℝ) ≤ 1) hf
  have hid : (StieltjesFunction.id : ℝ → ℝ) = id := by
    funext x
    exact StieltjesFunction.id_apply x
  simpa only [← Real.volume_eq_stieltjes_id, hid, integral_eq_gamma] using And.intro hd ht

lemma scaled_integral_eq_ratio (n : ℕ) (hn : 0 < n) :
    Real.sqrt n * (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ n) =
      Real.sqrt Real.pi *
        (Real.Gamma ((n : ℝ) + 3 / 2) / ((n : ℝ) ^ (3 / 2 : ℝ) * Real.Gamma n))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [integral_eq_gamma, Real.Gamma_add_one hn0.ne', hp, inv_div]
  rw [show (n : ℝ) + 1 + 1 / 2 = n + 3 / 2 by ring]
  ring

/-- Exercise 31, first on natural indices. The preceding Gamma ratio theorem
is applied with shift `3/2`, after the integral has been evaluated using Theorem 8.20. -/
theorem exercise31_scaled_integral_limit_nat :
    Tendsto (fun n : ℕ ↦ Real.sqrt n * (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ n))
      atTop (𝓝 (Real.sqrt Real.pi)) := by
  have h := (Exercise30.exercise30_gamma_ratio (3 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi := (h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_mul (Real.sqrt Real.pi)
  simp only [inv_one, mul_one] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (scaled_integral_eq_ratio n hn).symm

/-- The source limit, indexed by positive natural numbers. -/
theorem exercise31_scaled_integral_limit :
    Tendsto (fun n : ℕ+ ↦ Real.sqrt (n : ℕ) *
      (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ (n : ℕ)))
      atTop (𝓝 (Real.sqrt Real.pi)) :=
  exercise31_scaled_integral_limit_nat.comp tendsto_PNat_val_atTop_atTop

/-- The same limit for any sequence of literal Riemann integral values.
The values are not defined by the totalized Bochner integral. -/
theorem exercise31_riemann_limit (v : ℕ+ → ℝ)
    (hv : ∀ n : ℕ+, Rudin.Support.StieltjesPrototype.HasRSIntegral
      (fun x : ℝ ↦ (1 - x ^ 2) ^ (n : ℕ)) id (-1) 1 (v n)) :
    Tendsto (fun n : ℕ+ ↦ Real.sqrt (n : ℕ) * v n)
      atTop (𝓝 (Real.sqrt Real.pi)) := by
  have he (n : ℕ+) : (∫ x : ℝ in (-1)..1, (1 - x ^ 2) ^ (n : ℕ)) = v n := by
    exact (Rudin.Support.RiemannIntegrability.intervalIntegrable_and_integral_eq
      (by norm_num : (-1 : ℝ) ≤ 1)
      (Rudin.Support.StieltjesEquivalence.hasDarbouxRSIntegral_of_hasRSIntegral
        (by norm_num : (-1 : ℝ) ≤ 1) (hv n))).2
  simpa only [he] using exercise31_scaled_integral_limit

end Rudin.Chapter08.Exercise31
