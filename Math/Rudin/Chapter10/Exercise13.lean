module

public import Math.Rudin.Support.MultivariateRiemann
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Chapter 10, Exercise 13 -/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise13

open Set MeasureTheory
open Rudin.Support.MultivariateRiemann

/-- The beta integral at natural exponents, including both endpoints. -/
theorem beta_natural (p q : ℕ) :
    (∫ t : ℝ in 0..1, t ^ p * (1 - t) ^ q) =
      (p.factorial : ℝ) * q.factorial / (p + q + 1).factorial := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (p : ℂ) + 1) (t := (q : ℂ) + 1) (by simp; positivity) (by simp; positivity)
  have he : (p : ℂ) + 1 + ((q : ℂ) + 1) = ((p + q + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [he, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  have hb : Complex.betaIntegral ((p : ℂ) + 1) ((q : ℂ) + 1) =
      Complex.ofReal (∫ t : ℝ in 0..1, t ^ p * (1 - t) ^ q) := by
    simp only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast]
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hb] at h
  have hr : (p.factorial : ℝ) * q.factorial =
      ((p + q + 1).factorial : ℝ) * (∫ t : ℝ in 0..1, t ^ p * (1 - t) ^ q) := by
    exact_mod_cast h
  apply (eq_div_iff (by positivity : ((p + q + 1).factorial : ℝ) ≠ 0)).mpr
  nlinarith [hr]

/-- Polynomial scaling also covers the degenerate slice of length zero. -/
theorem beta_scaled (p q : ℕ) (a : ℝ) :
    (∫ t : ℝ in 0..a, t ^ p * (a - t) ^ q) =
      a ^ (p + q + 1) * ((p.factorial : ℝ) * q.factorial / (p + q + 1).factorial) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := 0) (b := 1) (fun t : ℝ => t ^ p * (a - t) ^ q) a
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  rw [← h]
  have he : (fun t : ℝ => (a * t) ^ p * (a - a * t) ^ q) =
      fun t => a ^ (p + q) * (t ^ p * (1 - t) ^ q) := by
    funext t
    rw [show a - a * t = a * (1 - t) by ring, mul_pow, mul_pow, pow_add]
    ring
  rw [he, intervalIntegral.integral_const_mul, beta_natural, pow_succ]
  ring

/-- The monomial coefficient. -/
def monomial {n : ℕ} (r : Fin n → ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, x i ^ r i

/-- The extra exponent is the final barycentric coordinate. -/
theorem mixed_moment (n : ℕ) (r : Fin n → ℕ) (q : ℕ) :
    (∫ x in piSimplex n, monomial r x * (1 - ∑ i, x i) ^ q) =
      ((∏ i, (r i).factorial : ℝ) * q.factorial) / (n + ∑ i, r i + q).factorial := by
  induction n generalizing q with
  | zero =>
    have hs : piSimplex 0 = univ := by ext x; simp [piSimplex]
    simp [hs, monomial, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), Nat.factorial_ne_zero]
  | succ n ih =>
    rw [simplex_integral_succ (by unfold monomial; fun_prop)]
    have he (x : Fin n → ℝ) :
        (∫ t in 0..(1 - ∑ i, x i),
          monomial r (Fin.cons t x) * (1 - ∑ i, Fin.cons t x i) ^ q) =
        monomial (fun i => r i.succ) x *
          ((1 - ∑ i, x i) ^ (r 0 + q + 1) *
            ((r 0).factorial * (q.factorial : ℝ) / (r 0 + q + 1).factorial)) := by
      have hf : (fun t : ℝ => monomial r (Fin.cons t x) *
          (1 - ∑ i, Fin.cons t x i) ^ q) =
          fun t => monomial (fun i => r i.succ) x *
            (t ^ r 0 * ((1 - ∑ i, x i) - t) ^ q) := by
        funext t
        simp only [monomial, Fin.prod_univ_succ, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
        rw [show 1 - (t + ∑ i, x i) = (1 - ∑ i, x i) - t by ring]
        ring
      rw [hf, intervalIntegral.integral_const_mul, beta_scaled]
    simp_rw [he, ← mul_assoc]
    rw [integral_mul_const, ih]
    have hd : (((r 0 + q + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hs : n + ∑ i : Fin n, r i.succ + (r 0 + q + 1) =
        n + 1 + (r 0 + ∑ i : Fin n, r i.succ) + q := by omega
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
    rw [hs]
    field_simp

/-- The exact mixed-coordinate monomial integral. -/
theorem monomial_integral {n : ℕ} (r : Fin n → ℕ) :
    (∫ x in piSimplex n, monomial r x) =
      (∏ i, (r i).factorial : ℝ) / (n + ∑ i, r i).factorial := by
  simpa using mixed_moment n r 0

/-- Integrability is proved independently of the total integral's value. -/
theorem monomial_integrable {n : ℕ} (r : Fin n → ℕ) :
    IntegrableOn (monomial r) (piSimplex n) := by
  exact (show Continuous (monomial r) by unfold monomial; fun_prop).continuousOn.integrableOn_compact
    (piSimplex_isCompact n)

/-- Literal iterated one-dimensional Darboux witnesses in every coordinate order. -/
theorem monomial_source {n : ℕ} (r : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n 0 1 (simplexZeroExtension (monomial r) ∘ coordinatePermutation σ)
      ((∏ i, (r i).factorial : ℝ) / (n + ∑ i, r i).factorial) := by
  rw [← monomial_integral]
  exact (simplex_source_all_orders
    (show Continuous (monomial r) by unfold monomial; fun_prop).continuousOn σ).1

/-- A tagged multidimensional Riemann witness with the same exact value. -/
theorem monomial_riemann {n : ℕ} (r : Fin n → ℕ) :
    BoxIntegral.HasIntegral (unitBox n) BoxIntegral.IntegrationParams.Riemann
      (simplexZeroExtension (monomial r)) (volume : Measure (Fin n → ℝ)).toBoxAdditive.toSMul
      ((∏ i, (r i).factorial : ℝ) / (n + ∑ i, r i).factorial) := by
  have hc : Continuous (monomial r) := by unfold monomial; fun_prop
  rw [← monomial_integral, ← (simplex_source hc.continuousOn).2]
  exact simplex_boxIntegral hc.continuousOn

/-- Volume is the case of zero exponents, not a separate normalization assumption. -/
theorem simplex_volume (n : ℕ) : volume.real (piSimplex n) = 1 / (n.factorial : ℝ) := by
  simpa [monomial] using monomial_integral (n := n) (fun _ => 0)

end Rudin.Chapter10.Exercise13
