module

public import Math.Rudin.Chapter06.Exercise02
public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComplex
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib

/-! # Chapter 7, Exercise 20
Zero moments imply zero polynomial pairings. Weierstrass approximation then
makes the square integral zero. The final statements use the source Riemann
integral and include the complex-valued case by real and imaginary parts.
Source: book page 169, PDF page 178.
-/

@[expose] public section

open Set MeasureTheory Polynomial
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesComplex
  Rudin.Support.RiemannIntegrability

namespace Rudin.Chapter07

noncomputable section

theorem exercise20_polynomial_moments {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hm : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, f x * x ^ n) = 0) (p : ℝ[X]) :
    (∫ x in (0 : ℝ)..1, f x * p.eval x) = 0 := by
  have hc (p : ℝ[X]) : ContinuousOn (fun x => f x * p.eval x) (Icc 0 1) :=
    hf.mul p.continuous.continuousOn
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, mul_add]
    rw [intervalIntegral.integral_add
      ((hc p).intervalIntegrable_of_Icc (by norm_num) (μ := volume))
      ((hc q).intervalIntegrable_of_Icc (by norm_num) (μ := volume)), hp, hq]
    simp
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    have he : (fun x => f x * (c * x ^ n)) = fun x => c * (f x * x ^ n) := by
      ext x
      ring
    rw [he, intervalIntegral.integral_const_mul, hm, mul_zero]

theorem exercise20_square_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hm : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, f x * x ^ n) = 0) :
    (∫ x in (0 : ℝ)..1, f x ^ 2) = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hM₀ : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by norm_num))
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf
    (ε / (M + 1)) (div_pos hε (by positivity))
  have hid : (∫ x in (0 : ℝ)..1, f x ^ 2) =
      ∫ x in (0 : ℝ)..1, f x * (f x - p.eval x) := by
    have he : (fun x => f x * (f x - p.eval x)) =
        fun x => f x ^ 2 - f x * p.eval x := by ext x; ring
    have hc : ContinuousOn (fun x => f x * p.eval x) (Icc 0 1) :=
      hf.mul p.continuous.continuousOn
    have hs : ContinuousOn (fun x => f x ^ 2) (Icc 0 1) := hf.pow 2
    rw [he, intervalIntegral.integral_sub
      (hs.intervalIntegrable_of_Icc (by norm_num) (μ := volume))
      (hc.intervalIntegrable_of_Icc (by norm_num) (μ := volume)),
      exercise20_polynomial_moments hf hm p, sub_zero]
  rw [hid, zero_add]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M * (ε / (M + 1)))
    (f := fun x => f x * (f x - p.eval x)) (by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        have h : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
        exact Ioc_subset_Icc_self h
      rw [norm_mul, Real.norm_eq_abs (f x - p.eval x), abs_sub_comm]
      exact mul_le_mul (hM x hx') (hp x hx').le (abs_nonneg _) hM₀)
  norm_num only [sub_zero, abs_one, mul_one] at hb
  refine hb.trans ?_
  have hh : 0 < M + 1 := by positivity
  have hq : M * (ε / (M + 1)) = ε * M / (M + 1) := by ring
  rw [hq]
  apply (div_le_iff₀ hh).mpr
  nlinarith

/-- Real source statement, including both endpoints of the interval. -/
theorem exercise20_zero_moments {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hm : ∀ n : ℕ, HasDarbouxRSIntegral (fun x => f x * x ^ n) id 0 1 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
  have hzero := exercise20_square_zero hf
    (fun n => (intervalIntegrable_and_integral_eq (by norm_num) (hm n)).2)
  have hs : ContinuousOn (fun x => f x ^ 2) (Icc 0 1) := hf.pow 2
  have hi := Rudin.Support.StieltjesMeasureBridge.continuous_bridge
    StieltjesFunction.id (by norm_num : (0 : ℝ) ≤ 1) hs
  rw [← Real.volume_eq_stieltjes_id, hzero] at hi
  have hz := Rudin.Chapter06.exercise02 (by norm_num : (0 : ℝ) < 1) (hf.pow 2)
    (fun x _ => sq_nonneg (f x)) hi
  intro x hx
  exact (sq_eq_zero_iff).mp (hz x hx)

/-- No hidden real-valued restriction: complex zero moments imply pointwise zero. -/
theorem exercise20_zero_moments_complex {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 1))
    (hm : ∀ n : ℕ, HasComplexRSIntegral (fun x => f x * (x : ℂ) ^ n) id 0 1 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
  have hr : ∀ n : ℕ, HasDarbouxRSIntegral (fun x => (f x).re * x ^ n) id 0 1 0 := by
    intro n
    have h := (hasComplexRSIntegral_iff.mp (hm n)).1
    apply hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num)
    simpa [← Complex.ofReal_pow, Complex.mul_re] using h
  have hi : ∀ n : ℕ, HasDarbouxRSIntegral (fun x => (f x).im * x ^ n) id 0 1 0 := by
    intro n
    have h := (hasComplexRSIntegral_iff.mp (hm n)).2
    apply hasDarbouxRSIntegral_of_hasRSIntegral (by norm_num)
    simpa [← Complex.ofReal_pow, Complex.mul_im] using h
  intro x hx
  apply Complex.ext
  · exact exercise20_zero_moments (Complex.continuous_re.comp_continuousOn hf) hr x hx
  · exact exercise20_zero_moments (Complex.continuous_im.comp_continuousOn hf) hi x hx

end

end Rudin.Chapter07
