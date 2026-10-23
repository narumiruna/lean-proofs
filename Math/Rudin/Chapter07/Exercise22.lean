module

public import Math.Rudin.Chapter06.Exercise12
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib

/-! # Chapter 7, Exercise 22
Polynomial approximation in the literal raw Stieltjes squared-error integral.
The real construction uses the continuous approximants of Chapter 6, Exercise 12.
The complex construction combines real and imaginary polynomial sequences.
Source: book page 169, PDF page 178.
-/

@[expose] public section

open Set Filter Polynomial
open scoped Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesIntegralLaws
  Rudin.Support.StieltjesComposition Rudin.Support.StieltjesComplex
  Rudin.Support.StieltjesMeasureBridge

namespace Rudin.Chapter07

noncomputable section

/-- An arbitrary positive squared-error tolerance, with no nonzero-mass hypothesis. -/
theorem exercise22_approximate_real {a b ε v : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f α a b v) (hε : 0 < ε) :
    ∃ (p : ℝ[X]) (E : ℝ),
      HasRSIntegral (fun x => (f x - p.eval x) ^ 2) α a b E ∧ 0 ≤ E ∧ E < ε := by
  obtain ⟨g, A, hgc, hA, hA₀, hAε⟩ :=
    Rudin.Chapter06.exists_continuous_real_sq_error hab hf (by positivity : 0 < ε / 4)
  have hα := hf.1
  have hm : 0 ≤ α b - α a := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let δ := Real.sqrt (ε / (4 * (α b - α a + 1)))
  have hd : 0 < δ := Real.sqrt_pos.mpr (div_pos hε (by positivity))
  have hd2 : δ ^ 2 = ε / (4 * (α b - α a + 1)) :=
    Real.sq_sqrt (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b g hgc.continuousOn δ hd
  obtain ⟨G, hG⟩ := exists_hasDarbouxRSIntegral hab hα hgc.continuousOn
  obtain ⟨P, hP⟩ := exists_hasDarbouxRSIntegral hab hα p.continuous.continuousOn
  have hG' := hasRSIntegral_of_hasDarbouxRSIntegral hab hG
  have hP' := hasRSIntegral_of_hasDarbouxRSIntegral hab hP
  obtain ⟨B, hB⟩ := exists_tagged_square hab (hasRSIntegral_sub hG' hP')
  have hBbound : B ≤ δ ^ 2 * (α b - α a) := by
    apply hasRSIntegral_mono hB (hasRSIntegral_constant hab hα (δ ^ 2))
    intro x hx
    have h := (hp x hx).le
    rw [abs_sub_comm] at h
    nlinarith [sq_abs (g x - p.eval x), abs_nonneg (g x - p.eval x)]
  have hBε : B ≤ ε / 4 := by
    have hdpos : 0 < 4 * (α b - α a + 1) := by positivity
    have he : δ ^ 2 * (α b - α a) ≤ ε / 4 := by
      rw [hd2, div_mul_eq_mul_div]
      apply (div_le_iff₀ hdpos).mpr
      nlinarith
    exact hBbound.trans he
  obtain ⟨E, hE⟩ := exists_tagged_square hab (hasRSIntegral_sub hf hP')
  refine ⟨p, E, hE, hasRSIntegral_nonneg hE (fun _ _ => sq_nonneg _), ?_⟩
  have he := hasRSIntegral_mono hE
    (hasRSIntegral_add (hasRSIntegral_mul hA 2) (hasRSIntegral_mul hB 2)) (by
      intro x _
      nlinarith [sq_nonneg ((f x - g x) - (g x - p.eval x))])
  linarith

/-- The polynomials and their actual squared-error values are selected together. -/
theorem exercise22_polynomial_l2_real {a b v : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f α a b v) :
    ∃ (p : ℕ → ℝ[X]) (E : ℕ → ℝ),
      (∀ n, HasRSIntegral (fun x => (f x - (p n).eval x) ^ 2) α a b (E n)) ∧
      (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) := by
  have hex (n : ℕ) := exercise22_approximate_real hab hf
    (by positivity : 0 < 1 / (n + 1 : ℝ))
  choose p E hE hE₀ hEε using hex
  refine ⟨p, E, hE, hE₀, ?_⟩
  exact squeeze_zero hE₀ (fun n => (hEε n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- A real input has real-coefficient polynomials. -/
theorem exercise22_polynomial_l2_darboux {a b v : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasDarbouxRSIntegral f α a b v) :
    ∃ (p : ℕ → ℝ[X]) (E : ℕ → ℝ),
      (∀ n, HasDarbouxRSIntegral (fun x => (f x - (p n).eval x) ^ 2) α a b (E n)) ∧
      (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) := by
  obtain ⟨p, E, hE, hE₀, ht⟩ := exercise22_polynomial_l2_real hab
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hf)
  exact ⟨p, E, fun n => hasDarbouxRSIntegral_of_hasRSIntegral hab (hE n), hE₀, ht⟩

/-- The component polynomials combine to a genuine complex polynomial. -/
def exercise22ComplexPolynomial (p q : ℝ[X]) : ℂ[X] :=
  p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom

theorem exercise22ComplexPolynomial_eval (p q : ℝ[X]) (x : ℝ) :
    (exercise22ComplexPolynomial p q).eval (x : ℂ) =
      ((p.eval x : ℝ) : ℂ) + Complex.I * ((q.eval x : ℝ) : ℂ) := by
  simp only [exercise22ComplexPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  congr 1
  · exact Polynomial.eval_map_apply (p := p) Complex.ofRealHom x
  · congr 1
    exact Polynomial.eval_map_apply (p := q) Complex.ofRealHom x

/-- The complex source case uses complex coefficients and squared absolute errors. -/
theorem exercise22_polynomial_l2_complex {a b : ℝ} {f : ℝ → ℂ} {α : ℝ → ℝ} {v : ℂ}
    (hab : a ≤ b) (hf : HasComplexRSIntegral f α a b v) :
    ∃ (p : ℕ → ℂ[X]) (E : ℕ → ℝ),
      (∀ n, HasRSIntegral (fun x => ‖f x - (p n).eval (x : ℂ)‖ ^ 2) α a b (E n)) ∧
      (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨p, A, hA, hA₀, htA⟩ := exercise22_polynomial_l2_real hab hr
  obtain ⟨q, B, hB, hB₀, htB⟩ := exercise22_polynomial_l2_real hab hi
  refine ⟨fun n => exercise22ComplexPolynomial (p n) (q n),
    fun n => A n + B n, ?_, fun n => add_nonneg (hA₀ n) (hB₀ n), ?_⟩
  · intro n
    apply hasRSIntegral_congr (hasRSIntegral_add (hA n) (hB n))
    intro x _
    rw [exercise22ComplexPolynomial_eval, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simpa only [add_zero] using htA.add htB

end

end Rudin.Chapter07
