module

public import Math.Rudin.Chapter08.Exercise25
public import Mathlib.Analysis.Fourier.AddCircle

/-! # Chapter 8, Exercise 26

The index is constructed from actual finite trigonometric sums. Density is
used only to produce these sums; the index is their integral index, not an
independent topological definition.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace Rudin.Chapter08

/-- A trigonometric polynomial, with finitely supported complex coefficients
and both positive and negative integer frequencies. -/
abbrev IndexTrigPolynomial := ℤ →₀ ℂ

namespace IndexTrigPolynomial

noncomputable def eval (P : IndexTrigPolynomial) (t : ℝ) : ℂ :=
  P.sum fun n c ↦ c * Complex.exp (Complex.I * n * t)

noncomputable def velocity (P : IndexTrigPolynomial) (t : ℝ) : ℂ :=
  P.sum fun n c ↦ c * (Complex.exp (Complex.I * n * t) * (Complex.I * n))

theorem hasDerivAt (P : IndexTrigPolynomial) (t : ℝ) :
    HasDerivAt P.eval (P.velocity t) t := by
  unfold eval velocity Finsupp.sum
  apply HasDerivAt.fun_sum
  intro n hn
  convert (((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * n)).cexp.const_mul
    (P n)) using 1 <;> simp

theorem continuous (P : IndexTrigPolynomial) : Continuous P.eval :=
  continuous_iff_continuousAt.mpr fun t ↦ (P.hasDerivAt t).continuousAt

theorem continuous_velocity (P : IndexTrigPolynomial) : Continuous P.velocity := by
  unfold velocity Finsupp.sum
  fun_prop

theorem closed (P : IndexTrigPolynomial) : P.eval 0 = P.eval (2 * Real.pi) := by
  unfold eval Finsupp.sum
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun z : ℂ ↦ P n * z) (exercise23_circle n).1.closed

theorem isLoop (P : IndexTrigPolynomial)
    (h : ∀ t ∈ Icc 0 (2 * Real.pi), P.eval t ≠ 0) :
    IsC1NonzeroLoop P.eval P.velocity 0 (2 * Real.pi) :=
  ⟨by positivity, P.closed, fun t _ ↦ (P.hasDerivAt t).hasDerivWithinAt,
    P.continuous_velocity.continuousOn, h⟩

end IndexTrigPolynomial

private theorem fourier_two_pi (n : ℤ) (t : ℝ) :
    fourier n (t : AddCircle (2 * Real.pi)) = Complex.exp (Complex.I * n * t) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- The density theorem produces actual finite trigonometric polynomials
uniformly close on the whole closed interval, including its identified endpoints. -/
theorem exercise26_trigonometric_approximation {γ : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc 0 (2 * Real.pi))) (hclosed : γ 0 = γ (2 * Real.pi))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : IndexTrigPolynomial, ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < ε := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let G : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIco (2 * Real.pi) 0 γ, AddCircle.liftIco_zero_continuous hclosed hc⟩
  have hG : ∀ t ∈ Icc 0 (2 * Real.pi), G (t : AddCircle (2 * Real.pi)) = γ t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, hlt⟩
    · change AddCircle.liftIco (2 * Real.pi) 0 γ (↑(2 * Real.pi)) = _
      rw [AddCircle.coe_period]
      rw [← hclosed]
      exact AddCircle.liftIco_zero_coe_apply (by constructor <;> positivity)
  have hg : G ∈ (Submodule.span ℂ (range (@fourier (2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.mp hg ε hε
  obtain ⟨P, hP⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hQ
  refine ⟨P, fun t ht ↦ ?_⟩
  have he : IndexTrigPolynomial.eval P t = Q (t : AddCircle (2 * Real.pi)) := by
    rw [← hP]
    simp only [IndexTrigPolynomial.eval, Finsupp.sum, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul, fourier_two_pi]
  rw [he, ← hG t ht]
  exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (Q - G) (t : AddCircle (2 * Real.pi))) (by simpa [dist_eq_norm, norm_sub_rev] using hdist)

/-- The continuous-curve hypotheses, without any derivative assumption. -/
structure IsContinuousNonzeroLoop (γ : ℝ → ℂ) : Prop where
  continuous : ContinuousOn γ (Icc 0 (2 * Real.pi))
  closed : γ 0 = γ (2 * Real.pi)
  nonzero : ∀ t ∈ Icc 0 (2 * Real.pi), γ t ≠ 0

/-- A positive continuous function on the parameter interval has a strictly
positive uniform lower bound. -/
theorem index_positive_lower_bound {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 (2 * Real.pi)))
    (hp : ∀ t ∈ Icc 0 (2 * Real.pi), 0 < f t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 (2 * Real.pi), δ < f t := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) (2 * Real.pi)).Nonempty from ⟨0, by constructor <;> positivity⟩) hc
  have hpos := hp t ht
  refine ⟨f t / 2, by positivity, fun u hu ↦ ?_⟩
  have hm : f t ≤ f u := hmin hu
  linarith

namespace IsContinuousNonzeroLoop

variable {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ)
include h

theorem lower_bound : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 (2 * Real.pi), δ < ‖γ t‖ :=
  index_positive_lower_bound h.continuous.norm (fun t ht ↦ norm_pos_iff.mpr (h.nonzero t ht))

/-- The actual source construction: an admissible `δ` and a nonzero closed
trigonometric polynomial within `δ/4` throughout the interval. -/
theorem approximants : ∃ δ : ℝ, 0 < δ ∧
    (∀ t ∈ Icc 0 (2 * Real.pi), δ < ‖γ t‖) ∧
    ∃ P : IndexTrigPolynomial,
      (∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < δ / 4) ∧
      IsC1NonzeroLoop P.eval P.velocity 0 (2 * Real.pi) := by
  obtain ⟨δ, hδ, hlower⟩ := h.lower_bound
  obtain ⟨P, hP⟩ := exercise26_trigonometric_approximation h.continuous h.closed
    (show 0 < δ / 4 by positivity)
  refine ⟨δ, hδ, hlower, P, hP, P.isLoop ?_⟩
  intro t ht hz
  have hpt := hP t ht
  rw [hz, zero_sub, norm_neg] at hpt
  have := hlower t ht
  linarith

/-- Arbitrarily close polynomials can also satisfy the relative quarter-norm
bound used to compare indices. -/
theorem close_polynomial {ε : ℝ} (hε : 0 < ε) :
    ∃ P : IndexTrigPolynomial, ∀ t ∈ Icc 0 (2 * Real.pi),
      ‖P.eval t - γ t‖ < ε ∧ ‖P.eval t - γ t‖ < ‖γ t‖ / 4 := by
  obtain ⟨δ, hδ, hlower⟩ := h.lower_bound
  obtain ⟨P, hP⟩ := exercise26_trigonometric_approximation h.continuous h.closed
    (show 0 < min ε (δ / 4) by positivity)
  refine ⟨P, fun t ht ↦ ?_⟩
  have hp := hP t ht
  rw [lt_min_iff] at hp
  exact ⟨hp.1, hp.2.trans (by linarith [hlower t ht])⟩

theorem small_polynomial : ∃ P : IndexTrigPolynomial,
    ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < ‖γ t‖ / 4 := by
  obtain ⟨P, hP⟩ := h.close_polynomial zero_lt_one
  exact ⟨P, fun t ht ↦ (hP t ht).2⟩

end IsContinuousNonzeroLoop

/-- A relative quarter-norm approximation is nonzero. -/
theorem index_close_nonzero {z w : ℂ} (h : ‖w - z‖ < ‖z‖ / 4) : w ≠ 0 := by
  intro hw
  rw [hw, zero_sub, norm_neg] at h
  have := norm_nonneg z
  linarith

/-- Two quarter-norm approximations satisfy the strict perturbation bound
from Exercise 25, even when their original admissible deltas differ. -/
theorem index_close_pair {z p q : ℂ}
    (hp : ‖p - z‖ < ‖z‖ / 4) (hq : ‖q - z‖ < ‖z‖ / 4) :
    ‖p - q‖ < ‖p‖ := by
  have ht := dist_triangle p z q
  have hz := dist_triangle z p 0
  simp only [dist_eq_norm, sub_zero, norm_sub_rev z p, norm_sub_rev z q] at ht hz
  linarith [norm_nonneg z]

noncomputable def indexPolynomial (γ : ℝ → ℂ) (h : IsContinuousNonzeroLoop γ) :
    IndexTrigPolynomial := Classical.choose h.small_polynomial

theorem indexPolynomial_close {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ) :
    ∀ t ∈ Icc 0 (2 * Real.pi),
      ‖(indexPolynomial γ h).eval t - γ t‖ < ‖γ t‖ / 4 :=
  Classical.choose_spec h.small_polynomial

theorem indexPolynomial_isLoop {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ) :
    IsC1NonzeroLoop (indexPolynomial γ h).eval (indexPolynomial γ h).velocity
      0 (2 * Real.pi) :=
  (indexPolynomial γ h).isLoop fun t ht ↦ index_close_nonzero (indexPolynomial_close h t ht)

/-- The continuous index is the integer supplied by the integral index of a
chosen close trigonometric polynomial. -/
noncomputable def continuousCurveIndex (γ : ℝ → ℂ) (h : IsContinuousNonzeroLoop γ) : ℤ :=
  Classical.choose (exercise23_integer_index (indexPolynomial_isLoop h))

theorem continuousCurveIndex_spec {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ) :
    (continuousCurveIndex γ h : ℂ) = curveIndex
      (indexPolynomial γ h).eval (indexPolynomial γ h).velocity 0 (2 * Real.pi) :=
  (Classical.choose_spec (exercise23_integer_index (indexPolynomial_isLoop h))).symm

/-- Any close smooth curve, not only the chosen polynomial, computes the
same index. -/
theorem continuousCurveIndex_eq_smooth {γ σ v : ℝ → ℂ}
    (h : IsContinuousNonzeroLoop γ) (hs : IsC1NonzeroLoop σ v 0 (2 * Real.pi))
    (hclose : ∀ t ∈ Icc 0 (2 * Real.pi), ‖σ t - γ t‖ < ‖γ t‖ / 4) :
    (continuousCurveIndex γ h : ℂ) = curveIndex σ v 0 (2 * Real.pi) := by
  rw [continuousCurveIndex_spec]
  exact exercise25_index_stability (indexPolynomial_isLoop h) hs
    (fun t ht ↦ index_close_pair (indexPolynomial_close h t ht) (hclose t ht))

/-- Every admissible delta and every corresponding polynomial give the
constructed index. This proves independence of both choices. -/
theorem exercise26_approximant_index {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ)
    {δ : ℝ} (hlower : ∀ t ∈ Icc 0 (2 * Real.pi), δ < ‖γ t‖)
    (P : IndexTrigPolynomial)
    (hP : ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < δ / 4) :
    (continuousCurveIndex γ h : ℂ) = curveIndex P.eval P.velocity 0 (2 * Real.pi) := by
  have hsmall : ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < ‖γ t‖ / 4 := by
    intro t ht
    linarith [hP t ht, hlower t ht]
  exact continuousCurveIndex_eq_smooth h
    (P.isLoop fun t ht ↦ index_close_nonzero (hsmall t ht)) hsmall

/-- In particular, two source approximants, with possibly different
admissible deltas, have equal integral indices. -/
theorem exercise26_independence {γ : ℝ → ℂ} (h : IsContinuousNonzeroLoop γ)
    {δ ε : ℝ}
    (hδ : ∀ t ∈ Icc 0 (2 * Real.pi), δ < ‖γ t‖)
    (hε : ∀ t ∈ Icc 0 (2 * Real.pi), ε < ‖γ t‖)
    (P Q : IndexTrigPolynomial)
    (hP : ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - γ t‖ < δ / 4)
    (hQ : ∀ t ∈ Icc 0 (2 * Real.pi), ‖Q.eval t - γ t‖ < ε / 4) :
    curveIndex P.eval P.velocity 0 (2 * Real.pi) =
      curveIndex Q.eval Q.velocity 0 (2 * Real.pi) :=
  (exercise26_approximant_index h hδ P hP).symm.trans
    (exercise26_approximant_index h hε Q hQ)

/-- The construction agrees with the integral whenever the original curve
has the required continuous within derivative. -/
theorem exercise26_smooth_agreement {γ v : ℝ → ℂ}
    (h : IsContinuousNonzeroLoop γ) (hs : IsC1NonzeroLoop γ v 0 (2 * Real.pi)) :
    (continuousCurveIndex γ h : ℂ) = curveIndex γ v 0 (2 * Real.pi) := by
  apply continuousCurveIndex_eq_smooth h hs
  intro t ht
  rw [sub_self, norm_zero]
  exact div_pos (norm_pos_iff.mpr (h.nonzero t ht)) (by norm_num)

/-- Exercise 24 remains true for continuous curves. Compactness gives a
uniform neighborhood of the range contained in the slit plane; an actual
polynomial approximation can be chosen inside that neighborhood. -/
theorem exercise26_negative_axis_extension {γ : ℝ → ℂ}
    (h : IsContinuousNonzeroLoop γ)
    (haxis : ∀ t ∈ Icc 0 (2 * Real.pi), γ t ∈ Complex.slitPlane) :
    continuousCurveIndex γ h = 0 := by
  obtain ⟨ε, hε, heps⟩ :=
    (isCompact_Icc.image_of_continuousOn h.continuous).exists_thickening_subset_open
      Complex.isOpen_slitPlane (by rintro _ ⟨t, ht, rfl⟩; exact haxis t ht)
  obtain ⟨P, hP⟩ := h.close_polynomial hε
  have hloop := P.isLoop (fun t ht ↦ index_close_nonzero (hP t ht).2)
  have hPaxis : ∀ t ∈ Icc 0 (2 * Real.pi), P.eval t ∈ Complex.slitPlane := by
    intro t ht
    apply heps
    exact Metric.mem_thickening_iff.mpr ⟨γ t, mem_image_of_mem γ ht,
      by simpa [dist_eq_norm] using (hP t ht).1⟩
  have hi := (continuousCurveIndex_eq_smooth h hloop (fun t ht ↦ (hP t ht).2)).trans
    (exercise24_zero_index hloop hPaxis)
  exact_mod_cast hi

/-- Exercise 25 remains true for continuous curves on the same interval.
The strict pointwise inequality has a positive uniform margin. Polynomials
chosen within one fourth of that margin satisfy the smooth perturbation
inequality, and each computes its original curve's index. -/
theorem exercise26_perturbation_extension {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : IsContinuousNonzeroLoop γ₁) (h₂ : IsContinuousNonzeroLoop γ₂)
    (hclose : ∀ t ∈ Icc 0 (2 * Real.pi), ‖γ₁ t - γ₂ t‖ < ‖γ₁ t‖) :
    continuousCurveIndex γ₁ h₁ = continuousCurveIndex γ₂ h₂ := by
  obtain ⟨ε, hε, hmargin⟩ := index_positive_lower_bound
    (h₁.continuous.norm.sub (h₁.continuous.sub h₂.continuous).norm)
    (fun t ht ↦ sub_pos.mpr (hclose t ht))
  obtain ⟨P, hP⟩ := h₁.close_polynomial (show 0 < ε / 4 by positivity)
  obtain ⟨Q, hQ⟩ := h₂.close_polynomial (show 0 < ε / 4 by positivity)
  have hploop := P.isLoop (fun t ht ↦ index_close_nonzero (hP t ht).2)
  have hqloop := Q.isLoop (fun t ht ↦ index_close_nonzero (hQ t ht).2)
  have hpq : ∀ t ∈ Icc 0 (2 * Real.pi), ‖P.eval t - Q.eval t‖ < ‖P.eval t‖ := by
    intro t ht
    have htri₁ := dist_triangle (P.eval t) (γ₁ t) (Q.eval t)
    have htri₂ := dist_triangle (γ₁ t) (γ₂ t) (Q.eval t)
    have hlower := dist_triangle (γ₁ t) (P.eval t) 0
    simp only [dist_eq_norm, sub_zero, norm_sub_rev (γ₁ t) (P.eval t),
      norm_sub_rev (γ₂ t) (Q.eval t)] at htri₁ htri₂ hlower
    have hm : ε < ‖γ₁ t‖ - ‖γ₁ t - γ₂ t‖ := hmargin t ht
    linarith [(hP t ht).1, (hQ t ht).1]
  have hi : (continuousCurveIndex γ₁ h₁ : ℂ) = (continuousCurveIndex γ₂ h₂ : ℂ) :=
    (continuousCurveIndex_eq_smooth h₁ hploop (fun t ht ↦ (hP t ht).2)).trans
      ((exercise25_index_stability hploop hqloop hpq).trans
        (continuousCurveIndex_eq_smooth h₂ hqloop (fun t ht ↦ (hQ t ht).2)).symm)
  exact_mod_cast hi

end Rudin.Chapter08
