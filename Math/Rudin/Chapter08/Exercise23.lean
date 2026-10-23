module

public import Math.Rudin.Chapter08.Exercise11
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Chapter 8, Exercise 23

The derivative is specified within the closed parameter interval. Thus no
extension of the curve or two-sided endpoint derivative is required.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace Rudin.Chapter08

/-- A continuously differentiable, closed curve which does not meet zero.
The velocity is an explicit derivative jet, including the endpoints. -/
structure IsC1NonzeroLoop (γ v : ℝ → ℂ) (a b : ℝ) : Prop where
  ordered : a ≤ b
  closed : γ a = γ b
  derivative : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t
  continuous_velocity : ContinuousOn v (Icc a b)
  nonzero : ∀ t ∈ Icc a b, γ t ≠ 0

noncomputable def curveIndex (γ v : ℝ → ℂ) (a b : ℝ) : ℂ :=
  (∫ t in a..b, v t / γ t) / (2 * Real.pi * Complex.I)

namespace IsC1NonzeroLoop

variable {γ v : ℝ → ℂ} {a b : ℝ} (h : IsC1NonzeroLoop γ v a b)

include h

theorem continuous : ContinuousOn γ (Icc a b) :=
  fun t ht ↦ (h.derivative t ht).continuousWithinAt

theorem continuous_logDerivative : ContinuousOn (fun t ↦ v t / γ t) (Icc a b) :=
  h.continuous_velocity.div h.continuous h.nonzero

theorem integrable_logDerivative : IntervalIntegrable (fun t ↦ v t / γ t) volume a b :=
  h.continuous_logDerivative.intervalIntegrable_of_Icc h.ordered

/-- The logarithmic derivative has the literal source Riemann integral. -/
theorem riemann_logDerivative :
    Rudin.Support.StieltjesComplex.HasComplexRSIntegral (fun t ↦ v t / γ t) id a b
      (∫ t in a..b, v t / γ t) := by
  obtain ⟨z, hz⟩ := continuous_riemannIntegrableComplex h.ordered h.continuous_logDerivative
  rw [(complex_riemann_bridge h.ordered hz).2]
  exact hz

/-- Every cut of the source primitive also has its actual Riemann value. -/
theorem riemann_logDerivative_subinterval {c d : ℝ} (hcd : c ≤ d)
    (hsub : Icc c d ⊆ Icc a b) :
    Rudin.Support.StieltjesComplex.HasComplexRSIntegral (fun t ↦ v t / γ t) id c d
      (∫ t in c..d, v t / γ t) := by
  obtain ⟨z, hz⟩ := continuous_riemannIntegrableComplex hcd
    (h.continuous_logDerivative.mono hsub)
  rw [(complex_riemann_bridge hcd hz).2]
  exact hz

/-- A literal source integral computes the same normalized index. -/
theorem index_eq_riemann_value {z : ℂ}
    (hz : Rudin.Support.StieltjesComplex.HasComplexRSIntegral
      (fun t ↦ v t / γ t) id a b z) :
    curveIndex γ v a b = z / (2 * Real.pi * Complex.I) := by
  rw [curveIndex, (complex_riemann_bridge h.ordered hz).2]

/-- The derivative jet computes the usual integral with the canonical within
derivative. The singleton interval also has index zero, independently of its
nonunique derivative jet. -/
theorem index_eq_derivWithin : curveIndex γ v a b =
    (∫ t in a..b, derivWithin γ (Icc a b) t / γ t) / (2 * Real.pi * Complex.I) := by
  rcases lt_or_eq_of_le h.ordered with hab | rfl
  · unfold curveIndex
    congr 1
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    change v t / γ t = derivWithin γ (Icc a b) t / γ t
    rw [(h.derivative t ht).derivWithin (uniqueDiffOn_Icc hab t ht)]
  · simp [curveIndex]

/-- The primitive in Rudin's hint has the required within derivative. -/
theorem primitive_derivative {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun u ↦ ∫ s in a..u, v s / γ s)
      (v t / γ t) (Icc a b) t := by
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  apply integral_hasDerivWithinAt_right (t := Icc a b)
    (h.integrable_logDerivative.mono_set ?_)
    (h.continuous_logDerivative.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (h.continuous_logDerivative t ht)
  rw [uIcc_of_le ht.1, uIcc_of_le h.ordered]
  exact Icc_subset_Icc le_rfl ht.2

/-- Multiplication by the negative exponential of the primitive makes the
curve constant. This is the analytic step in the source hint. -/
theorem primitive_identity {t : ℝ} (ht : t ∈ Icc a b) :
    γ t * Complex.exp (-(∫ s in a..t, v s / γ s)) = γ a := by
  have hd : ∀ u ∈ Icc a b,
      HasDerivWithinAt (fun u ↦ γ u * Complex.exp (-(∫ s in a..u, v s / γ s)))
        0 (Icc a b) u := by
    intro u hu
    convert (h.derivative u hu).mul (h.primitive_derivative hu).neg.cexp using 1
    field_simp [h.nonzero u hu]
    ring
  have hz := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun u _ ↦ (norm_zero : ‖(0 : ℂ)‖ = 0).le) t ht
  simpa [sub_eq_zero] using hz

/-- The closed endpoint condition forces the exponential of the complete
primitive to be one. -/
theorem exp_integral_eq_one : Complex.exp (∫ t in a..b, v t / γ t) = 1 := by
  have hid := h.primitive_identity (right_mem_Icc.mpr h.ordered)
  rw [← h.closed] at hid
  have he : Complex.exp (-(∫ t in a..b, v t / γ t)) = 1 :=
    (mul_eq_left₀ (h.nonzero a (left_mem_Icc.mpr h.ordered))).mp hid
  have he' := Complex.exp_add (-(∫ t in a..b, v t / γ t))
    (∫ t in a..b, v t / γ t)
  simpa [he] using he'.symm

end IsC1NonzeroLoop

/-- The integral index is an integer, as a complex number. -/
theorem exercise23_integer_index {γ v : ℝ → ℂ} {a b : ℝ}
    (h : IsC1NonzeroLoop γ v a b) : ∃ n : ℤ, curveIndex γ v a b = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h.exp_integral_eq_one
  refine ⟨n, ?_⟩
  rw [curveIndex, hn, mul_div_cancel_right₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- Every integer, including zero and negative integers, is realized by the
circle with that signed angular speed. -/
theorem exercise23_circle (n : ℤ) :
    IsC1NonzeroLoop (fun t : ℝ ↦ Complex.exp (Complex.I * n * t))
      (fun t : ℝ ↦ Complex.exp (Complex.I * n * t) * (Complex.I * n))
      0 (2 * Real.pi) ∧
    curveIndex (fun t : ℝ ↦ Complex.exp (Complex.I * n * t))
      (fun t : ℝ ↦ Complex.exp (Complex.I * n * t) * (Complex.I * n))
      0 (2 * Real.pi) = n := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ Complex.exp (Complex.I * n * t))
      (Complex.exp (Complex.I * n * t) * (Complex.I * n)) t := by
    convert ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * n)).cexp using 1 <;> simp
  constructor
  · refine ⟨by positivity, ?_, fun t _ ↦ (hd t).hasDerivWithinAt, ?_,
      fun t _ ↦ Complex.exp_ne_zero _⟩
    · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      symm
      apply Complex.exp_eq_one_iff.mpr
      exact ⟨n, by push_cast; ring⟩
    · fun_prop
  · unfold curveIndex
    have he : (fun t : ℝ ↦ Complex.exp (Complex.I * n * t) * (Complex.I * n) /
        Complex.exp (Complex.I * n * t)) = fun _ : ℝ ↦ Complex.I * n := by
      funext t
      exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
    rw [he, intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp

/-- A continuous polar representation of the curve, based at its initial
point. The total change of its lifted angle is exactly `2π` times the
integral index. Positive and negative integers therefore count turns with
opposite orientations, while zero has zero net angular change. -/
theorem exercise23_signed_turns {γ v : ℝ → ℂ} {a b : ℝ}
    (h : IsC1NonzeroLoop γ v a b) :
    ∃ (ρ θ : ℝ → ℝ) (n : ℤ),
      ContinuousOn ρ (Icc a b) ∧ ContinuousOn θ (Icc a b) ∧
      (∀ t ∈ Icc a b, 0 < ρ t) ∧ θ a = 0 ∧
      (∀ t ∈ Icc a b, γ t = γ a * ρ t * Complex.exp (θ t * Complex.I)) ∧
      curveIndex γ v a b = n ∧ θ b - θ a = 2 * Real.pi * n := by
  let φ : ℝ → ℂ := fun t ↦ ∫ s in a..t, v s / γ s
  have hc : ContinuousOn φ (Icc a b) :=
    fun t ht ↦ (h.primitive_derivative ht).continuousWithinAt
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h.exp_integral_eq_one
  refine ⟨fun t ↦ Real.exp (φ t).re, fun t ↦ (φ t).im, n,
    Real.continuous_exp.comp_continuousOn (Complex.continuous_re.comp_continuousOn hc),
    Complex.continuous_im.comp_continuousOn hc, fun t _ ↦ Real.exp_pos _, by simp [φ], ?_, ?_, ?_⟩
  · intro t ht
    have hi := congrArg (fun z : ℂ ↦ z * Complex.exp (φ t)) (h.primitive_identity ht)
    have hex : Complex.exp (φ t) =
        (Real.exp (φ t).re : ℂ) * Complex.exp ((φ t).im * Complex.I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
    have hi' : γ t = γ a * Complex.exp (φ t) := by
      simpa only [φ, mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, mul_one] using hi
    rw [hi', hex, mul_assoc]
  · rw [curveIndex, hn, mul_div_cancel_right₀]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  · change (∫ s in a..b, v s / γ s).im - (∫ s in a..a, v s / γ s).im = _
    rw [hn]
    simp [Complex.mul_im]
    ring

end Rudin.Chapter08
