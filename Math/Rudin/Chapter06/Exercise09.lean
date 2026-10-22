module

public import Math.Rudin.Chapter06.Exercise07

/-!
# Chapter 6, Exercise 9

The rules below state the local derivative, derivative-continuity, boundary
limit, and convergence hypotheses. Within derivatives allow one-sided
regularity at an included finite endpoint. No derivative at the omitted
endpoint, or integrability over the whole ray, is assumed.

The example uses the infinite-endpoint rule. All four proper truncations
(the two functions and their absolute values) have actual Riemann integrals.
Source: book page 139, PDF page 148.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesIntegralLaws
open scoped Topology

private theorem cosine_kernel_eq :
    oscillatoryKernel 1 = fun x ↦ Real.cos x / (1 + x) := by
  ext x
  simp [oscillatoryKernel]

private theorem sine_kernel_eq :
    sineSquareKernel 1 = fun x ↦ Real.sin x / (1 + x) ^ 2 := by
  ext x
  simp [sineSquareKernel]

private theorem boundary_one_eq :
    oscillatoryBoundary 1 = fun x ↦ (1 / (1 + x)) * Real.sin x := by
  ext x
  simp [oscillatoryBoundary, div_eq_mul_inv, mul_comm]

/-- Proper integration by parts with explicit derivative witnesses, also on a
singleton interval. The conclusion includes both actual Riemann integrals. -/
theorem properRiemann_integration_by_parts {u u' v v' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : ∀ x ∈ Icc a b, HasDerivWithinAt u (u' x) (Icc a b) x)
    (hv : ∀ x ∈ Icc a b, HasDerivWithinAt v (v' x) (Icc a b) x)
    (hu' : ContinuousOn u' (Icc a b)) (hv' : ContinuousOn v' (Icc a b)) :
    HasDarbouxRSIntegral (fun x ↦ u x * v' x) id a b
      (∫ x in a..b, u x * v' x) ∧
    HasDarbouxRSIntegral (fun x ↦ u' x * v x) id a b
      (∫ x in a..b, u' x * v x) ∧
    (∫ x in a..b, u x * v' x) =
      u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  have huc : ContinuousOn u (Icc a b) := fun x hx ↦ (hu x hx).continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun x hx ↦ (hv x hx).continuousWithinAt
  refine ⟨properRiemann_of_continuousOn hab (huc.mul hv'),
    properRiemann_of_continuousOn hab (hu'.mul hvc), ?_⟩
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
  · simpa only [uIcc_of_le hab] using hu
  · simpa only [uIcc_of_le hab] using hv
  · exact hu'.intervalIntegrable_of_Icc hab
  · exact hv'.intervalIntegrable_of_Icc hab

/-- **Finite-endpoint rule**. Local C¹ data on `(a,b]`, a finite boundary
limit, and convergence of one integral imply convergence of the other. -/
theorem exercise09_finite_endpoint_rule {u u' v v' : ℝ → ℝ} {a b L I : ℝ}
    (hab : a < b)
    (hu : ∀ x ∈ Ioc a b, HasDerivWithinAt u (u' x) (Ioc a b) x)
    (hv : ∀ x ∈ Ioc a b, HasDerivWithinAt v (v' x) (Ioc a b) x)
    (hu' : ContinuousOn u' (Ioc a b)) (hv' : ContinuousOn v' (Ioc a b))
    (hboundary : Tendsto (fun x ↦ u x * v x) (𝓝[>] a) (𝓝 L))
    (hi : HasImproperRiemannIntegralLeft (fun x ↦ u' x * v x) a b I) :
    HasImproperRiemannIntegralLeft (fun x ↦ u x * v' x) a b
      (u b * v b - L - I) := by
  have hp (c : ℝ) (hc : a < c) (hcb : c ≤ b) :=
    properRiemann_integration_by_parts hcb
      (fun x hx ↦ (hu x ⟨hc.trans_le hx.1, hx.2⟩).mono
        (fun _ hy ↦ ⟨hc.trans_le hy.1, hy.2⟩))
      (fun x hx ↦ (hv x ⟨hc.trans_le hx.1, hx.2⟩).mono
        (fun _ hy ↦ ⟨hc.trans_le hy.1, hy.2⟩))
      (hu'.mono (fun _ hx ↦ ⟨hc.trans_le hx.1, hx.2⟩))
      (hv'.mono (fun _ hx ↦ ⟨hc.trans_le hx.1, hx.2⟩))
  refine ⟨hab, fun c hc hcb ↦ (hp c hc hcb).1, ?_⟩
  have hlim := (hboundary.const_sub (u b * v b)).sub hi.2.2
  apply hlim.congr'
  filter_upwards [Ioc_mem_nhdsGT hab] with c hc
  exact (hp c hc.1 hc.2).2.2.symm

/-- **Infinite-endpoint rule**. Local C¹ data on `[a,∞)`, a finite boundary
limit, and convergence of one integral imply convergence of the other. -/
theorem exercise09_infinite_endpoint_rule {u u' v v' : ℝ → ℝ} {a L I : ℝ}
    (hu : ∀ x ∈ Ici a, HasDerivWithinAt u (u' x) (Ici a) x)
    (hv : ∀ x ∈ Ici a, HasDerivWithinAt v (v' x) (Ici a) x)
    (hu' : ContinuousOn u' (Ici a)) (hv' : ContinuousOn v' (Ici a))
    (hboundary : Tendsto (fun x ↦ u x * v x) atTop (𝓝 L))
    (hi : HasImproperRiemannIntegralTop (fun x ↦ u' x * v x) a I) :
    HasImproperRiemannIntegralTop (fun x ↦ u x * v' x) a
      (L - u a * v a - I) := by
  have hp (b : ℝ) (hb : a ≤ b) :=
    properRiemann_integration_by_parts hb
      (fun x hx ↦ (hu x hx.1).mono Icc_subset_Ici_self)
      (fun x hx ↦ (hv x hx.1).mono Icc_subset_Ici_self)
      (hu'.mono Icc_subset_Ici_self) (hv'.mono Icc_subset_Ici_self)
  refine ⟨fun b hb ↦ (hp b hb).1, ?_⟩
  have hlim := (hboundary.sub_const (u a * v a)).sub hi.2
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop a] with b hb
  exact (hp b hb).2.2.symm

/-- All proper truncations in the example and its absolute-convergence tests.
This includes the zero-length interval `[0,0]`. -/
theorem exercise09_proper {b : ℝ} (hb : 0 ≤ b) :
    HasDarbouxRSIntegral (fun x ↦ Real.cos x / (1 + x)) id 0 b
      (∫ x in 0..b, Real.cos x / (1 + x)) ∧
    HasDarbouxRSIntegral (fun x ↦ Real.sin x / (1 + x) ^ 2) id 0 b
      (∫ x in 0..b, Real.sin x / (1 + x) ^ 2) ∧
    HasDarbouxRSIntegral (fun x ↦ |Real.cos x / (1 + x)|) id 0 b
      (∫ x in 0..b, |Real.cos x / (1 + x)|) ∧
    HasDarbouxRSIntegral (fun x ↦ |Real.sin x / (1 + x) ^ 2|) id 0 b
      (∫ x in 0..b, |Real.sin x / (1 + x) ^ 2|) := by
  have hc : ContinuousOn (fun x ↦ Real.cos x / (1 + x)) (Icc 0 b) := by
    simpa only [cosine_kernel_eq] using
      (continuousOn_oscillatoryKernel 1).mono (show Icc 0 b ⊆ Ici 0 from fun _ hx ↦ hx.1)
  have hs : ContinuousOn (fun x ↦ Real.sin x / (1 + x) ^ 2) (Icc 0 b) := by
    simpa only [sine_kernel_eq] using
      (continuousOn_sineSquareKernel 1).mono (show Icc 0 b ⊆ Ici 0 from fun _ hx ↦ hx.1)
  exact ⟨properRiemann_of_continuousOn hb hc, properRiemann_of_continuousOn hb hs,
    properRiemann_of_continuousOn hb hc.abs, properRiemann_of_continuousOn hb hs.abs⟩

/-- The sine integral is absolutely convergent, with a proper Riemann witness
at every truncation and a finite limiting value. -/
theorem exercise09_sine_absolute :
    ImproperRiemannIntegrableTop (fun x ↦ |Real.sin x / (1 + x) ^ 2|) 0 := by
  have hi : IntegrableOn (fun x ↦ Real.sin x / (1 + x) ^ 2) (Ioi 0) := by
    simpa only [sine_kernel_eq] using integrableOn_sineSquareKernel 1
  exact ⟨_, improperRiemannTop_of_integrableOn
    (fun _ hb ↦ (exercise09_proper hb).2.2.2) hi.abs⟩

/-- Apply integration by parts with `u = 1/(1+x)` and `v = sin x`.
Both improper integrals converge and have the same finite value. -/
theorem exercise09_example_equality :
    ∃ I : ℝ,
      HasImproperRiemannIntegralTop (fun x ↦ Real.cos x / (1 + x)) 0 I ∧
      HasImproperRiemannIntegralTop (fun x ↦ Real.sin x / (1 + x) ^ 2) 0 I := by
  have hs : IntegrableOn (fun x ↦ Real.sin x / (1 + x) ^ 2) (Ioi 0) := by
    simpa only [sine_kernel_eq] using integrableOn_sineSquareKernel 1
  let I : ℝ := ∫ x in Ioi 0, Real.sin x / (1 + x) ^ 2
  have hsi : HasImproperRiemannIntegralTop (fun x ↦ Real.sin x / (1 + x) ^ 2) 0 I :=
    improperRiemannTop_of_integrableOn (fun _ hb ↦ (exercise09_proper hb).2.1) hs
  have hn : HasImproperRiemannIntegralTop
      (fun x ↦ (-1 / (1 + x) ^ 2) * Real.sin x) 0 (-I) := by
    have heq : (fun x ↦ (-1 / (1 + x) ^ 2) * Real.sin x) =
        fun x ↦ -(Real.sin x / (1 + x) ^ 2) := by
      ext x
      ring
    rw [heq]
    refine ⟨fun b hb ↦ ?_, ?_⟩
    · simpa only [intervalIntegral.integral_neg] using hasDarbouxRSIntegral_neg hb (hsi.1 b hb)
    · simpa only [intervalIntegral.integral_neg] using hsi.2.neg
  have hu (x : ℝ) (hx : x ∈ Ici 0) :
      HasDerivWithinAt (fun t : ℝ ↦ 1 / (1 + t)) (-1 / (1 + x) ^ 2) (Ici 0) x := by
    have hx' : 1 + x ≠ 0 := by linarith [mem_Ici.mp hx]
    apply HasDerivAt.hasDerivWithinAt
    convert (((hasDerivAt_id x).const_add 1).inv hx') using 1
    · ext t
      simp [one_div]
    · simp
  have hu' : ContinuousOn (fun x : ℝ ↦ -1 / (1 + x) ^ 2) (Ici 0) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (by linarith [mem_Ici.mp hx])
  have hboundary : Tendsto (fun x : ℝ ↦ (1 / (1 + x)) * Real.sin x) atTop (𝓝 0) := by
    simpa only [boundary_one_eq] using oscillatoryBoundary_tendsto (k := 1) one_ne_zero
  have h := exercise09_infinite_endpoint_rule hu
    (fun x _ ↦ (Real.hasDerivAt_sin x).hasDerivWithinAt) hu'
    Real.continuous_cos.continuousOn hboundary hn
  refine ⟨I, ?_, hsi⟩
  simpa only [Real.sin_zero, mul_zero, zero_mul, zero_sub, neg_neg, one_mul,
    sub_zero, one_div, mul_comm, div_eq_mul_inv] using h

/-- The cosine integral converges conditionally, not absolutely. -/
theorem exercise09_cosine_not_absolute :
    ¬ ImproperRiemannIntegrableTop (fun x ↦ |Real.cos x / (1 + x)|) 0 := by
  simpa only [cosine_kernel_eq] using oscillatoryKernel_one_not_absolute

end Rudin.Chapter06
