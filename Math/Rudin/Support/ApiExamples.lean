module

public import Mathlib.Order.Completion
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-! Compile probes for the pinned Mathlib API. These are not exercise solutions. -/

@[expose] public section

namespace Rudin.Support.ApiExamples

open Set MeasureTheory
open scoped Topology

-- Order completion is not Rudin's nonempty proper lower cut without a greatest element.
#check DedekindCut.principal
#check DedekindCut.principalEmbedding
#check DedekindCut.factorEmbedding
#check Real.equivCauchy
#check Real.mk_eq

example (q : ℚ) : (DedekindCut.principal q).left = Iic q := rfl

-- The standard completion uses Cauchy filters and a separation quotient.
#check UniformSpace.Completion
#check UniformSpace.Completion.coe_isometry
#check UniformSpace.Completion.denseRange_coe
#check UniformSpace.Completion.extension_coe

example {X : Type*} [MetricSpace X] (x y : X) :
    dist (x : UniformSpace.Completion X) (y : UniformSpace.Completion X) = dist x y :=
  UniformSpace.Completion.coe_isometry.dist_eq x y

example {X : Type*} [MetricSpace X] : CompleteSpace (UniformSpace.Completion X) :=
  inferInstance

-- A Stieltjes measure is not itself a Riemann–Stieltjes integral.
#check StieltjesFunction.measure_Ioc
#check StieltjesFunction.measure_Icc
#check StieltjesFunction.measure_singleton
#check Monotone.stieltjesFunction_eq
#check intervalIntegral.integral_of_le
#check BoxIntegral.HasIntegral
#check BoxIntegral.Integrable.hasIntegral
#check MeasureTheory.IntegrableOn.hasBoxIntegral
#check ContinuousOn.hasBoxIntegral
#check MeasureTheory.AEContinuous.hasBoxIntegral
#check BoxIntegral.IntegrationParams.Riemann
#check BoxIntegral.BoxAdditiveMap.upperSubLower

example (μ : Measure (Fin 1 → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : BoxIntegral.Box (Fin 1)) {f : (Fin 1 → ℝ) → ℝ}
    (hf : ContinuousOn f I.Icc) :
    BoxIntegral.HasIntegral I BoxIntegral.IntegrationParams.Riemann f
      μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) :=
  hf.hasBoxIntegral μ BoxIntegral.IntegrationParams.Riemann

example (α : StieltjesFunction ℝ) (a b : ℝ) :
    α.measure (Ioc a b) = ENNReal.ofReal (α b - α a) := α.measure_Ioc a b

-- Local existence and uniqueness have separate domain and regularity requirements.
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#check ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
#check ODE_solution_unique

example {v : ℝ → ℝ} {x₀ : ℝ} (hv : ContDiffAt ℝ 1 v x₀) (t₀ : ℝ) :
    ∃ γ : ℝ → ℝ, γ t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γ (v (γ t)) t :=
  hv.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

-- Periodic Fourier series and the real-line Fourier transform are different APIs.
#check fourierCoeff
#check fourierCoeff_eq_intervalIntegral
#check hasSum_fourier_series_L2
#check tsum_sq_fourierCoeff
#check Real.fourier_real_eq_integral_exp_smul
#check Real.Gamma_eq_integral
#check Real.Gamma_add_one
#check Complex.Gamma_eq_integral

example (n : ℕ) : Real.Gamma (n + 1) = n.factorial :=
  Real.Gamma_nat_eq_factorial n

-- Forms on normed spaces, not a bundled manifold forms/integration package.
#check extDeriv
#check extDeriv_apply
#check extDeriv_extDeriv
#check extDeriv_pullback
#check ContinuousAlternatingMap.compContinuousLinearMap
#check Orientation
#check Orientation.map_eq_iff_det_pos
#check AlternatingMap.domCoprod
#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
#check MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le

example (f : ℝ → ℝ) (x : ℝ) :
    extDeriv (fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ ℝ (Fin 0) (f y)) x =
      ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1) (fderiv ℝ f x) :=
  extDeriv_constOfIsEmpty f x

example {n : ℕ} {ω : ℝ → ℝ [⋀^Fin n]→L[ℝ] ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hω : DifferentiableAt ℝ ω (g x)) (hg : ContDiffAt ℝ 2 g x) :
    extDeriv (fun y ↦ (ω (g y)).compContinuousLinearMap (fderiv ℝ g y)) x =
      (extDeriv ω (g x)).compContinuousLinearMap (fderiv ℝ g x) :=
  extDeriv_pullback hω hg (by norm_num)

-- Lp contains almost-everywhere classes, not specified pointwise representatives.
#check MemLp.toLp
#check MemLp.coeFn_toLp
#check MemLp.toLp_eq_toLp_iff
#check Lp.ext
#check MeasureTheory.Lp.instCompleteSpace

example : CompleteSpace (Lp ℝ 2 (volume : Measure ℝ)) := inferInstance

example {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : f =ᵐ[volume] g) : hf.toLp f = hg.toLp g :=
  hf.toLp_congr hg hfg

end Rudin.Support.ApiExamples
