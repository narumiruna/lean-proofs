module

public import Math.Rudin.Support.OrientedChains
public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration on parameterized path chains

The integrand is the actual pullback coefficient `ω(p(t))(p'(t))`.
Reversal and constant-path identities prove descent to the existing signed
path quotient. For a continuous coefficient, a proved Darboux bridge identifies
the integral with Rudin's one-dimensional Riemann convention.

The definition uses the total Bochner interval integral: a nonintegrable
coefficient gives zero. `deriv` and `fderiv` also use zero where the required
derivative does not exist. These defaults do not certify a source path integral.
`darboux_path_bridge` certifies the scalar coefficient only. The source
exterior-boundary comparison also requires the stated genuine derivatives.
No general simplex integration or higher-dimensional Stokes theorem is claimed.
-/

@[expose] public section

noncomputable section

namespace Rudin.Support.PathIntegration

open Set Filter Topology MeasureTheory
open OrientedChains.Parametric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real scalar-valued differential 1-form in its continuous-linear form. -/
abbrev OneForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E → E →L[ℝ] ℝ

/-- The actual alternating-map representation of a 1-form, without changing it. -/
def fromAlternating (ω : E → E [⋀^Fin 1]→L[ℝ] ℝ) : OneForm E :=
  fun x => (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm (ω x)

@[simp] theorem fromAlternating_apply (ω : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x v : E) :
    fromAlternating ω x v = ω x (fun _ => v) := rfl

/-- A scalar potential as an actual differential 0-form. -/
def zeroForm (f : E → ℝ) (x : E) : E [⋀^Fin 0]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f x)

theorem exterior_potential (f : E → ℝ) (x v : E) :
    fromAlternating (extDeriv (zeroForm f)) x v = fderiv ℝ f x v := by
  rw [fromAlternating_apply]
  change extDeriv (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y))
    x (fun _ => v) = _
  rw [extDeriv_constOfIsEmpty]
  rfl

/-- The coefficient of the pullback to a real parameter. -/
def coefficient (ω : OneForm E) (p : Path E) (t : ℝ) : ℝ :=
  ω (p t) (deriv p t)

/-- Integration on the unit parameter interval, retaining its orientation. -/
def pathIntegral (ω : OneForm E) (p : Path E) : ℝ :=
  ∫ t in 0..1, coefficient ω p t

theorem coefficient_reverse (ω : OneForm E) (p : Path E) (t : ℝ) :
    coefficient ω (reverse p) t = -coefficient ω p (1 - t) := by
  change (ω (p (1 - t))) (deriv (fun x => p (1 - x)) t) =
    -(ω (p (1 - t))) (deriv p (1 - t))
  rw [deriv_comp_const_sub, map_neg]

theorem pathIntegral_reverse (ω : OneForm E) (p : Path E) :
    pathIntegral ω (reverse p) = -pathIntegral ω p := by
  simp only [pathIntegral, coefficient_reverse, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_sub_left]
  norm_num

@[simp] theorem pathIntegral_constant (ω : OneForm E) (a : E) :
    pathIntegral ω (fun _ => a) = 0 := by
  simp [pathIntegral, coefficient]

/-- Extend integration linearly before taking the orientation quotient. -/
def rawIntegral (ω : OneForm E) : FreeAbelianGroup (Path E) →+ ℝ :=
  FreeAbelianGroup.lift (pathIntegral ω)

@[simp] theorem rawIntegral_generator (ω : OneForm E) (p : Path E) :
    rawIntegral ω (FreeAbelianGroup.of p) = pathIntegral ω p := by
  simp [rawIntegral]

theorem rawIntegral_relation (ω : OneForm E) {r : FreeAbelianGroup (Path E)}
    (hr : PathRelation r) : rawIntegral ω r = 0 := by
  cases hr <;> simp [pathIntegral_reverse]

/-- The actual integral is well-defined on the proved path-orientation quotient. -/
def chainIntegral (ω : OneForm E) : PathChain E →+ ℝ :=
  QuotientAddGroup.lift (pathRelations E) (rawIntegral ω) (by
    intro r hr
    induction hr using AddSubgroup.closure_induction with
    | mem r hr => exact rawIntegral_relation ω hr
    | zero => exact (rawIntegral ω).ker.zero_mem
    | add r s _ _ hr hs => exact (rawIntegral ω).ker.add_mem hr hs
    | neg r _ hr => exact (rawIntegral ω).ker.neg_mem hr)

@[simp] theorem chainIntegral_path (ω : OneForm E) (p : Path E) :
    chainIntegral ω (path p) = pathIntegral ω p := by
  simp [chainIntegral, path, rawIntegral]

/-- A continuous pullback coefficient has Rudin's actual Darboux integral. -/
theorem darboux_path_bridge (ω : OneForm E) (p : Path E)
    (h : ContinuousOn (coefficient ω p) (Icc 0 1)) :
    StieltjesPrototype.HasDarbouxRSIntegral (coefficient ω p) id 0 1 (pathIntegral ω p) := by
  have hb := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (show (0 : ℝ) ≤ 1 by norm_num) h
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id, pathIntegral] using hb

/-- The line-integral boundary theorem for a differentiable potential.
Differentiability and integrability are inputs, not a Stokes identity. -/
theorem potential_boundary (f : E → ℝ) (p : Path E)
    (hf : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ f (p t))
    (hp : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ p t)
    (hi : IntervalIntegrable (coefficient (fderiv ℝ f) p) volume 0 1) :
    chainIntegral (fderiv ℝ f) (path p) = f (p 1) - f (p 0) := by
  rw [chainIntegral_path, pathIntegral]
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => f (p s)) (coefficient (fderiv ℝ f) p t) t := by
    intro t ht
    exact (hf t ht).hasFDerivAt.comp_hasDerivAt t (hp t ht).hasDerivAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- The source integral of the exterior derivative equals the actual endpoint
boundary evaluation, under continuous pullback and differentiability conditions. -/
theorem darboux_exterior_boundary (f : E → ℝ) (p : Path E)
    (hf : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ f (p t))
    (hp : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ p t)
    (hc : ContinuousOn (coefficient (fderiv ℝ f) p) (Icc 0 1)) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating (extDeriv (zeroForm f))) p) id 0 1
      ((FreeAbelianGroup.lift f) (pathBoundary (path p))) := by
  have he : coefficient (fromAlternating (extDeriv (zeroForm f))) p =
      coefficient (fderiv ℝ f) p := by
    funext t
    exact exterior_potential f (p t) (deriv p t)
  rw [he]
  have hi : IntervalIntegrable (coefficient (fderiv ℝ f) p) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hb := potential_boundary f p hf hp hi
  rw [chainIntegral_path] at hb
  have hd := darboux_path_bridge (fderiv ℝ f) p hc
  rw [hb] at hd
  simpa only [pathBoundary_path, map_sub, FreeAbelianGroup.lift_apply_of] using hd

/-- The actual affine path has its specified tangent, including constant paths. -/
theorem segment_hasDerivAt (a b : E) (t : ℝ) :
    HasDerivAt (segment a b) (b - a) t := by
  change HasDerivAt (fun s : ℝ => (1 - s) • a + s • b) (b - a) t
  have h := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a).add
    ((hasDerivAt_id t).smul_const b)
  simpa only [OrientedChains.Parametric.segment, Pi.add_def, Pi.sub_apply, id_eq,
    zero_sub, neg_smul, one_smul, neg_add_eq_sub] using h

/-- A concrete pullback computation in the actual derivative API. -/
theorem quadratic_coefficient (a b t : ℝ) :
    coefficient (fderiv ℝ (fun x : ℝ => x ^ 2)) (segment a b) t =
      (2 * segment a b t) * (b - a) := by
  unfold coefficient
  rw [(segment_hasDerivAt a b t).deriv, (hasDerivAt_pow 2 (segment a b t)).hasFDerivAt.fderiv]
  simp
  ring

/-- A nontrivial source-integral/boundary comparison with no remaining
regularity or integrability assumptions, also valid for `a=b` and reversal. -/
theorem quadratic_segment (a b : ℝ) :
    chainIntegral (fderiv ℝ (fun x : ℝ => x ^ 2)) (path (segment a b)) = b ^ 2 - a ^ 2 ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating (extDeriv (zeroForm (fun x : ℝ => x ^ 2)))) (segment a b))
      id 0 1 (b ^ 2 - a ^ 2) := by
  have hc : ContinuousOn
      (coefficient (fderiv ℝ (fun x : ℝ => x ^ 2)) (segment a b)) (Icc 0 1) := by
    have he : coefficient (fderiv ℝ (fun x : ℝ => x ^ 2)) (segment a b) =
        fun t => (2 * segment a b t) * (b - a) := funext (quadratic_coefficient a b)
    rw [he]
    unfold OrientedChains.Parametric.segment
    fun_prop
  have hf : ∀ t ∈ uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun x : ℝ => x ^ 2) (segment a b t) :=
    fun t _ => (hasDerivAt_pow 2 _).differentiableAt
  have hp : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ (segment a b) t :=
    fun t _ => (segment_hasDerivAt a b t).differentiableAt
  have hi : IntervalIntegrable
      (coefficient (fderiv ℝ (fun x : ℝ => x ^ 2)) (segment a b)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  constructor
  · simpa [OrientedChains.Parametric.segment] using potential_boundary (fun x : ℝ => x ^ 2) (segment a b) hf hp hi
  · simpa [pathBoundary_path, FreeAbelianGroup.lift_apply_of, OrientedChains.Parametric.segment] using
      darboux_exterior_boundary (fun x : ℝ => x ^ 2) (segment a b) hf hp hc

end Rudin.Support.PathIntegration
