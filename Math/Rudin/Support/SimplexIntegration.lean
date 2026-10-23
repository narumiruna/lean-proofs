module

public import Math.Rudin.Support.PathIntegration
public import Math.Rudin.Support.RiemannIntegrability
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Smooth parameter simplexes and triangle integration

The parameter maps and pullbacks use actual Fréchet derivatives. The triangle
integral is an iterated integral on `0 ≤ x ≤ 1`, `0 ≤ y ≤ 1 - x`.
The boundary consists of restrictions of the full map, not segments between
image vertices. The boundary theorem below is a restricted two-dimensional
FTC theorem, not a general Stokes theorem. A nonlinear example has surface
and boundary integrals equal to `1/3`. The fixed-order comparison uses the
literal zero extension in Rudin's Example 10.4.

Coordinate pairs are used for the triangle calculations; no assertion about
the product norm being Euclidean is made. Arbitrary-dimensional smooth
simplexes use `EuclideanSpace`. Total derivatives and total Bochner integrals
alone do not certify source integrals. The comparison theorems have explicit
regularity assumptions. General orientation descent, reparameterization,
arbitrary-dimensional integration-order independence and general Stokes remain
open. The Euclidean set integral is not yet identified with the coordinate
triangle integral.
-/

@[expose] public section
noncomputable section

namespace Rudin.Support.SimplexIntegration

open Set MeasureTheory
open OrientedChains.Parametric PathIntegration

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Rudin's closed Cartesian parameter simplex, including dimension zero. -/
def standardSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

/-- An actual map of class C² on an open neighborhood of the parameter simplex.
No injectivity or nonzero Jacobian is required by Definition 10.30. -/
structure SmoothSimplex (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : EuclideanSpace ℝ (Fin n) → E
  neighborhood : Set (EuclideanSpace ℝ (Fin n))
  isOpen_neighborhood : IsOpen neighborhood
  contains : standardSimplex n ⊆ neighborhood
  smooth : ContDiffOn ℝ 2 toFun neighborhood

/-- The stored regularity gives a genuine ambient derivative on every face too. -/
theorem SmoothSimplex.differentiableAt {n : ℕ} (S : SmoothSimplex n E)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ standardSimplex n) :
    DifferentiableAt ℝ S.toFun u :=
  (S.smooth.differentiableOn (by norm_num) u (S.contains hu)).differentiableAt
    (S.isOpen_neighborhood.mem_nhds (S.contains hu))

/-- Nonlinear postcomposition acts on the full smooth map. -/
def SmoothSimplex.map {n : ℕ} (S : SmoothSimplex n E) (f : E → F)
    (hf : ContDiff ℝ 2 f) : SmoothSimplex n F where
  toFun := f ∘ S.toFun
  neighborhood := S.neighborhood
  isOpen_neighborhood := S.isOpen_neighborhood
  contains := S.contains
  smooth := hf.comp_contDiffOn S.smooth

/-- Differential forms in the same alternating-map model as Mathlib. -/
abbrev Form (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → E [⋀^Fin n]→L[ℝ] ℝ

/-- Pullback applies the actual derivative to each argument. -/
def pullback {n : ℕ} (ω : Form n F) (f : E → F) : Form n E :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

@[simp] theorem pullback_apply {n : ℕ} (ω : Form n F) (f : E → F)
    (x : E) (v : Fin n → E) :
    pullback ω f x v = ω (f x) (fun i => fderiv ℝ f x (v i)) := rfl

/-- Chain-rule comparison requires genuine derivatives, not default-zero values. -/
theorem pullback_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} (ω : Form n G) (g : F → G) (f : E → F) (x : E)
    (hg : DifferentiableAt ℝ g (f x)) (hf : DifferentiableAt ℝ f x) :
    pullback ω (g ∘ f) x = pullback (pullback ω g) f x := by
  ext v
  simp only [pullback_apply, fderiv_comp x hg hf, Function.comp_apply,
    ContinuousLinearMap.comp_apply]

/-- The exterior derivative commutes with the actual pullback under C²/C¹
pointwise assumptions, independently of any integration theorem. -/
theorem exterior_pullback {n : ℕ} (ω : Form n F) (f : E → F) (x : E)
    (hω : DifferentiableAt ℝ ω (f x)) (hf : ContDiffAt ℝ 2 f x) :
    extDeriv (pullback ω f) x = pullback (extDeriv ω) f x := by
  exact extDeriv_pullback hω hf (by norm_num)

/-- The top-degree coefficient evaluated on the ordered Euclidean basis. -/
def simplexCoefficient {n : ℕ} (ω : Form n E) (S : SmoothSimplex n E)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  pullback ω S.toFun u (fun i => EuclideanSpace.single i 1)

/-- Compactness is proved for the actual Euclidean parameter domain. -/
theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) := by
  have hclosed : IsClosed (standardSimplex n) := by
    change IsClosed ({u : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ u i} ∩
      {u | ∑ i, u i ≤ 1})
    apply IsClosed.inter
    · have h := isClosed_iInter (fun i : Fin n => isClosed_le
        (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)))
        (EuclideanSpace.proj i).continuous)
      simpa only [ofPred_forall, EuclideanSpace.coe_proj] using h
    · exact isClosed_le (show Continuous (fun u : EuclideanSpace ℝ (Fin n) => ∑ i, u i)
        by fun_prop) continuous_const
  have hcube : IsCompact ((EuclideanSpace.equiv (Fin n) ℝ) ⁻¹'
      {u : Fin n → ℝ | ∀ i, u i ∈ Icc (0 : ℝ) 1}) :=
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr
      (isCompact_pi_infinite (fun _ => isCompact_Icc))
  apply hcube.of_isClosed_subset hclosed
  intro u hu i
  refine ⟨hu.1 i, le_trans ?_ hu.2⟩
  exact Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)

/-- A continuous form and the stored C² regularity give a continuous pullback
coefficient on the closed simplex, including its boundary. -/
theorem simplexCoefficient_continuousOn {n : ℕ} (ω : Form n E)
    (S : SmoothSimplex n E) (hω : ContinuousOn ω (S.toFun '' standardSimplex n)) :
    ContinuousOn (simplexCoefficient ω S) (standardSimplex n) := by
  intro u hu
  have hS := (S.smooth u (S.contains hu)).contDiffAt
    (S.isOpen_neighborhood.mem_nhds (S.contains hu))
  have hD := hS.continuousAt_fderiv (by norm_num)
  have hw : ContinuousWithinAt (fun u => ω (S.toFun u)) (standardSimplex n) u :=
    (hω _ ⟨u, hu, rfl⟩).comp hS.continuousAt.continuousWithinAt
      (fun v hv => ⟨v, hv, rfl⟩)
  change ContinuousWithinAt
    (fun u => (ω (S.toFun u)).toContinuousMultilinearMap
      (fun i => fderiv ℝ S.toFun u (EuclideanSpace.single i 1))) _ _
  let hm := (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ :
    (E [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
  simpa only [hm, Function.comp_apply,
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply] using
    (hm.continuous.continuousAt.comp_continuousWithinAt hw).eval
      (continuousWithinAt_pi.mpr (fun i : Fin n =>
        hD.continuousWithinAt.clm_apply
          (continuousWithinAt_const (b := EuclideanSpace.single i 1))))

/-- Arbitrary-dimensional integration on the standard Euclidean simplex.
The following theorem certifies integrability. Comparison with the source's
repeated Riemann integral in arbitrary dimension is not proved here. -/
def simplexIntegral {n : ℕ} (ω : Form n E) (S : SmoothSimplex n E) : ℝ :=
  ∫ u in standardSimplex n, simplexCoefficient ω S u

theorem simplexCoefficient_integrable {n : ℕ} (ω : Form n E)
    (S : SmoothSimplex n E) (hω : ContinuousOn ω (S.toFun '' standardSimplex n)) :
    IntegrableOn (simplexCoefficient ω S) (standardSimplex n) :=
  (simplexCoefficient_continuousOn ω S hω).integrableOn_compact (standardSimplex_isCompact n)

/-- The two-dimensional standard simplex in pair coordinates. -/
def triangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-- The positively oriented faces `[e₁,e₂] - [0,e₂] + [0,e₁]`. -/
def triangleBoundary (S : (ℝ × ℝ) → E) : PathChain E :=
  path (fun t => S (1 - t, t)) - path (fun t => S (0, t)) +
    path (fun t => S (t, 0))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem triangleBoundary_squared (S : (ℝ × ℝ) → E) :
    pathBoundary (triangleBoundary S) = 0 := by
  simp [triangleBoundary, pathBoundary_path]

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem triangleBoundary_map (S : (ℝ × ℝ) → E) (f : E → F) :
    triangleBoundary (f ∘ S) = pathMap f (triangleBoundary S) := by
  simp [triangleBoundary, Function.comp_def]

/-- Actual top-degree pullback coefficient in positively oriented coordinates. -/
def triangleCoefficient (ω : Form 2 E) (S : (ℝ × ℝ) → E) (p : ℝ × ℝ) : ℝ :=
  pullback ω S p ![(1, 0), (0, 1)]

/-- Iteration first in `y`, then in `x`, over the closed triangle. -/
def triangleIntegral (f : (ℝ × ℝ) → ℝ) : ℝ :=
  ∫ x in 0..1, ∫ y in 0..(1 - x), f (x, y)

/-- Integration uses the pullback coefficient, not vertex evaluation. -/
def formIntegral (ω : Form 2 E) (S : (ℝ × ℝ) → E) : ℝ :=
  triangleIntegral (triangleCoefficient ω S)

/-- Each one-dimensional stage has the source Darboux integral. Continuity of
both the slices and the outer coefficient is explicit. This is a fixed-order
comparison; no integration-order or zero-extension theorem is asserted. -/
theorem triangle_darboux_bridge (f : (ℝ × ℝ) → ℝ)
    (hinner : ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun y => f (x, y)) (Icc 0 (1 - x)))
    (houter : ContinuousOn (fun x => ∫ y in 0..(1 - x), f (x, y)) (Icc 0 1)) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => f (x, y)) id 0 (1 - x) (∫ y in 0..(1 - x), f (x, y))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..(1 - x), f (x, y)) id 0 1 (triangleIntegral f) := by
  constructor
  · intro x hx
    have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
      (sub_nonneg.mpr hx.2) (hinner x hx)
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id] using h
  · have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
      (show (0 : ℝ) ≤ 1 by norm_num) houter
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id, triangleIntegral] using h

/-- The coordinate 1-form `P dx`. -/
def horizontal (P : (ℝ × ℝ) → ℝ) : OneForm (ℝ × ℝ) :=
  fun p => P p • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The same form in the alternating-map API, for actual `extDeriv`. -/
def horizontalForm (P : (ℝ × ℝ) → ℝ) : Form 1 (ℝ × ℝ) :=
  fun p => P p • ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem horizontalForm_apply (P : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ)
    (v : Fin 1 → ℝ × ℝ) : horizontalForm P p v = P p * (v 0).1 := rfl

/-- The horizontal form along the actual three standard faces. -/
theorem horizontal_boundary (P : (ℝ × ℝ) → ℝ) :
    chainIntegral (horizontal P) (triangleBoundary id) =
      (∫ t in 0..1, P (t, 0)) - ∫ t in 0..1, P (t, 1 - t) := by
  have hb (t : ℝ) : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t 0)
  have hv (t : ℝ) : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) t :=
    (hasDerivAt_const t 0).prodMk (hasDerivAt_id t)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (1 - t, t)) (-1, 1) t := by
    have h : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      exact (hasDerivAt_id t).const_sub 1
    exact h.prodMk (hasDerivAt_id t)
  simp only [triangleBoundary, map_add, map_sub, chainIntegral_path, pathIntegral,
    coefficient, Function.id_def]
  simp only [(hb _).deriv, (hv _).deriv, (hd _).deriv, horizontal,
    smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    mul_zero, mul_one, mul_neg_one, intervalIntegral.integral_zero,
    intervalIntegral.integral_neg, sub_zero]
  have he : (fun t => P (1 - t, t)) = (fun t => P (t, 1 - t)) ∘ (fun t => 1 - t) := by
    funext t
    simp
  rw [he]
  change -(∫ t in 0..1, (fun s => P (s, 1 - s)) (1 - t)) + _ = _
  have hi := intervalIntegral.integral_comp_sub_left
    (fun s => P (s, 1 - s)) (a := (0 : ℝ)) (b := 1) 1
  norm_num at hi
  simp only [sub_sub_cancel] at *
  rw [hi]
  ring

/-- The derivative of `P dx`, evaluated on the positive coordinate basis,
is `-∂P/∂y`. The derivative hypothesis rules out the total-derivative default. -/
theorem exterior_horizontal (P : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ)
    (hP : DifferentiableAt ℝ P p) :
    extDeriv (horizontalForm P) p ![(1, 0), (0, 1)] =
      -fderiv ℝ P p (0, 1) := by
  have hh : DifferentiableAt ℝ (horizontalForm P) p := by
    exact hP.smul_const _
  rw [extDeriv_apply hh]
  simp [Fin.sum_univ_two, horizontalForm_apply, Fin.removeNth]

/-- A continuous coefficient on the ambient coordinate plane has integrable
slices and an integrable outer coefficient. -/
theorem triangle_integrable (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    (∀ x : ℝ, IntervalIntegrable (fun y => f (x, y)) volume 0 (1 - x)) ∧
    IntervalIntegrable (fun x => ∫ y in 0..(1 - x), f (x, y)) volume 0 1 := by
  constructor
  · intro x
    exact (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · apply Continuous.intervalIntegrable
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x y => f (x, y)) hf (continuous_const.sub continuous_id)

/-- The fixed-order source comparison follows from ordinary continuity; no
integrability or numerical integral identity is assumed. -/
theorem triangle_darboux_of_continuous (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => f (x, y)) id 0 (1 - x) (∫ y in 0..(1 - x), f (x, y))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..(1 - x), f (x, y)) id 0 1 (triangleIntegral f) := by
  apply triangle_darboux_bridge
  · intro x _
    exact (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x y => f (x, y)) hf (continuous_const.sub continuous_id)).continuousOn

/-- The actual exterior coefficient on the identity triangle. -/
theorem triangleCoefficient_horizontal (P : (ℝ × ℝ) → ℝ)
    (hP : Differentiable ℝ P) (p : ℝ × ℝ) :
    triangleCoefficient (extDeriv (horizontalForm P)) id p =
      -fderiv ℝ P p (0, 1) := by
  simpa [triangleCoefficient, pullback_apply] using exterior_horizontal P p (hP p)

/-- Slice FTC on the triangle, with a genuine derivative and its continuity. -/
theorem horizontal_slice (P : (ℝ × ℝ) → ℝ) (hP : ContDiff ℝ 1 P) (x : ℝ) :
    (∫ y in 0..(1 - x), -fderiv ℝ P (x, y) (0, 1)) =
      P (x, 0) - P (x, 1 - x) := by
  have hd (y : ℝ) : HasDerivAt (fun y => P (x, y)) (fderiv ℝ P (x, y) (0, 1)) y :=
    (hP.differentiable (by norm_num) (x, y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  have hc : Continuous (fun y => fderiv ℝ P (x, y) (0, 1)) := by
    exact (hP.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.comp
      (continuous_const.prodMk continuous_id)
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      (hc.intervalIntegrable _ _)]
  ring

/-- A two-dimensional boundary theorem for C¹ horizontal forms. It is proved
from slice FTC and the actual three face tangents, not assumed Stokes. The
ambient C¹ hypothesis is stronger than C¹ on a neighborhood of the triangle. -/
theorem horizontal_stokes (P : (ℝ × ℝ) → ℝ) (hP : ContDiff ℝ 1 P) :
    formIntegral (extDeriv (horizontalForm P)) id =
      chainIntegral (horizontal P) (triangleBoundary id) := by
  have he : triangleCoefficient (extDeriv (horizontalForm P)) id =
      fun p => -fderiv ℝ P p (0, 1) :=
    funext (triangleCoefficient_horizontal P (hP.differentiable (by norm_num)))
  rw [formIntegral, he, triangleIntegral]
  simp_rw [horizontal_slice P hP]
  rw [intervalIntegral.integral_sub, horizontal_boundary]
  · exact (hP.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (hP.continuous.comp (continuous_id.prodMk
      (continuous_const.sub continuous_id))).intervalIntegrable _ _

/-- Each iterated integral in the two-dimensional boundary theorem has the
source Darboux value. All derivative and continuity facts follow from C¹. -/
theorem horizontal_stokes_darboux (P : (ℝ × ℝ) → ℝ) (hP : ContDiff ℝ 1 P) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => triangleCoefficient (extDeriv (horizontalForm P)) id (x, y)) id
      0 (1 - x) (P (x, 0) - P (x, 1 - x))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..(1 - x),
        triangleCoefficient (extDeriv (horizontalForm P)) id (x, y)) id 0 1
      (chainIntegral (horizontal P) (triangleBoundary id)) := by
  have he : triangleCoefficient (extDeriv (horizontalForm P)) id =
      fun p => -fderiv ℝ P p (0, 1) :=
    funext (triangleCoefficient_horizontal P (hP.differentiable (by norm_num)))
  have hc : Continuous (triangleCoefficient (extDeriv (horizontalForm P)) id) := by
    rw [he]
    exact ((hP.continuous_fderiv (by norm_num)).clm_apply continuous_const).neg
  obtain ⟨hi, ho⟩ := triangle_darboux_of_continuous _ hc
  constructor
  · intro x hx
    convert hi x hx using 1
    rw [he, horizontal_slice P hP]
  · rw [← horizontal_stokes P hP]
    exact ho

/-- Pullback commutes with actual path integration when both maps have genuine
derivatives on the parameter interval. -/
theorem pathIntegral_pullback (ω : Form 1 F) (S : E → F) (p : ℝ → E)
    (hS : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ S (p t))
    (hp : ∀ t ∈ uIcc (0 : ℝ) 1, DifferentiableAt ℝ p t) :
    pathIntegral (fromAlternating ω) (S ∘ p) =
      pathIntegral (fromAlternating (pullback ω S)) p := by
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [coefficient, fromAlternating_apply, pullback_apply]
  rw [((hS t ht).hasFDerivAt.comp_hasDerivAt t (hp t ht).hasDerivAt).deriv]
  rfl

/-- The three actual boundary restrictions satisfy the pullback comparison. -/
theorem triangleBoundary_integral_pullback (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hS : Differentiable ℝ S) :
    chainIntegral (fromAlternating ω) (triangleBoundary S) =
      chainIntegral (fromAlternating (pullback ω S)) (triangleBoundary id) := by
  have hb : Differentiable ℝ (fun t : ℝ => (t, (0 : ℝ))) := by fun_prop
  have hv : Differentiable ℝ (fun t : ℝ => ((0 : ℝ), t)) := by fun_prop
  have hd : Differentiable ℝ (fun t : ℝ => (1 - t, t)) := by fun_prop
  simp only [triangleBoundary, map_add, map_sub, chainIntegral_path]
  have hbd := pathIntegral_pullback ω S _ (fun t _ => hS _) (fun t _ => hd t)
  have hbv := pathIntegral_pullback ω S _ (fun t _ => hS _) (fun t _ => hv t)
  have hbb := pathIntegral_pullback ω S _ (fun t _ => hS _) (fun t _ => hb t)
  simpa only [Function.comp_def, id_eq] using congrArg₂ (· + ·)
    (congrArg₂ (· - ·) hbd hbv) hbb

@[simp] theorem fromAlternating_horizontal (P : (ℝ × ℝ) → ℝ) :
    fromAlternating (horizontalForm P) = horizontal P := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- A nonlinear parameterized triangle boundary theorem when the pulled-back
1-form has no `dy` component. The hypothesis specifies a form coefficient,
not an integral or a Stokes identity. No injectivity is needed. -/
theorem horizontal_pullback_stokes (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (P : (ℝ × ℝ) → ℝ) (hω : Differentiable ℝ ω) (hS : ContDiff ℝ 2 S)
    (hP : ContDiff ℝ 1 P) (he : pullback ω S = horizontalForm P) :
    formIntegral (extDeriv ω) S =
      chainIntegral (fromAlternating ω) (triangleBoundary S) := by
  have hc : triangleCoefficient (extDeriv ω) S =
      triangleCoefficient (extDeriv (horizontalForm P)) id := by
    funext p
    have h := exterior_pullback ω S p (hω _) hS.contDiffAt
    rw [he] at h
    simp only [triangleCoefficient]
    rw [← h]
    simp [pullback_apply]
  rw [formIntegral, hc, ← formIntegral, horizontal_stokes P hP,
    triangleBoundary_integral_pullback ω S (hS.differentiable (by norm_num)), he,
    fromAlternating_horizontal]

/-- A genuinely nonlinear parameterization, allowed to degenerate on `y=0`. -/
def verticalSquare (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 ^ 2)

theorem verticalSquare_smooth : ContDiff ℝ 2 verticalSquare := by
  unfold verticalSquare
  fun_prop

/-- The derivative is computed, rather than supplied as structure data. -/
theorem verticalSquare_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt verticalSquare
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  simpa [verticalSquare] using!
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2)

/-- Pulling back `-y dx` along `(x,y) ↦ (x,y²)` gives `-y² dx`. -/
theorem verticalSquare_pullback :
    pullback (horizontalForm (fun p => -p.2)) verticalSquare =
      horizontalForm (fun p => -(p.2 ^ 2)) := by
  funext p
  ext v
  simp [pullback_apply, horizontalForm_apply, (verticalSquare_hasFDerivAt p).fderiv,
    verticalSquare]

/-- The actual exterior pullback coefficient is the nonconstant function `2y`. -/
theorem verticalSquare_coefficient (p : ℝ × ℝ) :
    triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare p =
      2 * p.2 := by
  have hω : Differentiable ℝ (horizontalForm (fun p => -p.2)) := by
    unfold horizontalForm
    fun_prop
  have h := exterior_pullback (horizontalForm (fun p => -p.2)) verticalSquare p
    (hω _) verticalSquare_smooth.contDiffAt
  rw [verticalSquare_pullback] at h
  rw [triangleCoefficient, ← h,
    exterior_horizontal _ p (by fun_prop)]
  have hd := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).fun_neg.fderiv
  rw [hd]
  simp

/-- A nonzero two-dimensional nonlinear simplex computation: both the surface
integral of the exterior derivative and the actual boundary integral are `1/3`. -/
theorem verticalSquare_integrals :
    formIntegral (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare = 1 / 3 ∧
    chainIntegral (horizontal (fun p => -p.2)) (triangleBoundary verticalSquare) = 1 / 3 := by
  have hi : formIntegral (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare =
      1 / 3 := by
    unfold formIntegral triangleIntegral
    simp only [verticalSquare_coefficient]
    have hs (x : ℝ) : (∫ y in 0..(1 - x), 2 * y) = (1 - x) ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    simp_rw [hs]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2)]
    norm_num [integral_pow]
  constructor
  · exact hi
  · rw [← fromAlternating_horizontal]
    rw [← horizontal_pullback_stokes (horizontalForm (fun p => -p.2)) verticalSquare
      (fun p => -(p.2 ^ 2)) (by unfold horizontalForm; fun_prop) verticalSquare_smooth
      (by fun_prop) verticalSquare_pullback]
    exact hi

/-- The nonlinear example also has source Darboux values at each integration
stage; the final value is not a default-zero Bochner integral. -/
theorem verticalSquare_darboux :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2)))
        verticalSquare (x, y)) id 0 (1 - x) ((1 - x) ^ 2)) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..(1 - x),
        triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2)))
          verticalSquare (x, y)) id 0 1 (1 / 3) := by
  have hc : Continuous
      (triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare) := by
    have he := funext verticalSquare_coefficient
    rw [he]
    fun_prop
  obtain ⟨hi, ho⟩ := triangle_darboux_of_continuous _ hc
  constructor
  · intro x hx
    convert hi x hx using 1
    simp only [verticalSquare_coefficient]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  · exact verticalSquare_integrals.1 ▸ ho

/-- The literal zero extension used in Rudin's Example 10.4. Its enclosing
cell is the unit square, and it retains the values on the closed triangle. -/
def triangleZeroExtension (f : (ℝ × ℝ) → ℝ) : (ℝ × ℝ) → ℝ :=
  triangle.indicator f

/-- A cut at `c` preserves ordinary Riemann integrability. The possible jump
at `c` is handled by the proved almost-everywhere continuity criterion. -/
theorem cut_darboux (f : ℝ → ℝ) (hf : Continuous f) {c : ℝ} (hc : c ∈ Icc 0 1) :
    StieltjesPrototype.HasDarbouxRSIntegral ((Iic c).indicator f) id 0 1
      (∫ y in 0..c, f y) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1))
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by norm_num))
  have hi := RiemannIntegrability.hasDarbouxRSIntegral_of_ae_continuousWithinAt
    (f := (Iic c).indicator f) (M := M) (show (0 : ℝ) ≤ 1 by norm_num)
    (by
      intro y hy
      by_cases h : y ∈ Iic c
      · simpa only [indicator_of_mem h, Real.norm_eq_abs] using hM y hy
      · simpa only [indicator_of_notMem h, abs_zero] using hM0)
    (by
      have hne : ∀ᵐ y : ℝ ∂volume, y ≠ c := by
        rw [ae_iff]
        simp
      apply ae_restrict_of_ae
      filter_upwards [hne] with y hy
      apply ContinuousAt.continuousWithinAt
      rcases lt_or_gt_of_ne hy with hlt | hgt
      · apply hf.continuousAt.congr_of_eventuallyEq
        filter_upwards [isOpen_Iio.mem_nhds hlt] with z hz
        exact indicator_of_mem (show z ∈ Iic c from hz.le) f
      · apply continuousAt_const.congr_of_eventuallyEq
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with z hz
        exact indicator_of_notMem (show z ∉ Iic c from not_le.mpr hz) f)
  have he : (∫ y in 0..1, (Iic c).indicator f y) = ∫ y in 0..c, f y :=
    intervalIntegral.integral_indicator hc
  rwa [he] at hi

/-- The closed zero-extension slice agrees with the cut function on the full
unit integration interval, including both endpoints. -/
theorem triangleZeroExtension_slice (f : (ℝ × ℝ) → ℝ) {x : ℝ}
    (hx : x ∈ Icc 0 1) {y : ℝ} (hy : y ∈ Icc 0 1) :
    triangleZeroExtension f (x, y) =
      (Iic (1 - x)).indicator (fun y => f (x, y)) y := by
  have hm : (x, y) ∈ triangle ↔ y ∈ Iic (1 - x) := by
    simp only [triangle, mem_ofPred_eq, mem_Iic]
    constructor
    · intro h; linarith [h.2.2]
    · intro h; exact ⟨hx.1, hy.1, by linarith⟩
  simp only [triangleZeroExtension, indicator, hm]

/-- Equality of the literal source zero-extension integral and the variable-
bound slice integral; no omitted endpoint convention is used. -/
theorem triangleZeroExtension_integral (f : (ℝ × ℝ) → ℝ) {x : ℝ}
    (hx : x ∈ Icc 0 1) :
    (∫ y in 0..1, triangleZeroExtension f (x, y)) =
      ∫ y in 0..(1 - x), f (x, y) := by
  calc
    _ = ∫ y in 0..1, (Iic (1 - x)).indicator (fun y => f (x, y)) y := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply triangleZeroExtension_slice f hx
      simpa using hy
    _ = _ := intervalIntegral.integral_indicator ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- Comparison with the literal zero-extension Riemann convention in Example
10.4. Every row and the outer integration on the unit square have Darboux
values. The coefficient is assumed ambient continuous. This proves the order
`dy` then `dx`. `triangleIntegral_swap` below proves equality with the other
order for these ambient continuous coefficients. -/
theorem triangle_source_riemann (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => triangleZeroExtension f (x, y)) id 0 1
      (∫ y in 0..(1 - x), f (x, y))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..1, triangleZeroExtension f (x, y)) id 0 1
      (triangleIntegral f) := by
  constructor
  · intro x hx
    apply StieltjesIntegralLaws.hasDarbouxRSIntegral_congr (by norm_num)
      (cut_darboux (fun y => f (x, y))
        (hf.comp (continuous_const.prodMk continuous_id))
        ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    intro y hy
    exact (triangleZeroExtension_slice f hx hy).symm
  · apply StieltjesIntegralLaws.hasDarbouxRSIntegral_congr (by norm_num)
      (triangle_darboux_of_continuous f hf).2
    intro x hx
    exact (triangleZeroExtension_integral f hx).symm

/-- The nonlinear example satisfies the literal source convention, and its
source value equals the integral over its actual parameterized boundary. -/
theorem verticalSquare_source_boundary :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..1,
        triangleZeroExtension
          (triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare)
          (x, y)) id 0 1
      (chainIntegral (horizontal (fun p => -p.2)) (triangleBoundary verticalSquare)) := by
  have hc : Continuous
      (triangleCoefficient (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare) := by
    have he := funext verticalSquare_coefficient
    rw [he]
    fun_prop
  have h := (triangle_source_riemann _ hc).2
  change StieltjesPrototype.HasDarbouxRSIntegral _ _ _ _
    (formIntegral (extDeriv (horizontalForm (fun p => -p.2))) verticalSquare) at h
  rw [verticalSquare_integrals.1] at h
  rw [verticalSquare_integrals.2]
  exact h

/-- The parameter triangle is measurable, with all three faces included. -/
theorem triangle_isClosed : IsClosed triangle := by
  change IsClosed ({p : ℝ × ℝ | 0 ≤ p.1} ∩
    ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1}))
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

/-- The discontinuous zero extension is genuinely integrable on the unit cell. -/
theorem triangleZeroExtension_integrable (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (triangleZeroExtension f) (Icc 0 1 ×ˢ Icc 0 1) := by
  exact ((hf.continuousOn).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).indicator triangle_isClosed.measurableSet

/-- The zero extension respects coordinate interchange pointwise, including
points on the sloping face. -/
theorem triangleZeroExtension_swap (f : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) :
    triangleZeroExtension (f ∘ Prod.swap) p = triangleZeroExtension f p.swap := by
  have hm : p ∈ triangle ↔ p.swap ∈ triangle := by
    simp only [triangle, mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
    simp only [add_comm p.1 p.2, and_left_comm]
  by_cases hp : p ∈ triangle
  · simp only [triangleZeroExtension, indicator_of_mem hp,
      indicator_of_mem (hm.mp hp), Function.comp_apply]
  · simp only [triangleZeroExtension, indicator_of_notMem hp,
      indicator_of_notMem (mt hm.mpr hp)]

/-- On continuous ambient coefficients, the two integration orders agree.
This is a proved two-dimensional Fubini result for the source zero extension;
it does not assert the arbitrary-dimensional exercise. -/
theorem triangleIntegral_swap (f : (ℝ × ℝ) → ℝ) (hf : Continuous f) :
    triangleIntegral f = triangleIntegral (f ∘ Prod.swap) := by
  have hs (g : (ℝ × ℝ) → ℝ) : triangleIntegral g =
      ∫ x in 0..1, ∫ y in 0..1, triangleZeroExtension g (x, y) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact (triangleZeroExtension_integral g (by simpa using hx)).symm
  rw [hs f, hs (f ∘ Prod.swap)]
  have hi : IntegrableOn (triangleZeroExtension f)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) :=
    (triangleZeroExtension_integrable f hf).mono_set
      (Set.prod_mono (by simp [uIoc_of_le]; exact Ioc_subset_Icc_self)
        (by simp [uIoc_of_le]; exact Ioc_subset_Icc_self))
  have h := intervalIntegral_intervalIntegral_swap
    (F := fun x y => triangleZeroExtension f (x, y)) hi
  simp_rw [triangleZeroExtension_swap]
  exact h

end Rudin.Support.SimplexIntegration
