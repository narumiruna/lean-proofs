module

public import Math.Rudin.Support.SmoothChainIntegration
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Euclidean flux on positive smooth regions

Sources: Rudin Sections 10.31, 10.46, 10.49–10.51.

Divergence is the trace of the actual Fréchet derivative. The normal is the
Cartesian determinant cofactor vector, and area is the square root of the
Gram determinant. Their comparison includes rank-deficient faces. Positive
regions are finite unions of injective C² simplex images with positive
interior Jacobians and disjoint interiors. Boundary Jacobians may vanish.

The volume-image comparison uses the analytic change-of-variables theorem.
Null interfaces follow from the inverse function theorem and differentiable
images of null sets. The signed boundary is the frozen ordinary chain
boundary. The divergence theorem is derived from local simplex Stokes.
Functional localization proves cancellation for fields zero on the actual
frontier. Signed cofactors have the negative inward barycentric pairing;
regular normal rays leave the nonlinear cell. At nonzero-area singular faces,
the unit normals are limits of actual outward normals of homothetically
contracted interior faces. These contractions remain positive smooth cells.
-/

@[expose] public section
noncomputable section
namespace Rudin.Support.EuclideanFlux

open Set MeasureTheory
open scoped RealInnerProductSpace
open SimplexIntegration SmoothChains SmoothChainIntegration

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def divergence {n : ℕ} (F : Space n → Space n) (x : Space n) : ℝ :=
  ∑ i, ⟪EuclideanSpace.single i 1, fderiv ℝ F x (EuclideanSpace.single i 1)⟫

def laplacian {n : ℕ} (h : Space n → ℝ) : Space n → ℝ :=
  divergence (gradient h)

theorem gradient_contDiffOn {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {h : Space n → ℝ} (hh : ContDiffOn ℝ 2 h U) :
    ContDiffOn ℝ 1 (gradient h) U := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.contDiff.comp_contDiffOn
    (hh.fderiv_of_isOpen hU (by norm_num))

/-- Product rule for the trace of the actual Fréchet derivative. -/
theorem divergence_smul {n : ℕ} {g : Space n → ℝ} {F : Space n → Space n}
    {x : Space n} (hg : DifferentiableAt ℝ g x) (hF : DifferentiableAt ℝ F x) :
    divergence (fun y => g y • F y) x =
      g x * divergence F x + ⟪gradient g x, F x⟫ := by
  unfold divergence
  rw [(hg.hasFDerivAt.fun_smul hF.hasFDerivAt).fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, inner_add_right, inner_smul_right,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb := (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner (gradient g x) (F x)
  simp only [EuclideanSpace.basisFun_apply, inner_gradient_left] at hb
  rw [hb, inner_gradient_left]

/-- Rudin's product identity in every dimension, including dimensions zero and one. -/
theorem divergence_mul_gradient {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {g h : Space n → ℝ} (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U)
    {x : Space n} (hx : x ∈ U) :
    divergence (fun y => g y • gradient h y) x =
      g x * laplacian h x + ⟪gradient g x, gradient h x⟫ := by
  exact divergence_smul
    ((hg x hx).contDiffAt (hU.mem_nhds hx) |>.differentiableAt (by norm_num))
    (((gradient_contDiffOn hU hh) x hx).contDiffAt (hU.mem_nhds hx)
      |>.differentiableAt (by norm_num))

/-- Contraction of Cartesian volume with the actual vector field. -/
def fluxForm {n : ℕ} (F : Space (n+1) → Space (n+1)) :
    Form n (Space (n+1)) := fun x => (parameterVolume (n+1)).curryLeft (F x)

theorem fluxForm_contDiffOn {n : ℕ} {F : Space (n+1) → Space (n+1)}
    {U : Set (Space (n+1))} (hF : ContDiffOn ℝ 1 F U) :
    ContDiffOn ℝ 1 (fluxForm F) U :=
  (parameterVolume (n+1)).curryLeft.contDiff.comp_contDiffOn hF

theorem volume_update_basis {n : ℕ} (i : Fin n) (x : Space n) :
    parameterVolume n (Function.update (fun j => EuclideanSpace.single j 1) i x) = x i := by
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) i (fun j => x j)
  have he : (∑ k, x k • (1 : Matrix (Fin n) (Fin n) ℝ) k) = (fun k => x k) := by
    ext k
    simp [Matrix.one_apply, Pi.smul_apply]
  rw [he, Matrix.det_one, smul_eq_mul, mul_one] at h
  change Matrix.det (fun j k => (Function.update (fun j => EuclideanSpace.single j 1) i x j) k) = x i
  rw [← h]
  congr 1
  ext j k
  change (Function.update (fun j => EuclideanSpace.single j 1) i x j) k =
    (Function.update (fun j k : Fin n => if j = k then (1 : ℝ) else 0)
      i (fun k => x k) j) k
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    simp [eq_comm]

theorem top_form_eq {n : ℕ} (A : Space n [⋀^Fin n]→L[ℝ] ℝ) :
    A = A (fun i => EuclideanSpace.single i 1) • parameterVolume n := by
  have ha := A.toAlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hv := (parameterVolume n).toAlternatingMap.eq_smul_basis_det
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb : ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
      (fun i => EuclideanSpace.single i 1) := by
    funext i
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ i
  rw [hb] at ha hv
  change A.toAlternatingMap = A (fun i => EuclideanSpace.single i 1) •
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det at ha
  change (parameterVolume n).toAlternatingMap =
    parameterVolume n (fun i => EuclideanSpace.single i 1) •
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det at hv
  rw [parameterVolume_basis, one_smul] at hv
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change A.toAlternatingMap = A (fun i => EuclideanSpace.single i 1) •
    (parameterVolume n).toAlternatingMap
  rw [hv]
  exact ha

/-- The exterior derivative of the flux form is divergence times Cartesian volume. -/
theorem extDeriv_fluxForm {n : ℕ} {F : Space (n+1) → Space (n+1)}
    {x : Space (n+1)} (hF : DifferentiableAt ℝ F x) :
    extDeriv (fluxForm F) x = divergence F x • parameterVolume (n+1) := by
  rw [top_form_eq (extDeriv (fluxForm F) x)]
  congr 1
  unfold extDeriv fluxForm
  have hd := ((parameterVolume (n+1)).curryLeft.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
  rw [← (parameterVolume (n+1)).map_insertNth, Fin.insertNth_removeNth,
    volume_update_basis]
  simp [EuclideanSpace.inner_single_left]

theorem standardSimplex_convex (n : ℕ) : Convex ℝ (standardSimplex n) :=
  (MultivariateRiemann.piSimplex_convex n).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

theorem ae_interior_standardSimplex (n : ℕ) :
    ∀ᵐ u : Space n ∂volume.restrict (standardSimplex n),
      u ∈ interior (standardSimplex n) := by
  have hn : ∀ᵐ u : Space n ∂volume, u ∉ frontier (standardSimplex n) := by
    rw [ae_iff]
    simpa using (standardSimplex_convex n).addHaar_frontier volume
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (standardSimplex_isCompact n).measurableSet] with u hf hu
  by_contra hi
  exact hf ⟨subset_closure hu, hi⟩

/-- Change of variables is proved for the geometric image measure.
The Jacobian may vanish on the source boundary, as permitted in Section 10.31. -/
theorem simplex_volume_integral {n : ℕ} (S : Simplex n (Space n))
    (hinj : InjOn S.val (standardSimplex n))
    (hdet : ∀ u ∈ interior (standardSimplex n), 0 ≤ (fderiv ℝ S.val u).det)
    (f : Space n → ℝ) :
    (∫ x in S.val '' standardSimplex n, f x) =
      simplexIntegral (fun x => f x • parameterVolume n) S.toSmooth := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (standardSimplex_isCompact n).measurableSet
    (fun u hu => (S.differentiableAt hu).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply integral_congr_ae
  filter_upwards [ae_interior_standardSimplex n] with u hu
  simp only [simplexCoefficient, pullback_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, abs_of_nonneg (hdet u hu)]
  change (fderiv ℝ S.val u).det * f (S.val u) =
    f (S.val u) * parameterVolume n (fun i => fderiv ℝ S.val u (EuclideanSpace.single i 1))
  rw [alternating_linear (parameterVolume n) (fderiv ℝ S.val u), parameterVolume_basis]
  ring

/-- Oriented normal from the determinant cofactors, independent of any field. -/
def normal {n : ℕ} (v : Fin n → Space (n+1)) : Space (n+1) :=
  ∑ i, parameterVolume (n+1) (Fin.cons (EuclideanSpace.single i 1) v) •
    EuclideanSpace.single i 1

theorem normal_inner {n : ℕ} (v : Fin n → Space (n+1)) (x : Space (n+1)) :
    ⟪normal v, x⟫ = parameterVolume (n+1) (Fin.cons x v) := by
  unfold normal
  simp only [sum_inner, inner_smul_left, EuclideanSpace.inner_single_left,
    map_one, one_mul]
  have hx := (EuclideanSpace.basisFun (Fin (n+1)) ℝ).sum_repr x
  simp only [OrthonormalBasis.repr_apply_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul] at hx
  conv_rhs => rw [← hx]
  change _ = (parameterVolume (n+1)).curryLeft (∑ i, x i • EuclideanSpace.single i 1) v
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [starRingEnd_apply, star_trivial]
  change parameterVolume (n+1) (Fin.cons (EuclideanSpace.single i 1) v) * x i =
    x i * parameterVolume (n+1) (Fin.cons (EuclideanSpace.single i 1) v)
  ring

theorem normal_orthogonal {n : ℕ} (v : Fin n → Space (n+1)) (i : Fin n) :
    ⟪normal v, v i⟫ = 0 := by
  rw [normal_inner]
  exact (parameterVolume (n+1)).map_eq_zero_of_eq _
    (show (Fin.cons (v i) v : Fin (n+1) → Space (n+1)) 0 =
      (Fin.cons (v i) v : Fin (n+1) → Space (n+1)) i.succ from rfl)
    (Fin.succ_ne_zero i).symm

/-- The Cartesian determinant squared is the full Gram determinant. -/
theorem volume_sq_eq_gram {n : ℕ} (v : Fin n → Space n) :
    (parameterVolume n v) ^ 2 = (Matrix.gram ℝ v).det := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => v i j
  have hm : Matrix.gram ℝ v = A * A.transpose := by
    ext i j
    change ⟪v i, v j⟫ = ∑ k, v i k * v j k
    simp [PiLp.inner_apply, mul_comm]
  rw [hm, Matrix.det_mul, Matrix.det_transpose]
  change A.det ^ 2 = A.det * A.det
  ring

/-- An independent tangent frame has a nonzero determinant normal. -/
theorem normal_ne_zero {n : ℕ} {v : Fin n → Space (n+1)}
    (hv : LinearIndependent ℝ v) : normal v ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hv
    (by simp : n < Module.finrank ℝ (Space (n+1)))
  intro hn
  have hz : parameterVolume (n+1) (Fin.cons x v) = 0 := by
    rw [← normal_inner, hn, inner_zero_left]
  have hh := volume_sq_eq_gram (Fin.cons x v)
  rw [hz, zero_pow (by decide)] at hh
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hx) hh.symm

/-- The cofactor normal has the geometric Gram area density, including singular frames. -/
theorem normal_norm_sq {n : ℕ} (v : Fin n → Space (n+1)) :
    ‖normal v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  have hfull := volume_sq_eq_gram (Fin.cons (normal v) v)
  rw [← normal_inner, real_inner_self_eq_norm_sq] at hfull
  have hd : (Matrix.gram ℝ (Fin.cons (normal v) v)).det =
      ‖normal v‖ ^ 2 * (Matrix.gram ℝ v).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.gram, normal_orthogonal, Matrix.submatrix]
  rw [hd] at hfull
  by_cases hn : normal v = 0
  · have hv : ¬LinearIndependent ℝ v := fun hv => normal_ne_zero hv hn
    have hg : (Matrix.gram ℝ v).det = 0 := by
      by_contra h
      exact hv (Matrix.det_gram_ne_zero_iff_linearIndependent.mp h)
    simp [hn, hg]
  · have hn' : ‖normal v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hn)
    apply mul_left_cancel₀ hn'
    nlinarith [hfull]

def areaDensity {n : ℕ} (v : Fin n → Space (n+1)) : ℝ :=
  Real.sqrt (Matrix.gram ℝ v).det

theorem areaDensity_eq_norm {n : ℕ} (v : Fin n → Space (n+1)) :
    areaDensity v = ‖normal v‖ := by
  rw [areaDensity, ← normal_norm_sq, Real.sqrt_sq (norm_nonneg _)]

def unitNormal {n : ℕ} (v : Fin n → Space (n+1)) : Space (n+1) :=
  if normal v = 0 then EuclideanSpace.single 0 1 else ‖normal v‖⁻¹ • normal v

theorem normal_eq_density_smul {n : ℕ} (v : Fin n → Space (n+1)) :
    normal v = areaDensity v • unitNormal v := by
  rw [areaDensity_eq_norm, unitNormal]
  split_ifs with h
  · simp [h]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

theorem flux_eq_normal_area {n : ℕ} (v : Fin n → Space (n+1)) (x : Space (n+1)) :
    parameterVolume (n+1) (Fin.cons x v) =
      ⟪x, unitNormal v⟫ * areaDensity v := by
  rw [← normal_inner, normal_eq_density_smul, inner_smul_left, real_inner_comm]
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem unitNormal_norm {n : ℕ} (v : Fin n → Space (n+1)) : ‖unitNormal v‖ = 1 := by
  rw [unitNormal]
  split_ifs with h
  · simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem unitNormal_orthogonal {n : ℕ} (v : Fin n → Space (n+1))
    (h : normal v ≠ 0) (i : Fin n) : ⟪unitNormal v, v i⟫ = 0 := by
  simp [unitNormal, h, inner_smul_left, normal_orthogonal]

theorem normal_apply {n : ℕ} (v : Fin n → Space (n+1)) (i : Fin (n+1)) :
    normal v i = parameterVolume (n+1) (Fin.cons (EuclideanSpace.single i 1) v) := by
  simp [normal, Pi.single_apply]

theorem cartesianVolume_apply {n : ℕ} (v : Fin n → Space n) :
    parameterVolume n v = Matrix.det (fun i j => v i j) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The general cofactor normal specializes to the three Jacobian minors in (129). -/
theorem normal_three (a b : Space 3) :
    (normal ![a,b]) 0 = a 1 * b 2 - a 2 * b 1 ∧
    (normal ![a,b]) 1 = a 2 * b 0 - a 0 * b 2 ∧
    (normal ![a,b]) 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [normal_apply, cartesianVolume_apply, Matrix.det_fin_three]
  ring

/-- Actual tangent vectors of a parameterized hypersurface. -/
def tangentFrame {n : ℕ} (S : Simplex n (Space (n+1))) (u : Space n) :
    Fin n → Space (n+1) := fun i => fderiv ℝ S.val u (EuclideanSpace.single i 1)

/-- Geometric surface integration, with the Gram area element. -/
def surfaceIntegral {n : ℕ} (S : Simplex n (Space (n+1)))
    (f : Space (n+1) → Space (n+1) → ℝ) : ℝ :=
  ∫ u in standardSimplex n,
    f (S.val u) (unitNormal (tangentFrame S u)) * areaDensity (tangentFrame S u)

/-- The surface flux density equals the pullback of contraction with volume. -/
theorem surface_flux_coefficient {n : ℕ} (S : Simplex n (Space (n+1)))
    (F : Space (n+1) → Space (n+1)) (u : Space n) :
    ⟪F (S.val u), unitNormal (tangentFrame S u)⟫ * areaDensity (tangentFrame S u) =
      simplexCoefficient (fluxForm F) S.toSmooth u := by
  exact (flux_eq_normal_area (tangentFrame S u) (F (S.val u))).symm

theorem surface_flux_integrable {n : ℕ} (S : Simplex n (Space (n+1)))
    (F : Space (n+1) → Space (n+1))
    (hF : ContinuousOn F (S.val '' standardSimplex n)) :
    IntegrableOn (fun u => ⟪F (S.val u), unitNormal (tangentFrame S u)⟫ *
      areaDensity (tangentFrame S u)) (standardSimplex n) := by
  simp_rw [surface_flux_coefficient]
  exact integral_integrable (fluxForm F) S
    ((parameterVolume (n+1)).curryLeft.continuous.comp_continuousOn hF)

theorem surface_flux_eq_integral {n : ℕ} (S : Simplex n (Space (n+1)))
    (F : Space (n+1) → Space (n+1)) :
    surfaceIntegral S (fun x ν => ⟪F x, ν⟫) = simplexIntegral (fluxForm F) S.toSmooth := by
  unfold surfaceIntegral simplexIntegral
  simp_rw [surface_flux_coefficient]

/-- All coordinate-order source Riemann values for the geometric flux density. -/
theorem surface_flux_source {n : ℕ} (S : Simplex n (Space (n+1)))
    (F : Space (n+1) → Space (n+1))
    (hF : ContinuousOn F (S.val '' standardSimplex n)) (σ : Equiv.Perm (Fin n)) :
    MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension
        ((fun u => ⟪F (S.val u), unitNormal (tangentFrame S u)⟫ *
          areaDensity (tangentFrame S u)) ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘
        MultivariateRiemann.coordinatePermutation σ)
      (surfaceIntegral S (fun x ν => ⟪F x, ν⟫)) := by
  simp_rw [surface_flux_coefficient, surface_flux_eq_integral]
  exact MultivariateRiemann.simplexIntegral_source (fluxForm F) S.toSmooth
    ((parameterVolume (n+1)).curryLeft.continuous.comp_continuousOn hF) σ

/-- Continuity of divergence follows from continuity of the actual first derivative. -/
theorem divergence_continuousOn {n : ℕ} {F : Space n → Space n}
    {U : Set (Space n)} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    ContinuousOn (divergence F) U := by
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.inner
    ((hF.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const)

/-- Geometric volume divergence equals geometric signed face flux for a positive,
injective smooth simplex. The divergence theorem is derived, not assumed. -/
theorem simplex_divergence {n : ℕ} (S : Simplex (n+1) (Space (n+1)))
    (hinj : InjOn S.val (standardSimplex (n+1)))
    (hdet : ∀ u ∈ interior (standardSimplex (n+1)), 0 ≤ (fderiv ℝ S.val u).det)
    {U : Set (Space (n+1))} (hU : IsOpen U)
    (hS : S.val '' standardSimplex (n+1) ⊆ U)
    (F : Space (n+1) → Space (n+1)) (hF : ContDiffOn ℝ 1 F U) :
    (∫ x in S.val '' standardSimplex (n+1), divergence F x) =
      ∑ i : Fin (n+2), (-1 : ℝ) ^ (i : ℕ) *
        surfaceIntegral (S.face i) (fun x ν => ⟪F x, ν⟫) := by
  rw [simplex_volume_integral S hinj hdet]
  have he : simplexIntegral (fun x => divergence F x • parameterVolume (n+1)) S.toSmooth =
      simplexIntegral (extDeriv (fluxForm F)) S.toSmooth := by
    apply setIntegral_congr_fun (standardSimplex_isCompact (n+1)).measurableSet
    intro u hu
    simp only [simplexCoefficient, pullback_apply, Simplex.toSmooth]
    rw [extDeriv_fluxForm (((hF _ (hS ⟨u, hu, rfl⟩)).contDiffAt
      (hU.mem_nhds (hS ⟨u, hu, rfl⟩))).differentiableAt (by norm_num))]
  rw [he]
  have hs := SimplexStokes.smoothChains_stokes (fluxForm F) S hU
    (fluxForm_contDiffOn hF) hS
  rw [integral_simplex, boundary_simplex, map_sum] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integral_simplex, surface_flux_eq_integral]
  simp [zsmul_eq_mul]

/-- The precise positive parameterization in Rudin 10.31. Boundary derivatives
may be singular. Injectivity is required only on the closed source simplex. -/
structure PositiveSimplex (n : ℕ) where
  simplex : Simplex n (Space n)
  injective : InjOn simplex.val (standardSimplex n)
  positive : ∀ u ∈ interior (standardSimplex n), 0 < (fderiv ℝ simplex.val u).det

namespace PositiveSimplex

def carrier {n : ℕ} (S : PositiveSimplex n) : Set (Space n) :=
  S.simplex.val '' standardSimplex n

theorem contDiffAt {n : ℕ} (S : PositiveSimplex n) {u : Space n}
    (hu : u ∈ standardSimplex n) : ContDiffAt ℝ 2 S.simplex.val u := by
  obtain ⟨U, hU, hsub, hS⟩ := S.simplex.property
  exact (hS u (hsub hu)).contDiffAt (hU.mem_nhds (hsub hu))

theorem compact {n : ℕ} (S : PositiveSimplex n) : IsCompact S.carrier :=
  (standardSimplex_isCompact n).image_of_continuousOn
    (fun _ hu => (S.contDiffAt hu).continuousAt.continuousWithinAt)

theorem interior_image {n : ℕ} (S : PositiveSimplex n) {u : Space n}
    (hu : u ∈ interior (standardSimplex n)) : S.simplex.val u ∈ interior S.carrier := by
  have hd := (S.contDiffAt (interior_subset hu)).hasStrictFDerivAt (by norm_num)
  have hs : Function.Surjective (fderiv ℝ S.simplex.val u) :=
    (LinearMap.equivOfDetNeZero _ (ne_of_gt (S.positive u hu))).surjective
  have hn := hd.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hs)
  apply mem_interior_iff_mem_nhds.mpr
  rw [← hn]
  exact Filter.image_mem_map (mem_interior_iff_mem_nhds.mp hu)

theorem frontier_subset_image {n : ℕ} (S : PositiveSimplex n) :
    frontier S.carrier ⊆ S.simplex.val '' frontier (standardSimplex n) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := S.compact.isClosed.frontier_subset hx
  refine ⟨u, ⟨subset_closure hu, ?_⟩, rfl⟩
  intro hi
  exact hx.2 (S.interior_image hi)

theorem frontier_null {n : ℕ} (S : PositiveSimplex n) : volume (frontier S.carrier) = 0 := by
  apply measure_mono_null S.frontier_subset_image
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
  · intro u hu
    exact ((S.contDiffAt ((standardSimplex_isCompact n).isClosed.frontier_subset hu)).differentiableAt
      (by norm_num)).differentiableWithinAt
  · exact (standardSimplex_convex n).addHaar_frontier volume

theorem interior_ae {n : ℕ} (S : PositiveSimplex n) :
    interior S.carrier =ᵐ[volume] S.carrier := by
  have hn : ∀ᵐ x : Space n ∂volume, x ∉ frontier S.carrier := by
    rw [ae_iff]
    simpa using S.frontier_null
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · exact fun h => interior_subset h
  · intro h
    by_contra hi
    exact hx ⟨subset_closure h, hi⟩

end PositiveSimplex

/-- Exactly a finite union of positive smooth simplex images with disjoint
interiors. There is no connectedness requirement and the empty union is allowed. -/
structure Region (n : ℕ) where
  count : ℕ
  cell : Fin count → PositiveSimplex n
  disjoint : Pairwise (fun i j => Disjoint (interior (cell i).carrier)
    (interior (cell j).carrier))

namespace Region

def carrier {n : ℕ} (R : Region n) : Set (Space n) := ⋃ i, (R.cell i).carrier

theorem compact {n : ℕ} (R : Region n) : IsCompact R.carrier :=
  isCompact_iUnion (fun i => (R.cell i).compact)

theorem integrableOn {n : ℕ} (R : Region n) {f : Space n → ℝ}
    (hf : ContinuousOn f R.carrier) : IntegrableOn f R.carrier :=
  hf.integrableOn_compact R.compact

/-- The geometric volume integral is the sum of cell integrals; zero-measure
interfaces are proved from differentiability, not supplied as an integral law. -/
theorem integral_cells {n : ℕ} (R : Region n) {f : Space n → ℝ}
    (hf : ContinuousOn f R.carrier) :
    (∫ x in R.carrier, f x) = ∑ i, ∫ x in (R.cell i).carrier, f x := by
  have ha : (⋃ i, interior (R.cell i).carrier) =ᵐ[volume] R.carrier := by
    have hh := ae_all_iff.mpr (fun i => (R.cell i).interior_ae)
    filter_upwards [hh] with x hx
    simp only [carrier, mem_iUnion]
    exact propext (exists_congr (fun i => Iff.of_eq (hx i)))
  rw [← setIntegral_congr_set ha]
  rw [integral_iUnion_fintype (fun _ => isOpen_interior.measurableSet) R.disjoint]
  · apply Finset.sum_congr rfl
    intro i _
    exact setIntegral_congr_set (R.cell i).interior_ae
  · intro i
    exact (R.integrableOn hf).mono_set
      (interior_subset.trans (subset_iUnion (fun i => (R.cell i).carrier) i))

/-- The positively oriented boundary is the sum of the ordinary signed faces,
exactly as in 10.31. Surface measure is the Gram density on each face. -/
def boundaryIntegral {n : ℕ} (R : Region (n+1))
    (f : Space (n+1) → Space (n+1) → ℝ) : ℝ :=
  ∑ c, ∑ i : Fin (n+2), (-1 : ℝ) ^ (i : ℕ) *
    surfaceIntegral ((R.cell c).simplex.face i) f

/-- The finite-chain divergence theorem on the complete source class. -/
theorem divergence_integral {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    (F : Space (n+1) → Space (n+1)) (hF : ContDiffOn ℝ 1 F U) :
    (∫ x in R.carrier, divergence F x) = R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) := by
  rw [R.integral_cells ((divergence_continuousOn hU hF).mono hR)]
  apply Finset.sum_congr rfl
  intro c _
  exact simplex_divergence (R.cell c).simplex (R.cell c).injective
    (fun u hu => ((R.cell c).positive u hu).le) hU
    ((subset_iUnion (fun c => (R.cell c).carrier) c).trans hR) F hF

/-- Each geometric face density is integrable, including singular faces. -/
theorem boundary_flux_integrable {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hR : R.carrier ⊆ U)
    {F : Space (n+1) → Space (n+1)} (hF : ContinuousOn F U)
    (c : Fin R.count) (i : Fin (n+2)) :
    IntegrableOn (fun u =>
      ⟪F (((R.cell c).simplex.face i).val u),
        unitNormal (tangentFrame ((R.cell c).simplex.face i) u)⟫ *
      areaDensity (tangentFrame ((R.cell c).simplex.face i) u)) (standardSimplex n) := by
  apply surface_flux_integrable
  apply hF.mono
  rintro x ⟨u, hu, rfl⟩
  apply hR
  apply mem_iUnion.mpr
  exact ⟨c, ⟨relabel i.succAbove u, relabel_mem i.succAbove hu, rfl⟩⟩

theorem boundaryIntegral_flux_sub {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hR : R.carrier ⊆ U)
    {F G : Space (n+1) → Space (n+1)}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) :
    R.boundaryIntegral (fun x ν => ⟪F x, ν⟫ - ⟪G x, ν⟫) =
      R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) -
        R.boundaryIntegral (fun x ν => ⟪G x, ν⟫) := by
  simp only [boundaryIntegral, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  unfold surfaceIntegral
  simp_rw [sub_mul]
  rw [integral_sub (R.boundary_flux_integrable hR hF c i)
    (R.boundary_flux_integrable hR hG c i), mul_sub]

/-- The region's volume chain uses its full nonlinear parameter maps. -/
def volumeChain {n : ℕ} (R : Region n) : Chain n (Space n) :=
  ∑ c, simplex (R.cell c).simplex

/-- The positive boundary is the ordinary boundary in the frozen quotient. -/
def positiveBoundary {n : ℕ} (R : Region (n+1)) : Oriented n (Space (n+1)) :=
  orientedBoundary n (project (n+1) R.volumeChain)

theorem boundary_flux_eq_orientedIntegral {n : ℕ} (R : Region (n+1))
    (F : Space (n+1) → Space (n+1)) :
    R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) =
      orientedIntegral (fluxForm F) R.positiveBoundary := by
  simp only [positiveBoundary, orientedBoundary_project, orientedIntegral_project,
    volumeChain, map_sum, boundary_simplex, map_zsmul, integral_simplex,
    boundaryIntegral, surface_flux_eq_integral, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]

/-- The normal after the canonical boundary sign is included. The area density
remains nonnegative; no signed or field-dependent area measure is used. -/
def positiveFaceNormal {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) (u : Space n) : Space (n+1) :=
  ((-1 : ℝ) ^ (i : ℕ)) • unitNormal (tangentFrame ((R.cell c).simplex.face i) u)

theorem positiveFaceNormal_norm {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) (u : Space n) : ‖R.positiveFaceNormal c i u‖ = 1 := by
  simp [positiveFaceNormal, norm_smul, unitNormal_norm]

/-- The signed normal is perpendicular to every actual face tangent whenever
the geometric area density is nonzero. -/
theorem positiveFaceNormal_orthogonal {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) (u : Space n)
    (ha : 0 < areaDensity (tangentFrame ((R.cell c).simplex.face i) u)) (j : Fin n) :
    ⟪R.positiveFaceNormal c i u, tangentFrame ((R.cell c).simplex.face i) u j⟫ = 0 := by
  have hn : normal (tangentFrame ((R.cell c).simplex.face i) u) ≠ 0 := by
    intro hz
    rw [areaDensity_eq_norm, hz, norm_zero] at ha
    exact lt_irrefl _ ha
  simp only [positiveFaceNormal, real_inner_smul_left, unitNormal_orthogonal _ hn,
    mul_zero]

theorem boundary_flux_eq_positive_normals {n : ℕ} (R : Region (n+1))
    (F : Space (n+1) → Space (n+1)) :
    R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) =
      ∑ c, ∑ i : Fin (n+2), ∫ u in standardSimplex n,
        ⟪F (((R.cell c).simplex.face i).val u), R.positiveFaceNormal c i u⟫ *
          areaDensity (tangentFrame ((R.cell c).simplex.face i) u) := by
  simp only [boundaryIntegral, surfaceIntegral, positiveFaceNormal, inner_smul_right]
  simp_rw [mul_assoc, integral_const_mul]

/-- Source Riemann witnesses for every cell volume term, with its actual geometric
Lebesgue value. The parameter Jacobian is not defined by the desired integral. -/
theorem cell_volume_source {n : ℕ} (R : Region n) {f : Space n → ℝ}
    (hf : ContinuousOn f R.carrier) (c : Fin R.count) (σ : Equiv.Perm (Fin n)) :
    MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension
        (simplexCoefficient (fun x => f x • parameterVolume n) (R.cell c).simplex.toSmooth ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (∫ x in (R.cell c).carrier, f x) := by
  unfold PositiveSimplex.carrier
  rw [simplex_volume_integral (R.cell c).simplex (R.cell c).injective
    (fun u hu => ((R.cell c).positive u hu).le)]
  exact MultivariateRiemann.simplexIntegral_source _ _
    ((hf.mono (subset_iUnion (fun c => (R.cell c).carrier) c)).smul continuousOn_const) σ

end Region


theorem integral_divergence_compact {n : ℕ} {F : Space n → Space n}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    (∫ x, divergence F x) = 0 := by
  have hi (i : Fin n) : Integrable
      (fun x => ⟪EuclideanSpace.single i 1, fderiv ℝ F x (EuclideanSpace.single i 1)⟫) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.inner ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · exact (hFc.fderiv_apply ℝ _).comp_left
        (g := fun v : Space n => ⟪EuclideanSpace.single i 1, v⟫) (by simp)
  unfold divergence
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  have hd : Integrable (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hFc.fderiv_apply ℝ _)
  have he := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun _ : Space n => (1 : ℝ)) (g := F) (v := EuclideanSpace.single i 1)
    (by simp)
    (by simpa using hd) (by simpa using hF.continuous.integrable_of_hasCompactSupport hFc)
    (fun _ _ => differentiableAt_const _) (fun x _ => hF.differentiable (by norm_num) x)
  simp only [one_smul, fderiv_const_apply, _root_.zero_apply, zero_smul,
    integral_zero, neg_zero] at he
  have hi' := (InnerProductSpace.toDual ℝ (Space n) (EuclideanSpace.single i 1)).integral_comp_comm hd
  simpa only [InnerProductSpace.toDual_apply_apply, he, inner_zero_right] using hi'

theorem contDiff_smul_of_tsupport {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {χ : Space n → ℝ} {F : Space n → Space n} (hχ : ContDiff ℝ 1 χ)
    (hs : tsupport χ ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ContDiff ℝ 1 (fun x => χ x • F x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul ((hF x hx).contDiffAt (hU.mem_nhds hx))
  · have he : χ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    apply (contDiffAt_const (c := (0 : Space n))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

theorem smooth_interior_cutoffs {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k)) ∧ (∀ k, tsupport (χ k) ⊆ K) ∧
      (∀ k x, χ k x ∈ Icc 0 1) ∧
      (∀ x ∈ interior K, Filter.Tendsto (fun k => χ k x) Filter.atTop (nhds 1)) := by
  obtain ⟨f, hs, hf, hb⟩ := isOpen_interior.exists_contDiff_support_eq (n := 1) (s := interior K)
  refine ⟨fun k x => 1 - (1 - f x)^k, ?_, ?_, ?_, ?_⟩
  · intro k
    exact contDiff_const.sub ((contDiff_const.sub hf).pow k)
  · intro k
    apply closure_minimal _ hK.isClosed
    intro x hx
    apply interior_subset
    rw [← hs]
    by_contra hn
    have hz : f x = 0 := Function.notMem_support.mp hn
    exact hx (by simp [hz])
  · intro k x
    obtain ⟨hx₀, hx₁⟩ := hb (mem_range_self x)
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ (by linarith : 0 ≤ 1 - f x) (by linarith))
    · have := pow_nonneg (by linarith : 0 ≤ 1 - f x) k
      linarith
  · intro x hx
    have hp : 0 < f x := lt_of_le_of_ne (hb (mem_range_self x)).1
      (Ne.symm (show f x ≠ 0 from (show x ∈ Function.support f from hs.symm ▸ hx)))
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ 1 - f x by linarith [(hb (mem_range_self x)).2]) (by linarith : 1 - f x < 1)
    simpa using tendsto_const_nhds.sub ht

namespace Region

/-- A globally smooth field supported in the region has zero total signed face flux.
This is a statement about the integration functional, not equality of quotient chains. -/
theorem boundary_flux_compact {n : ℕ} (R : Region (n+1))
    {F : Space (n+1) → Space (n+1)} (hF : ContDiff ℝ 1 F)
    (hs : tsupport F ⊆ R.carrier) :
    R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) = 0 := by
  rw [← R.divergence_integral isOpen_univ (subset_univ _) F hF.contDiffOn]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_divergence_compact hF (R.compact.of_isClosed_subset (isClosed_tsupport _) hs)
  · intro x hx
    have he := fderiv_of_notMem_tsupport ℝ (f := F) (x := x) (fun h => hx (hs h))
    simp [divergence, he]

/-- Functional cancellation on all internal faces. The only zero-boundary
assumption is on the topological frontier of the geometric union. -/
theorem boundary_flux_zero_of_frontier {n : ℕ} (R : Region (n+1))
    {U : Set (Space (n+1))} (hU : IsOpen U) (hR : R.carrier ⊆ U)
    {F : Space (n+1) → Space (n+1)} (hF : ContDiffOn ℝ 1 F U)
    (hz : ∀ x ∈ frontier R.carrier, F x = 0) :
    R.boundaryIntegral (fun x ν => ⟪F x, ν⟫) = 0 := by
  obtain ⟨χ, hχ, hs, hb, ht⟩ := smooth_interior_cutoffs R.compact
  let G : ℕ → Space (n+1) → Space (n+1) := fun k x => χ k x • F x
  have hG (k) : ContDiff ℝ 1 (G k) := contDiff_smul_of_tsupport hU (hχ k)
    ((hs k).trans hR) hF
  have hGs (k) : tsupport (G k) ⊆ R.carrier := (tsupport_smul_subset_left (χ k) F).trans (hs k)
  have hzero (k) : R.boundaryIntegral (fun x ν => ⟪G k x, ν⟫) = 0 :=
    R.boundary_flux_compact (hG k) (hGs k)
  have hlim (x) (hx : x ∈ R.carrier) :
      Filter.Tendsto (fun k => G k x) Filter.atTop (nhds (F x)) := by
    by_cases hi : x ∈ interior R.carrier
    · simpa [G] using (ht x hi).smul (tendsto_const_nhds (x := F x))
    · have hf := hz x ⟨subset_closure hx, hi⟩
      simp only [G, hf, smul_zero]
      exact tendsto_const_nhds
  have hface (c : Fin R.count) (i : Fin (n+2)) :
      Filter.Tendsto (fun k => surfaceIntegral ((R.cell c).simplex.face i)
        (fun x ν => ⟪G k x, ν⟫)) Filter.atTop
        (nhds (surfaceIntegral ((R.cell c).simplex.face i) (fun x ν => ⟪F x, ν⟫))) := by
    let S := (R.cell c).simplex.face i
    let q := fun u => ⟪F (S.val u), unitNormal (tangentFrame S u)⟫ * areaDensity (tangentFrame S u)
    have hqi : IntegrableOn q (SimplexIntegration.standardSimplex n) :=
      R.boundary_flux_integrable hR hF.continuousOn c i
    apply tendsto_integral_of_dominated_convergence (fun u => ‖q u‖)
    · intro k
      exact (R.boundary_flux_integrable (subset_univ _) (hG k).continuous.continuousOn c i).aestronglyMeasurable
    · exact hqi.norm
    · intro k
      apply Filter.Eventually.of_forall
      intro u
      change ‖⟪χ k (S.val u) • F (S.val u), unitNormal (tangentFrame S u)⟫ *
        areaDensity (tangentFrame S u)‖ ≤ ‖q u‖
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial, mul_assoc]
      change ‖χ k (S.val u) * q u‖ ≤ ‖q u‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hb k (S.val u)).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb k (S.val u)).2
    · filter_upwards [ae_restrict_mem (SimplexIntegration.standardSimplex_isCompact n).measurableSet] with u hu
      have hx : S.val u ∈ R.carrier := mem_iUnion.mpr
        ⟨c, ⟨SmoothChains.relabel i.succAbove u, SmoothChains.relabel_mem i.succAbove hu, rfl⟩⟩
      exact ((hlim (S.val u) hx).inner tendsto_const_nhds).mul tendsto_const_nhds
  have hh : Filter.Tendsto (fun k => R.boundaryIntegral (fun x ν => ⟪G k x, ν⟫))
      Filter.atTop (nhds (R.boundaryIntegral (fun x ν => ⟪F x, ν⟫))) := by
    unfold boundaryIntegral
    exact tendsto_finsetSum _ (fun c _ => tendsto_finsetSum _
      (fun i _ => tendsto_const_nhds.mul (hface c i)))
  simp_rw [hzero] at hh
  exact (tendsto_nhds_unique hh tendsto_const_nhds)

end Region

set_option backward.isDefEq.respectTransparency false


/-- Derivative of the barycentric coordinate which increases toward the
vertex opposite the specified face. -/
def inwardCoordinate {n : ℕ} (i : Fin (n+2)) (w : Space (n+1)) : ℝ :=
  Fin.cases (-∑ j, w j) (fun j => w j) i

theorem volume_cons_omitted {n : ℕ} (i : Fin (n+1)) (w : Space (n+1)) :
    parameterVolume (n+1) (Fin.cons w (fun j => EuclideanSpace.single (i.succAbove j) 1)) =
      (-1 : ℝ)^i.val * w i := by
  have hi := (parameterVolume (n+1)).neg_one_pow_smul_map_insertNth i w
    (i.removeNth (fun j => EuclideanSpace.single j 1))
  rw [Fin.insertNth_removeNth, volume_update_basis] at hi
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hi
  rw [hi]
  congr 1

/-- The Stokes face sign produces the negative inward barycentric covector,
not an arbitrary choice of unit normal. -/
theorem reference_face_conormal {n : ℕ} (i : Fin (n+2)) (w : Space (n+1)) :
    (-1 : ℝ)^i.val * parameterVolume (n+1)
      (Fin.cons w (fun j => relabelLinear i.succAbove (EuclideanSpace.single j 1))) =
      -inwardCoordinate i w := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.val_zero, pow_zero, one_mul, inwardCoordinate, Fin.cases_zero,
      neg_neg, relabelLinear_single, Fin.succAbove_zero, vertex_succ]
    let A := ((parameterVolume (n+1)).curryLeft w).compContinuousLinearMap
      (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm.toContinuousLinearMap
    have he := SimplexStokes.alternating_upperFace A
    change parameterVolume (n+1)
      (Fin.cons w (fun j => EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1)) = _
    have he' : parameterVolume (n+1)
        (Fin.cons w (fun j => EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1)) =
        ∑ i : Fin (n+1), (-1 : ℝ)^i.val * parameterVolume (n+1)
          (Fin.cons w (fun j => EuclideanSpace.single (i.succAbove j) 1)) := he
    rw [he']
    apply Finset.sum_congr rfl
    intro i _
    rw [volume_cons_omitted, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  · simp only [relabelLinear_single, Fin.succ_succAbove_zero, vertex_zero, sub_zero,
      Fin.succ_succAbove_succ, vertex_succ, volume_cons_omitted, Fin.val_succ,
      pow_succ, inwardCoordinate, Fin.cases_succ]
    have hs : (-1 : ℝ)^i.val * (-1 : ℝ)^i.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc
      _ = -((-1 : ℝ)^i.val * (-1 : ℝ)^i.val) * w i := by ring
      _ = _ := by rw [hs]; ring

/-- Pullback of the signed cofactor under any linear map. Singular maps are
included: the identity is polynomial, with no inverse or division. -/
theorem linear_face_conormal {n : ℕ} (L : Space (n+1) →L[ℝ] Space (n+1))
    (i : Fin (n+2)) (w : Space (n+1)) :
    ⟪(-1 : ℝ)^i.val • normal (fun j => L (relabelLinear i.succAbove
      (EuclideanSpace.single j 1))), L w⟫ = -L.det * inwardCoordinate i w := by
  rw [inner_smul_left, normal_inner]
  simp only [starRingEnd_apply, star_trivial]
  have he : (parameterVolume (n+1)).compContinuousLinearMap L =
      L.det • parameterVolume (n+1) := by
    rw [top_form_eq ((parameterVolume (n+1)).compContinuousLinearMap L),
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      alternating_linear, parameterVolume_basis, mul_one]
  have hh := congrArg (fun A : Space (n+1) [⋀^Fin (n+1)]→L[ℝ] ℝ =>
    A (Fin.cons w (fun j => relabelLinear i.succAbove (EuclideanSpace.single j 1)))) he
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hh
  have hh' : parameterVolume (n+1) (Fin.cons (L w)
      (fun j => L (relabelLinear i.succAbove (EuclideanSpace.single j 1)))) =
      L.det * parameterVolume (n+1) (Fin.cons w
        (fun j => relabelLinear i.succAbove (EuclideanSpace.single j 1))) := by
    rw [← hh]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [hh']
  calc
    _ = L.det * ((-1 : ℝ)^i.val * parameterVolume (n+1)
        (Fin.cons w (fun j => relabelLinear i.succAbove (EuclideanSpace.single j 1)))) := by ring
    _ = _ := by rw [reference_face_conormal]; ring

theorem interior_simplex_of_strict {n : ℕ} {u : Space n}
    (hp : ∀ i, 0 < u i) (hs : ∑ i, u i < 1) :
    u ∈ interior (standardSimplex n) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hi : ∀ᶠ v in nhds u, ∀ i, 0 < v i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (show ContinuousAt (fun v : Space n => v i) u by fun_prop).eventually
      (lt_mem_nhds (hp i))
  have hj : ∀ᶠ v in nhds u, ∑ i, v i < 1 :=
    (show ContinuousAt (fun v : Space n => ∑ i, v i) u by fun_prop).eventually
      (gt_mem_nhds hs)
  filter_upwards [hi, hj] with v hv hv'
  exact ⟨fun i => (hv i).le, hv'.le⟩

theorem standardSimplex_closure_interior (n : ℕ) :
    closure (interior (standardSimplex n)) = standardSimplex n := by
  rw [(standardSimplex_convex n).closure_interior_eq_closure_of_nonempty_interior,
    (standardSimplex_isCompact n).isClosed.closure_eq]
  let u : Space n := WithLp.toLp 2 (fun _ => 1 / ((n : ℝ)+1))
  refine ⟨u, interior_simplex_of_strict (fun i => ?_) ?_⟩
  · change 0 < 1 / ((n : ℝ)+1)
    positivity
  · change (∑ _ : Fin n, 1 / ((n : ℝ)+1)) < 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith

/-- Positivity in the interior gives a nonnegative boundary Jacobian; no
nondegeneracy is imposed on the boundary. -/
theorem PositiveSimplex.det_nonneg {n : ℕ} (S : PositiveSimplex n)
    {u : Space n} (hu : u ∈ standardSimplex n) : 0 ≤ (fderiv ℝ S.simplex.val u).det := by
  have hc : ContinuousWithinAt (fun v => (fderiv ℝ S.simplex.val v).det)
      (interior (standardSimplex n)) u :=
    ContinuousLinearMap.continuous_det.continuousAt.comp_continuousWithinAt
      ((S.contDiffAt hu).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have : Filter.NeBot (nhdsWithin u (interior (standardSimplex n))) :=
    mem_closure_iff_nhdsWithin_neBot.mp ((standardSimplex_closure_interior n).symm ▸ hu)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hc
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (S.positive v hv).le

theorem inwardCoordinate_sub_face {n : ℕ} (i : Fin (n+2)) (u : Space n)
    (w : Space (n+1)) :
    inwardCoordinate i (w - relabel i.succAbove u) = weights w i := by
  have hz := congrFun (weights_face i u) i
  simp only [Fin.insertNth_apply_same] at hz
  induction i using Fin.cases with
  | zero =>
    simp only [inwardCoordinate, Fin.cases_zero, weights, Fin.cons_zero] at hz ⊢
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib]
    linarith
  | succ j =>
    simp only [inwardCoordinate, Fin.cases_succ, weights, Fin.cons_succ] at hz ⊢
    simp only [PiLp.sub_apply]
    linarith

theorem tangentFrame_face {n : ℕ} (S : Simplex (n+1) (Space (n+1)))
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) :
    tangentFrame (S.face i) u = fun j =>
      fderiv ℝ S.val (relabel i.succAbove u)
        (relabelLinear i.succAbove (EuclideanSpace.single j 1)) := by
  unfold tangentFrame Simplex.face
  rw [fderiv_reparam S i.succAbove hu]
  rfl

namespace Region

/-- The signed unit normal pairs negatively with every inward barycentric
transverse vector. The identity includes zero Jacobians and zero area. -/
theorem positiveFaceNormal_conormal {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) (w : Space (n+1)) :
    areaDensity (tangentFrame ((R.cell c).simplex.face i) u) *
      ⟪R.positiveFaceNormal c i u,
        fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)
          (w - relabel i.succAbove u)⟫ =
      -(fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)).det * weights w i := by
  rw [positiveFaceNormal, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [mul_left_comm, ← real_inner_smul_left]
  rw [← normal_eq_density_smul, ← real_inner_smul_left]
  rw [tangentFrame_face _ i hu, linear_face_conormal, inwardCoordinate_sub_face]

/-- Nonnegative area and the Stokes sign make this normal support the affine
tangent image of the whole source simplex on its exterior side. -/
theorem positiveFaceNormal_supports {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (ha : 0 < areaDensity (tangentFrame ((R.cell c).simplex.face i) u))
    {w : Space (n+1)} (hw : w ∈ standardSimplex (n+1)) :
    ⟪R.positiveFaceNormal c i u,
      fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)
        (w - relabel i.succAbove u)⟫ ≤ 0 := by
  have he := R.positiveFaceNormal_conormal c i hu w
  have hp := (R.cell c).det_nonneg (relabel_mem i.succAbove hu)
  have hw' := (mem_simplex_iff_weights w).mp hw i
  have hn : -(fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)).det * weights w i ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hw'
  nlinarith

/-- Strictly positive Jacobian makes the signed normal strictly opposite to
an inward transverse direction; negating it would give the wrong sign. -/
theorem positiveFaceNormal_strict_inward {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (hd : 0 < (fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)).det)
    {w : Space (n+1)} (hw : 0 < weights w i) :
    ⟪R.positiveFaceNormal c i u,
      fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)
        (w - relabel i.succAbove u)⟫ < 0 := by
  have he := R.positiveFaceNormal_conormal c i hu w
  have ha : 0 ≤ areaDensity (tangentFrame ((R.cell c).simplex.face i) u) := Real.sqrt_nonneg _
  have hn := mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hw
  nlinarith

/-- The normal ray leaves the affine tangent image, including full Jacobians
which vanish on the face, provided the face itself has nonzero area. -/
theorem positiveFaceNormal_exterior_tangent {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (ha : 0 < areaDensity (tangentFrame ((R.cell c).simplex.face i) u))
    {t : ℝ} (ht : 0 < t) :
    t • R.positiveFaceNormal c i u ∉
      (fun w => fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)
        (w - relabel i.succAbove u)) '' standardSimplex (n+1) := by
  rintro ⟨w, hw, he⟩
  have hs := R.positiveFaceNormal_supports c i hu ha hw
  dsimp only at he
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq, R.positiveFaceNormal_norm] at hs
  norm_num at hs
  linarith

end Region

/-- Cofactors depend continuously on the frame, even when its rank drops. -/
theorem continuous_normal {n : ℕ} : Continuous (normal (n := n)) := by
  unfold normal
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun a : Fin n → Space (n+1) =>
      parameterVolume (n+1) (Fin.cons (EuclideanSpace.single i 1) a)) := by
    apply (parameterVolume (n+1)).cont.comp
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact continuous_const
    · exact continuous_apply j
  exact hc.smul continuous_const

/-- The boundary cofactor is the limit of the same oriented tangent cofactor
at positive-Jacobian interior points. This fixes its sign when the full
boundary Jacobian vanishes but the face area is nonzero. -/
theorem PositiveSimplex.face_cofactor_limit {n : ℕ} (S : PositiveSimplex (n+1))
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) :
    Filter.Tendsto (fun v => (-1 : ℝ)^i.val • normal (fun j =>
      fderiv ℝ S.simplex.val v (relabelLinear i.succAbove (EuclideanSpace.single j 1))))
      (nhdsWithin (relabel i.succAbove u) (interior (standardSimplex (n+1))))
      (nhds ((-1 : ℝ)^i.val • normal (tangentFrame (S.simplex.face i) u))) := by
  rw [tangentFrame_face _ i hu]
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun v => normal (fun j =>
      fderiv ℝ S.simplex.val v (relabelLinear i.succAbove (EuclideanSpace.single j 1))))
      (relabel i.succAbove u) := by
    apply continuous_normal.continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    exact ((S.contDiffAt (relabel_mem i.succAbove hu)).continuousAt_fderiv
      (by norm_num)).clm_apply continuousAt_const
  exact (continuousAt_const (y := (-1 : ℝ)^i.val)).smul hc

/-- At every positive-Jacobian interior point, the transported face cofactor
has negative pairing with each strictly inward direction. -/
theorem PositiveSimplex.interior_cofactor_inward {n : ℕ} (S : PositiveSimplex (n+1))
    (i : Fin (n+2)) {v w : Space (n+1)} (hv : v ∈ interior (standardSimplex (n+1)))
    (hw : 0 < inwardCoordinate i w) :
    ⟪(-1 : ℝ)^i.val • normal (fun j => fderiv ℝ S.simplex.val v
      (relabelLinear i.succAbove (EuclideanSpace.single j 1))), fderiv ℝ S.simplex.val v w⟫ < 0 := by
  rw [linear_face_conormal]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (S.positive v hv)) hw

def inwardLinear {n : ℕ} (i : Fin (n+2)) : Space (n+1) →L[ℝ] ℝ :=
  Fin.cases (-∑ j, (ContinuousLinearMap.proj j).comp
    (EuclideanSpace.equiv (Fin (n+1)) ℝ).toContinuousLinearMap)
    (fun j => (ContinuousLinearMap.proj j).comp
      (EuclideanSpace.equiv (Fin (n+1)) ℝ).toContinuousLinearMap) i

theorem inwardLinear_apply {n : ℕ} (i : Fin (n+2)) (v : Space (n+1)) :
    inwardLinear i v = inwardCoordinate i v := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [inwardLinear, inwardCoordinate]

theorem weights_eq_affine {n : ℕ} (i : Fin (n+2)) (v : Space (n+1)) :
    weights v i = weights (0 : Space (n+1)) i + inwardLinear i v := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [weights, inwardLinear, sub_eq_add_neg]

theorem weights_hasFDerivAt {n : ℕ} (i : Fin (n+2)) (v : Space (n+1)) :
    HasFDerivAt (fun w => weights w i) (inwardLinear i) v := by
  simpa only [← weights_eq_affine] using (inwardLinear i).hasFDerivAt.const_add (weights 0 i)

/-- Compactness and injectivity prevent remote parameter points from mapping
arbitrarily close to the image of a given parameter point. -/
theorem PositiveSimplex.eventually_preimage_near {n : ℕ} (S : PositiveSimplex n)
    {p : Space n} (hp : p ∈ standardSimplex n) {V : Set (Space n)}
    (hV : IsOpen V) (hpV : p ∈ V) :
    ∀ᶠ y in nhds (S.simplex.val p), ∀ q ∈ standardSimplex n, S.simplex.val q = y → q ∈ V := by
  have hc := ((standardSimplex_isCompact n).diff hV).image_of_continuousOn
    (fun q hq => (S.contDiffAt hq.1).continuousAt.continuousWithinAt)
  have hn : S.simplex.val p ∉ S.simplex.val '' (standardSimplex n \ V) := by
    rintro ⟨q, hq, he⟩
    exact hq.2 (S.injective hq.1 hp he ▸ hpV)
  filter_upwards [hc.isClosed.isOpen_compl.mem_nhds hn] with y hy
  intro q hq he
  by_contra hqV
  exact hy ⟨q, ⟨hq, hqV⟩, he⟩

/-- A negative derivative at zero makes a scalar function strictly smaller
than its value at zero on a sufficiently short positive interval. -/
theorem eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d < 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), f t < f 0 := by
  have ht := hf.tendsto_slope_zero_right
  filter_upwards [ht.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with t htd htpos
  have hs : (f t - f 0) / t < 0 := by simpa [slope_def_field, div_eq_mul_inv, mul_comm] using htd
  have := (div_lt_iff₀ htpos).mp hs
  simpa using (sub_neg.mp (by simpa using this : f t - f 0 < 0))

/-- At a nonsingular boundary parameter, the signed normal ray leaves the
actual nonlinear cell image, not merely its affine tangent model. -/
theorem Region.positiveFaceNormal_exterior {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (hd : 0 < (fderiv ℝ (R.cell c).simplex.val (relabel i.succAbove u)).det) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      (R.cell c).simplex.val (relabel i.succAbove u) + t • R.positiveFaceNormal c i u ∉
        (R.cell c).carrier := by
  let S := R.cell c
  let p := relabel i.succAbove u
  let ν := R.positiveFaceNormal c i u
  let L := fderiv ℝ S.simplex.val p
  let e : Space (n+1) ≃L[ℝ] Space (n+1) :=
    (LinearMap.equivOfDetNeZero L.toLinearMap (ne_of_gt hd)).toContinuousLinearEquiv
  have he : (e : Space (n+1) →L[ℝ] Space (n+1)) = L := by ext v; rfl
  have hp : p ∈ standardSimplex (n+1) := relabel_mem i.succAbove hu
  have hstrict : HasStrictFDerivAt S.simplex.val (e : Space (n+1) →L[ℝ] Space (n+1)) p := by
    rw [he]
    exact (S.contDiffAt hp).hasStrictFDerivAt (by norm_num)
  let inv := hstrict.localInverse S.simplex.val e p
  have hinv := hstrict.to_localInverse.hasFDerivAt
  have hv : L (e.symm ν) = ν := by rw [← he]; exact e.apply_symm_apply ν
  have ha : 0 < areaDensity (tangentFrame (S.simplex.face i) u) := by
    have hx := R.positiveFaceNormal_conormal c i hu (vertex i)
    rw [weights_vertex] at hx
    simp only [ite_true, mul_one] at hx
    have hn : 0 ≤ areaDensity (tangentFrame (S.simplex.face i) u) := Real.sqrt_nonneg _
    apply lt_of_le_of_ne hn
    intro hz
    rw [← hz, zero_mul] at hx
    linarith
  have hdot := R.positiveFaceNormal_conormal c i hu (p + e.symm ν)
  rw [← inwardCoordinate_sub_face i u (p + e.symm ν)] at hdot
  change areaDensity (tangentFrame (S.simplex.face i) u) *
      ⟪ν, L (p + e.symm ν - p)⟫ = -L.det * inwardCoordinate i (p + e.symm ν - p) at hdot
  rw [add_sub_cancel_left, hv, real_inner_self_eq_norm_sq] at hdot
  have hν : ‖ν‖ = 1 := R.positiveFaceNormal_norm c i u
  rw [hν, one_pow, mul_one] at hdot
  have hneg : inwardLinear i (e.symm ν) < 0 := by
    rw [inwardLinear_apply]
    change 0 < L.det at hd
    nlinarith
  let ray := fun t : ℝ => S.simplex.val p + t • ν
  have hray : HasDerivAt ray ν 0 := by
    simpa [ray] using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add (S.simplex.val p)
  have hder : HasDerivAt (fun t => weights (inv (ray t)) i) (inwardLinear i (e.symm ν)) 0 := by
    have hinv' : HasFDerivAt inv (e.symm : Space (n+1) →L[ℝ] Space (n+1)) (ray 0) := by
      simpa only [ray, zero_smul, add_zero] using hinv
    have hcomp := hinv'.comp_hasDerivAt 0 hray
    have hw := (weights_hasFDerivAt i (inv (ray 0))).comp_hasDerivAt 0 hcomp
    simpa only [Function.comp_def, inv] using! hw
  have hzero : weights (inv (ray 0)) i = 0 := by
    simp only [ray, zero_smul, add_zero, inv, hstrict.localInverse_apply_image]
    exact (congrFun (weights_face i u) i).trans (Fin.insertNth_apply_same _ _ _)
  have hnegative := eventually_lt_right_of_deriv_neg hder hneg
  rw [hzero] at hnegative
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hstrict.eventually_left_inverse
  have hnear := S.eventually_preimage_near hp hV hpV
  have hrayt : Filter.Tendsto ray (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (S.simplex.val p)) := by
    have h := hray.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [ray, zero_smul, add_zero] using h
  filter_upwards [hnegative, hrayt.eventually hnear] with t ht hnear'
  rintro ⟨q, hq, hqt⟩
  change S.simplex.val q = ray t at hqt
  have hqV := hnear' q hq hqt
  have heq : inv (ray t) = q := by rw [← hqt]; exact hVsub hqV
  rw [heq] at ht
  exact (not_lt_of_ge ((mem_simplex_iff_weights q).mp hq i)) ht

/-- At a nonzero-area face, including a singular full boundary Jacobian, the
unit normal is the continuous limit of the inward-negative interior cofactors.
Thus the singular case does not permit an independent sign choice. -/
theorem Region.positiveFaceNormal_limit {n : ℕ} (R : Region (n+1)) (c : Fin R.count)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (ha : 0 < areaDensity (tangentFrame ((R.cell c).simplex.face i) u)) :
    Filter.Tendsto (fun v =>
      let N := (-1 : ℝ)^i.val • normal (fun j => fderiv ℝ (R.cell c).simplex.val v
        (relabelLinear i.succAbove (EuclideanSpace.single j 1)))
      ‖N‖⁻¹ • N)
      (nhdsWithin (relabel i.succAbove u) (interior (standardSimplex (n+1))))
      (nhds (R.positiveFaceNormal c i u)) := by
  have ht := (R.cell c).face_cofactor_limit i hu
  let v := tangentFrame ((R.cell c).simplex.face i) u
  have hn : ‖(-1 : ℝ)^i.val • normal v‖ = areaDensity v := by
    simp [norm_smul, areaDensity_eq_norm]
  have hh := (ht.norm.inv₀ (by rw [hn]; exact ne_of_gt ha)).smul ht
  have he : ‖(-1 : ℝ)^i.val • normal v‖⁻¹ • ((-1 : ℝ)^i.val • normal v) =
      R.positiveFaceNormal c i u := by
    rw [hn, normal_eq_density_smul]
    simp only [smul_smul, mul_comm, mul_assoc]
    rw [mul_inv_cancel₀ (ne_of_gt ha), mul_one]
    rfl
  rw [he] at hh
  exact hh



def contractParameter {n : ℕ} (b : Space n) (t : ℝ) (x : Space n) : Space n :=
  (1-t) • x + t • b

theorem contractParameter_smooth {n : ℕ} (b : Space n) (t : ℝ) :
    ContDiff ℝ 2 (contractParameter b t) := by unfold contractParameter; fun_prop

theorem contractParameter_hasFDerivAt {n : ℕ} (b : Space n) (t : ℝ) (x : Space n) :
    HasFDerivAt (contractParameter b t) ((1-t) • ContinuousLinearMap.id ℝ (Space n)) x := by
  exact ((hasFDerivAt_id x).const_smul (1-t)).add_const (t • b)

theorem contractParameter_interior {n : ℕ} {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1)
    {x : Space n} (hx : x ∈ standardSimplex n) :
    contractParameter b t x ∈ interior (standardSimplex n) :=
  (standardSimplex_convex n).combo_self_interior_mem_interior hx hb
    (sub_nonneg.mpr ht.2.le) ht.1 (by ring)

/-- Homothetic source contraction. Its canonical faces are parallel to the
original canonical faces and lie strictly inside the original source simplex. -/
def contractSimplex {n : ℕ} (S : Simplex n (Space n)) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    Simplex n (Space n) := ⟨S.val ∘ contractParameter b t, by
  obtain ⟨U, hU, hsub, hS⟩ := S.property
  refine ⟨contractParameter b t ⁻¹' U, hU.preimage (contractParameter_smooth b t).continuous,
    (fun x hx => hsub (interior_subset (contractParameter_interior hb ht hx))), ?_⟩
  exact hS.comp (contractParameter_smooth b t).contDiffOn (fun _ hx => hx)⟩

theorem contractSimplex_deriv {n : ℕ} (S : Simplex n (Space n)) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1)
    {x : Space n} (hx : x ∈ standardSimplex n) :
    fderiv ℝ (contractSimplex S hb ht).val x =
      (1-t) • fderiv ℝ S.val (contractParameter b t x) := by
  change fderiv ℝ (S.val ∘ contractParameter b t) x = _
  rw [fderiv_comp x
    (S.differentiableAt (interior_subset (contractParameter_interior hb ht hx)))
    (contractParameter_hasFDerivAt b t x).differentiableAt,
    (contractParameter_hasFDerivAt b t x).fderiv]
  ext v
  simp

theorem contractSimplex_det {n : ℕ} (S : Simplex n (Space n)) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1)
    {x : Space n} (hx : x ∈ standardSimplex n) :
    (fderiv ℝ (contractSimplex S hb ht).val x).det =
      (1-t)^n * (fderiv ℝ S.val (contractParameter b t x)).det := by
  rw [contractSimplex_deriv S hb ht hx]
  simp [ContinuousLinearMap.det, LinearMap.det_smul]

/-- Every contracted cell has strictly positive Jacobian even on its closed
boundary, although the original boundary Jacobian is allowed to vanish. -/
def PositiveSimplex.contract {n : ℕ} (S : PositiveSimplex n) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    PositiveSimplex n where
  simplex := contractSimplex S.simplex hb ht
  injective := by
    intro x hx y hy he
    have he' := S.injective
      (interior_subset (contractParameter_interior hb ht hx))
      (interior_subset (contractParameter_interior hb ht hy)) he
    have he'' : (1-t) • x = (1-t) • y := add_right_cancel he'
    exact (smul_right_injective _ (ne_of_gt (sub_pos.mpr ht.2))) he''
  positive := by
    intro x hx
    rw [contractSimplex_det _ hb ht (interior_subset hx)]
    exact mul_pos (pow_pos (sub_pos.mpr ht.2) _) (S.positive _
      (contractParameter_interior hb ht (interior_subset hx)))

theorem PositiveSimplex.contract_det_pos {n : ℕ} (S : PositiveSimplex n) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1)
    {x : Space n} (hx : x ∈ standardSimplex n) :
    0 < (fderiv ℝ (S.contract hb ht).simplex.val x).det := by
  change 0 < (fderiv ℝ (contractSimplex S.simplex hb ht).val x).det
  rw [contractSimplex_det _ hb ht hx]
  exact mul_pos (pow_pos (sub_pos.mpr ht.2) _) (S.positive _ (contractParameter_interior hb ht hx))

theorem PositiveSimplex.contract_carrier_subset {n : ℕ} (S : PositiveSimplex n) {b : Space n}
    (hb : b ∈ interior (standardSimplex n)) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    (S.contract hb ht).carrier ⊆ interior S.carrier := by
  rintro x ⟨u, hu, rfl⟩
  exact S.interior_image (contractParameter_interior hb ht hu)

theorem contract_face_tangent {n : ℕ} (S : Simplex (n+1) (Space (n+1))) {b : Space (n+1)}
    (hb : b ∈ interior (standardSimplex (n+1))) {t : ℝ} (ht : t ∈ Ioo 0 1)
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) :
    tangentFrame ((contractSimplex S hb ht).face i) u = fun j =>
      (1-t) • (fderiv ℝ S.val (contractParameter b t (relabel i.succAbove u))
        (relabelLinear i.succAbove (EuclideanSpace.single j 1))) := by
  rw [tangentFrame_face _ i hu, contractSimplex_deriv _ hb ht (relabel_mem i.succAbove hu)]
  rfl

theorem contract_face_tangent_limit {n : ℕ} (S : PositiveSimplex (n+1)) {b : Space (n+1)}
    (hb : b ∈ interior (standardSimplex (n+1))) {t : ℕ → ℝ}
    (ht : ∀ k, t k ∈ Ioo 0 1) (hlim : Filter.Tendsto t Filter.atTop (nhds 0))
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) :
    Filter.Tendsto (fun k => tangentFrame ((S.contract hb (ht k)).simplex.face i) u)
      Filter.atTop (nhds (tangentFrame (S.simplex.face i) u)) := by
  have hp : Filter.Tendsto (fun k => contractParameter b (t k) (relabel i.succAbove u))
      Filter.atTop (nhds (relabel i.succAbove u)) := by
    simpa only [contractParameter, sub_zero, one_smul, zero_smul, add_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim |>.smul
        (tendsto_const_nhds (x := relabel i.succAbove u))).add
          (hlim.smul (tendsto_const_nhds (x := b)))
  have hd : Filter.Tendsto
      (fun k => fderiv ℝ S.simplex.val (contractParameter b (t k) (relabel i.succAbove u)))
      Filter.atTop (nhds (fderiv ℝ S.simplex.val (relabel i.succAbove u))) :=
    ((S.contDiffAt (relabel_mem i.succAbove hu)).continuousAt_fderiv
      (by norm_num)).tendsto.comp hp
  change Filter.Tendsto (fun k => tangentFrame ((contractSimplex S.simplex hb (ht k)).face i) u)
      Filter.atTop (nhds (tangentFrame (S.simplex.face i) u))
  simp_rw [contract_face_tangent _ hb _ i hu, tangentFrame_face _ i hu]
  apply tendsto_pi_nhds.mpr
  intro j
  have heval : Continuous (fun A : Space (n+1) →L[ℝ] Space (n+1) =>
      A (relabelLinear i.succAbove (EuclideanSpace.single j 1))) :=
    continuous_id.clm_apply continuous_const
  simpa only [Function.comp_def, sub_zero, one_smul] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).smul
      (heval.continuousAt.tendsto.comp hd)

theorem unitNormal_tendsto {n : ℕ} {v : ℕ → Fin n → Space (n+1)} {w : Fin n → Space (n+1)}
    (hv : Filter.Tendsto v Filter.atTop (nhds w)) (hw : 0 < areaDensity w) :
    Filter.Tendsto (fun k => unitNormal (v k)) Filter.atTop (nhds (unitNormal w)) := by
  have hn : normal w ≠ 0 := by
    intro hz
    rw [areaDensity_eq_norm, hz, norm_zero] at hw
    exact lt_irrefl _ hw
  have hN := continuous_normal.continuousAt.tendsto.comp hv
  have hnorm := (hN.norm.inv₀ (norm_ne_zero_iff.mpr hn)).smul hN
  rw [unitNormal, ite_eq_right hn]
  apply Filter.Tendsto.congr' _ hnorm
  filter_upwards [hN.eventually (eventually_ne_nhds hn)] with k hk
  change normal (v k) ≠ 0 at hk
  simp [unitNormal, hk]

theorem PositiveSimplex.contract_face_normal_limit {n : ℕ} (S : PositiveSimplex (n+1))
    {b : Space (n+1)} (hb : b ∈ interior (standardSimplex (n+1))) {t : ℕ → ℝ}
    (ht : ∀ k, t k ∈ Ioo 0 1) (hlim : Filter.Tendsto t Filter.atTop (nhds 0))
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (ha : 0 < areaDensity (tangentFrame (S.simplex.face i) u)) :
    Filter.Tendsto (fun k => (-1 : ℝ)^i.val •
      unitNormal (tangentFrame ((S.contract hb (ht k)).simplex.face i) u)) Filter.atTop
      (nhds ((-1 : ℝ)^i.val • unitNormal (tangentFrame (S.simplex.face i) u))) :=
  (tendsto_const_nhds (x := (-1 : ℝ)^i.val)).smul
    (unitNormal_tendsto (contract_face_tangent_limit S hb ht hlim i hu) ha)

/-- Every contracted canonical face has the actual nonlinear exterior normal,
since contraction moves all source points into the positive-Jacobian interior. -/
theorem PositiveSimplex.contract_face_exterior {n : ℕ} (S : PositiveSimplex (n+1))
    {b : Space (n+1)} (hb : b ∈ interior (standardSimplex (n+1)))
    {t : ℝ} (ht : t ∈ Ioo 0 1) (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      (S.contract hb ht).simplex.val (relabel i.succAbove u) +
        s • ((-1 : ℝ)^i.val • unitNormal (tangentFrame ((S.contract hb ht).simplex.face i) u)) ∉
          (S.contract hb ht).carrier := by
  let Q : Region (n+1) := {
    count := 1
    cell := fun _ => S.contract hb ht
    disjoint := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)) }
  exact Q.positiveFaceNormal_exterior ⟨0, Nat.zero_lt_one⟩ i hu
    (S.contract_det_pos hb ht (relabel_mem i.succAbove hu))

/-- Every nonzero-area face normal, including at a singular full Jacobian,
is a limit of actual outward unit normals of interior parallel faces.
The approximation retains full positive simplex parameterizations. -/
theorem PositiveSimplex.exists_interior_parallel_faces {n : ℕ} (S : PositiveSimplex (n+1))
    (i : Fin (n+2)) {u : Space n} (hu : u ∈ standardSimplex n)
    (ha : 0 < areaDensity (tangentFrame (S.simplex.face i) u)) :
    ∃ P : ℕ → PositiveSimplex (n+1),
      (∀ k, (P k).carrier ⊆ interior S.carrier) ∧
      (∀ k x, x ∈ standardSimplex (n+1) → 0 < (fderiv ℝ (P k).simplex.val x).det) ∧
      Filter.Tendsto (fun k => (P k).simplex.val (relabel i.succAbove u)) Filter.atTop
        (nhds (S.simplex.val (relabel i.succAbove u))) ∧
      Filter.Tendsto (fun k => tangentFrame ((P k).simplex.face i) u) Filter.atTop
        (nhds (tangentFrame (S.simplex.face i) u)) ∧
      Filter.Tendsto (fun k => (-1 : ℝ)^i.val • unitNormal (tangentFrame ((P k).simplex.face i) u))
        Filter.atTop (nhds ((-1 : ℝ)^i.val • unitNormal (tangentFrame (S.simplex.face i) u))) ∧
      (∀ k, ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
        (P k).simplex.val (relabel i.succAbove u) +
          s • ((-1 : ℝ)^i.val • unitNormal (tangentFrame ((P k).simplex.face i) u)) ∉
            (P k).carrier) := by
  let b : Space (n+1) := WithLp.toLp 2 (fun _ => 1 / ((n+1 : ℕ) + 1 : ℝ))
  have hb : b ∈ interior (standardSimplex (n+1)) := by
    apply interior_simplex_of_strict
    · intro j
      change 0 < 1 / ((n+1 : ℕ) + 1 : ℝ)
      positivity
    · change (∑ _ : Fin (n+1), 1 / ((n+1 : ℕ) + 1 : ℝ)) < 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
  let t : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 1)) / 2
  have ht (k) : t k ∈ Ioo 0 1 := by
    constructor
    · dsimp [t]; positivity
    · dsimp [t]
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2), div_lt_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hlim : Filter.Tendsto t Filter.atTop (nhds 0) := by
    simpa only [div_zero, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  refine ⟨fun k => S.contract hb (ht k), (fun k => S.contract_carrier_subset hb (ht k)),
    (fun k x hx => S.contract_det_pos hb (ht k) hx), ?_,
    contract_face_tangent_limit S hb ht hlim i hu,
    S.contract_face_normal_limit hb ht hlim i hu ha,
    (fun k => S.contract_face_exterior hb (ht k) i hu)⟩
  have hp : Filter.Tendsto (fun k => contractParameter b (t k) (relabel i.succAbove u))
      Filter.atTop (nhds (relabel i.succAbove u)) := by
    simpa only [contractParameter, sub_zero, one_smul, zero_smul, add_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim |>.smul
        (tendsto_const_nhds (x := relabel i.succAbove u))).add
          (hlim.smul (tendsto_const_nhds (x := b)))
  exact (S.contDiffAt (relabel_mem i.succAbove hu)).continuousAt.tendsto.comp hp


end Rudin.Support.EuclideanFlux
