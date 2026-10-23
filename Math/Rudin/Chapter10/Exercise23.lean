module

public import Math.Rudin.Support.SimplexStokes
public import Math.Rudin.Support.SmoothChainIntegration
public import Math.Rudin.Chapter10.Exercise01
public import Math.Rudin.Chapter10.Exercise20
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exercise 10.23: radial forms

The form indexed by `m` below is the source's `omega_(m+1)`.
All statements about a singular form require its radial domain.
The Euclidean norm, not the coordinate supremum norm, is used throughout.

The prescribed primitive, dimension classification, whole-sphere flux and
radial-invariance comparisons are included. The sphere charts have proved
coverage, overlap, orientation and geometric Gram-area identities.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise23

open Set MeasureTheory ContinuousAlternatingMap
open scoped RealInnerProductSpace Topology
open Rudin.Support.SimplexIntegration

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Projection to the first `k` coordinates, in their source order. -/
def firstCoordinates {n k : ℕ} (h : k ≤ n) : Space n →L[ℝ] Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (i.castLE h)))

@[simp] theorem firstCoordinates_apply {n k : ℕ} (h : k ≤ n) (x : Space n) (i : Fin k) :
    firstCoordinates h x i = x (i.castLE h) := rfl

/-- The source radius `r_k`. -/
def radius {n k : ℕ} (h : k ≤ n) (x : Space n) : ℝ := ‖firstCoordinates h x‖

/-- The source open domain `E_k`; no form assertion at radius zero is intended. -/
def radialDomain {n k : ℕ} (h : k ≤ n) : Set (Space n) := {x | 0 < radius h x}

theorem radialDomain_isOpen {n k : ℕ} (h : k ≤ n) : IsOpen (radialDomain h) :=
  isOpen_lt continuous_const (firstCoordinates h).continuous.norm

/-- The coordinate determinant with the standard orientation. -/
def coordinateVolume (k : ℕ) : Space k [⋀^Fin k]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating.compLinearMap
    (EuclideanSpace.equiv (Fin k) ℝ).toLinearEquiv.toLinearMap
  cont := by
    change Continuous (fun v : Fin k → Space k => Matrix.det (fun i j => v i j))
    have hc : Continuous (fun v : Fin k → Space k => fun i j => v i j) :=
      continuous_pi fun i => continuous_pi fun j =>
        (EuclideanSpace.proj j).continuous.comp (continuous_apply i)
    exact hc.matrix_det

@[simp] theorem coordinateVolume_apply {k : ℕ} (v : Fin k → Space k) :
    coordinateVolume k v = Matrix.det (fun i j => v i j) := rfl

/-- The source radial form in its own first `m+1` coordinates. -/
def topRadial (m : ℕ) : Form m (Space (m+1)) :=
  fun x => (‖x‖ ^ (m+1))⁻¹ • (coordinateVolume (m+1)).curryLeft x

/-- The actual source form on the ambient `R^n`, with source index `k=m+1`. -/
def omega {n : ℕ} (m : ℕ) (h : m+1 ≤ n) : Form m (Space n) :=
  fun x => (topRadial m (firstCoordinates h x)).compContinuousLinearMap (firstCoordinates h)

/-- Expansion into the signed omitted-coordinate determinants in the source. -/
theorem omega_source_formula {n m : ℕ} (h : m+1 ≤ n) (x : Space n)
    (v : Fin m → Space n) :
    omega m h x v = (radius h x ^ (m+1))⁻¹ *
      ∑ i : Fin (m+1), (-1 : ℝ)^i.val * x (i.castLE h) *
        Matrix.det (fun a b : Fin m => v a ((i.succAbove b).castLE h)) := by
  change (radius h x ^ (m+1))⁻¹ *
    Matrix.det (fun i j => (Matrix.vecCons (firstCoordinates h x)
      (fun a => firstCoordinates h (v a)) i) j) = _
  congr 1
  exact Matrix.det_succ_row_zero _

/-- The prescribed scalar integral. Its convergence and FTC require separate proofs. -/
def g (k : ℕ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioc (-1 : ℝ) t, (1-s^2) ^ (((k : ℝ)-3)/2)

/-- The prescribed scalar multiplier, with `k=m+2`. -/
def primitiveFactor {n : ℕ} (m : ℕ) (h : m+2 ≤ n) (x : Space n) : ℝ :=
  (-1 : ℝ)^(m+2) * g (m+2) (x (⟨m+1, by omega⟩) / radius h x)

/-- Exactness uses image `{0}` in degree zero. Positive degrees use an actual
C¹ primitive on the given open set. This does not introduce negative forms. -/
def ExactOn {n : ℕ} : (m : ℕ) → Form m (Space n) → Set (Space n) → Prop
  | 0, ω, U => ∀ x ∈ U, ω x = 0
  | m+1, ω, U => ∃ η : Form m (Space n), ContDiffOn ℝ 1 η U ∧
      ∀ x ∈ U, extDeriv η x = ω x

@[simp] theorem exactOn_zero_iff {n : ℕ} (ω : Form 0 (Space n)) (U : Set (Space n)) :
    ExactOn 0 ω U ↔ ∀ x ∈ U, ω x = 0 := Iff.rfl

@[simp] theorem exactOn_succ_iff {n m : ℕ} (ω : Form (m+1) (Space n)) (U : Set (Space n)) :
    ExactOn (m+1) ω U ↔ ∃ η : Form m (Space n), ContDiffOn ℝ 1 η U ∧
      ∀ x ∈ U, extDeriv η x = ω x := Iff.rfl

/-- In one active coordinate the source form is the sign function. -/
theorem omega_one_apply {n : ℕ} (h : 1 ≤ n) (x : Space n) (v : Fin 0 → Space n) :
    omega 0 h x v = x ⟨0, by omega⟩ / |x ⟨0, by omega⟩| := by
  have hdet : coordinateVolume 1 (Matrix.vecCons (firstCoordinates h x)
      (fun a : Fin 0 => firstCoordinates h (v a))) = x ⟨0, by omega⟩ :=
    Matrix.det_fin_one _
  change (‖firstCoordinates h x‖ ^ 1)⁻¹ *
    coordinateVolume 1 (Matrix.vecCons (firstCoordinates h x)
      (fun a : Fin 0 => firstCoordinates h (v a))) = _
  rw [hdet, pow_one]
  have hr : ‖firstCoordinates h x‖ = |x ⟨0, by omega⟩| := by
    simp only [EuclideanSpace.norm_eq, firstCoordinates_apply,
      Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    rfl
  rw [hr, div_eq_mul_inv, mul_comm]

/-- The one-coordinate form is genuinely locally constant on its domain. -/
theorem omega_one_locally_constant {n : ℕ} (h : 1 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain h) :
    ∃ c : Space n [⋀^Fin 0]→L[ℝ] ℝ, omega 0 h =ᶠ[𝓝 x] fun _ => c := by
  let i : Fin n := ⟨0, by omega⟩
  have hne : x i ≠ 0 := by
    have hr : radius h x = |x i| := by
      simp only [radius, EuclideanSpace.norm_eq, firstCoordinates_apply,
        Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
      rfl
    change 0 < radius h x at hx
    rw [hr, abs_pos] at hx
    exact hx
  rcases lt_or_gt_of_ne hne with hn | hp
  · refine ⟨constOfIsEmpty ℝ (Space n) (Fin 0) (-1), ?_⟩
    have he : ∀ᶠ y in 𝓝 x, y i < 0 :=
      (EuclideanSpace.proj i).continuous.continuousAt.eventually (gt_mem_nhds hn)
    filter_upwards [he] with y hy
    ext v
    rw [omega_one_apply]
    change y i / |y i| = -1
    rw [abs_of_neg hy]
    simp [div_neg, div_self hy.ne]
  · refine ⟨constOfIsEmpty ℝ (Space n) (Fin 0) 1, ?_⟩
    have he : ∀ᶠ y in 𝓝 x, 0 < y i :=
      (EuclideanSpace.proj i).continuous.continuousAt.eventually (lt_mem_nhds hp)
    filter_upwards [he] with y hy
    ext v
    rw [omega_one_apply]
    change y i / |y i| = 1
    rw [abs_of_pos hy, div_self hy.ne']

/-- Part (a), including the degree-zero boundary case, with derivative existence. -/
theorem omega_one_closed {n : ℕ} (h : 1 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain h) :
    DifferentiableAt ℝ (omega 0 h) x ∧ extDeriv (omega 0 h) x = 0 := by
  obtain ⟨c, hc⟩ := omega_one_locally_constant h hx
  constructor
  · exact hc.differentiableAt_iff.mpr (differentiableAt_const c)
  · rw [hc.extDeriv_eq]
    ext v
    simp [extDeriv, alternatizeUncurryFin_apply]

/-- A nonzero value prevents exactness under the stated image-`{0}` convention. -/
theorem omega_one_not_exact {n : ℕ} (h : 1 ≤ n) :
    ¬ ExactOn 0 (omega 0 h) (radialDomain h) := by
  intro he
  let i : Fin n := ⟨0, by omega⟩
  let x : Space n := EuclideanSpace.single i 1
  have hx : x ∈ radialDomain h := by
    change 0 < ‖firstCoordinates h x‖
    rw [norm_pos_iff]
    intro hz
    have hz' := congrArg (fun z : Space 1 => z 0) hz
    change (EuclideanSpace.single i 1 : Space n) i = 0 at hz'
    simp at hz'
  have hv := congrArg (fun A : Space n [⋀^Fin 0]→L[ℝ] ℝ => A Fin.elim0) (he x hx)
  rw [omega_one_apply] at hv
  norm_num [x, i] at hv

/-- Adding multiples of the first vector to other arguments leaves an
alternating evaluation unchanged. No independence assumption is needed. -/
theorem alternating_radial_shear {n : ℕ} (A : Space (n+1) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (x : Space (n+1)) (v : Fin n → Space (n+1)) (a : Fin n → ℝ) :
    A (Matrix.vecCons x (fun i => v i + a i • x)) = A (Matrix.vecCons x v) := by
  classical
  have hzero (w : Fin n → Space (n+1)) (i : Fin n) :
      A.curryLeft x (Function.update w i x) = 0 := by
    apply A.map_eq_zero_of_eq _ (i := 0) (j := i.succ)
    · simp
    · exact Fin.succ_ne_zero i |>.symm
  have hind (s : Finset (Fin n)) :
      A.curryLeft x (fun i => v i + (if i ∈ s then a i else 0) • x) =
        A.curryLeft x v := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let w := fun j => v j + (if j ∈ s then a j else 0) • x
      have he : (fun j => v j + (if j ∈ insert i s then a j else 0) • x) =
          Function.update w i (v i + a i • x) := by
        funext j
        by_cases hj : j = i
        · subst j; simp
        · simp [w, hj]
      rw [he, (A.curryLeft x).map_update_add, (A.curryLeft x).map_update_smul,
        hzero, smul_zero, add_zero]
      have hw : Function.update w i (v i) = w := by
        apply Function.update_eq_self_iff.mpr
        simp [w, hi]
      rw [hw]
      exact ih
  simpa using hind Finset.univ

/-- The numerator's exact scaling, including all derivative terms of a
nonconstant radial scale. -/
theorem alternating_radial_scale {n : ℕ} (A : Space (n+1) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (x : Space (n+1)) (v : Fin n → Space (n+1)) (a : Fin n → ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    A (Matrix.vecCons (r • x) (fun i => r • v i + a i • x)) =
      r^(n+1) * A (Matrix.vecCons x v) := by
  have he : Matrix.vecCons (r • x) (fun i => r • v i + a i • x) =
      fun i => r • Matrix.vecCons x (fun j => v j + (a j / r) • x) i := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change r • v j + a j • x = r • (v j + (a j / r) • x)
      rw [smul_add, smul_smul]
      congr 1
      congr 1
      field_simp
  rw [he, A.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [alternating_radial_shear]

/-- Positive radial rescaling preserves the actual pulled-back form.
This pointwise statement permits rank-deficient maps and nonconstant scales. -/
theorem radial_pullback_at {n p : ℕ} {σ : Space p → Space (n+1)}
    {ρ : Space p → ℝ} {u : Space p}
    (hσ : DifferentiableAt ℝ σ u) (hρ : DifferentiableAt ℝ ρ u)
    (hpos : 0 < ρ u) :
    pullback (topRadial n) (fun z => ρ z • σ z) u = pullback (topRadial n) σ u := by
  ext v
  have hd : fderiv ℝ (fun z => ρ z • σ z) u =
      ρ u • fderiv ℝ σ u + (fderiv ℝ ρ u).smulRight (σ u) :=
    (hρ.hasFDerivAt.smul hσ.hasFDerivAt).fderiv
  simp only [pullback_apply, hd, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply]
  change (‖ρ u • σ u‖ ^ (n+1))⁻¹ * coordinateVolume (n+1)
    (Matrix.vecCons (ρ u • σ u) (fun i => ρ u • fderiv ℝ σ u (v i) +
      fderiv ℝ ρ u (v i) • σ u)) =
    (‖σ u‖ ^ (n+1))⁻¹ * coordinateVolume (n+1)
      (Matrix.vecCons (σ u) (fun i => fderiv ℝ σ u (v i)))
  rw [alternating_radial_scale _ _ _ _ hpos.ne']
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, mul_pow, mul_inv_rev]
  have hp : (ρ u)^(n+1) ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp

/-- Unit-sphere maps and positive scales cannot meet the singular point. -/
theorem radial_nonzero {n : ℕ} {x : Space n} (hx : ‖x‖ = 1) {r : ℝ} (hr : 0 < r) :
    r • x ≠ 0 := by
  have hn : x ≠ 0 := by intro hz; simp [hz] at hx
  exact smul_ne_zero hr.ne' hn

/-- Tangency is derived by differentiating the squared norm on the parameter
set. Unique differentiation permits compact-domain boundary points. -/
theorem sphere_tangent {n p : ℕ} {σ : Space p → Space n} {K : Set (Space p)}
    {u : Space p} (hu : u ∈ K) (hK : UniqueDiffWithinAt ℝ K u)
    (hσ : DifferentiableAt ℝ σ u) (hsphere : ∀ z ∈ K, ‖σ z‖ = 1)
    (v : Space p) : ⟪σ u, fderiv ℝ σ u v⟫ = 0 := by
  have hd := hσ.hasFDerivAt.norm_sq.hasFDerivWithinAt (s := K)
  have hc : HasFDerivWithinAt (fun _ : Space p => (1 : ℝ))
      (2 • (innerSL ℝ (σ u)).comp (fderiv ℝ σ u)) K u := by
    apply hd.congr
    · intro z hz
      simp [hsphere z hz]
    · simp [hsphere u hu]
  have he := hK.eq hc (hasFDerivWithinAt_const (x := u) (s := K) 1)
  have hv := congrArg (fun L : Space p →L[ℝ] ℝ => L v) he
  simp only [two_smul, _root_.add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, zero_apply] at hv
  linarith

/-- Geometric parametric density: square root of the Gram determinant.
This definition is independent of the radial form and its flux. -/
def areaDensity {n p : ℕ} (σ : Space p → Space n) (u : Space p) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => fderiv ℝ σ u (EuclideanSpace.single i 1))).det

/-- The integral of geometric parametric density, not an area-as-flux definition. -/
def parametricArea {n p : ℕ} (K : Set (Space p)) (σ : Space p → Space n) : ℝ :=
  ∫ u in K, areaDensity σ u

/-- The determinant squared is the Gram determinant, proved from matrix
multiplication. This is the geometric step in the flux comparison. -/
theorem coordinateVolume_sq {n : ℕ} (v : Fin n → Space n) :
    coordinateVolume n v ^ 2 = (Matrix.gram ℝ v).det := by
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin n) ℝ),
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [EuclideanSpace.basisFun_repr, star_trivial]
  change Matrix.det (fun i j => v i j) ^ 2 =
    Matrix.det (fun i j => v j i) * Matrix.det (fun i j => v j i)
  rw [← sq]
  congr 1
  exact (Matrix.det_transpose (fun i j => v i j)).symm

/-- Appending a unit normal orthogonal to all tangents leaves the tangent
Gram determinant unchanged. -/
theorem gram_cons_unit_normal {n : ℕ} (x : Space (n+1)) (v : Fin n → Space (n+1))
    (hx : ‖x‖ = 1) (hv : ∀ i, ⟪x, v i⟫ = 0) :
    (Matrix.gram ℝ (Matrix.vecCons x v)).det = (Matrix.gram ℝ v).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (Matrix.gram ℝ (Matrix.vecCons x v)).submatrix Fin.succ
      (Fin.succAbove 0) = Matrix.gram ℝ v := by
    ext i j
    simp [Matrix.gram, Matrix.submatrix]
  rw [hsub]
  simp [Matrix.gram, hx, hv]

/-- Outward orientation selects the nonnegative square root of the Gram
identity, rather than defining geometric area by a flux. -/
theorem normal_flux_eq_gram_area {n : ℕ} (x : Space (n+1))
    (v : Fin n → Space (n+1)) (hx : ‖x‖ = 1) (hv : ∀ i, ⟪x, v i⟫ = 0)
    (horient : 0 ≤ coordinateVolume (n+1) (Matrix.vecCons x v)) :
    topRadial n x v = Real.sqrt (Matrix.gram ℝ v).det := by
  have hs := coordinateVolume_sq (Matrix.vecCons x v)
  rw [gram_cons_unit_normal x v hx hv] at hs
  change (‖x‖ ^ (n+1))⁻¹ * coordinateVolume (n+1) (Matrix.vecCons x v) = _
  rw [hx, one_pow, inv_one, one_mul, ← hs, Real.sqrt_sq horient]

/-- Parametric flux equals geometric density on an outward-oriented sphere
patch. Tangent orthogonality is a conclusion, not an input. -/
theorem sphere_flux_density {n : ℕ} {σ : Space n → Space (n+1)}
    {K : Set (Space n)} {u : Space n} (hu : u ∈ K)
    (hK : UniqueDiffWithinAt ℝ K u) (hσ : DifferentiableAt ℝ σ u)
    (hsphere : ∀ z ∈ K, ‖σ z‖ = 1)
    (horient : 0 ≤ coordinateVolume (n+1) (Matrix.vecCons (σ u)
      (fun i => fderiv ℝ σ u (EuclideanSpace.single i 1)))) :
    pullback (topRadial n) σ u (fun i => EuclideanSpace.single i 1) = areaDensity σ u :=
  normal_flux_eq_gram_area (σ u) _ (hsphere u hu)
    (fun _ => sphere_tangent hu hK hσ hsphere _) horient

/-- Radial forms are smooth on the punctured Euclidean space. -/
theorem topRadial_contDiffAt {n : ℕ} {x : Space (n+1)} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (topRadial n) x := by
  exact (((contDiffAt_id.norm ℝ hx).pow (n+1)).inv
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))).smul
      (coordinateVolume (n+1)).curryLeft.contDiff.contDiffAt

/-- Radial projection onto the unit sphere. -/
def normalize {n : ℕ} (x : Space n) : Space n := ‖x‖⁻¹ • x

theorem normalize_norm {n : ℕ} {x : Space n} (hx : x ≠ 0) : ‖normalize x‖ = 1 := by
  simp [normalize, norm_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem normalize_contDiffAt {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (normalize : Space n → Space n) x :=
  ((contDiffAt_id.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- A top-degree alternating form vanishes on a family orthogonal to a
nonzero vector. This proves rank deficiency instead of assuming it. -/
theorem top_alternating_tangent_zero {n : ℕ} (A : Space n [⋀^Fin n]→L[ℝ] ℝ)
    {x : Space n} (hx : x ≠ 0) (v : Fin n → Space n)
    (hv : ∀ i, ⟪x, v i⟫ = 0) : A v = 0 := by
  apply A.toAlternatingMap.map_linearDependent
  intro hi
  have hspan : Submodule.span ℝ (Set.range v) ≤ (innerSL ℝ x).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i
  have htop : Submodule.span ℝ (Set.range v) = ⊤ :=
    hi.span_eq_top_of_card_eq_finrank' (by simp)
  rw [htop] at hspan
  have hxker : x ∈ (innerSL ℝ x).ker := hspan Submodule.mem_top
  have hh : ⟪x, x⟫ = 0 := hxker
  exact hx (inner_self_eq_zero.mp hh)

/-- Radial projection preserves the form locally, with genuine derivatives. -/
theorem normalize_pullback {n : ℕ} {x : Space (n+1)} (hx : x ≠ 0) :
    pullback (topRadial n) normalize x = topRadial n x := by
  have hρ : DifferentiableAt ℝ (fun z : Space (n+1) => ‖z‖⁻¹) x :=
    (((contDiffAt_id.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)) :
      ContDiffAt ℝ 2 _ x).differentiableAt (by norm_num)
  have he := radial_pullback_at (σ := (id : Space (n+1) → Space (n+1)))
    differentiableAt_id hρ (inv_pos.mpr (norm_pos_iff.mpr hx))
  ext v
  calc
    pullback (topRadial n) normalize x v = pullback (topRadial n) id x v :=
      congrArg (fun A => A v) he
    _ = topRadial n x v := by
      simp only [pullback_apply, fderiv_id, ContinuousLinearMap.id_apply, id_eq]

/-- Part (a) in the first `n+1` coordinates. Closedness follows by actual
pullback naturality and the rank deficiency of radial projection. -/
theorem topRadial_closed {n : ℕ} {x : Space (n+1)} (hx : x ≠ 0) :
    extDeriv (topRadial n) x = 0 := by
  have hopen : IsOpen {y : Space (n+1) | y ≠ 0} := isOpen_ne
  have he : pullback (topRadial n) normalize =ᶠ[𝓝 x] topRadial n := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact normalize_pullback hy
  rw [← he.extDeriv_eq]
  have hn : normalize x ≠ 0 := by
    intro hz
    have hh := normalize_norm hx
    simp [hz] at hh
  rw [exterior_pullback (topRadial n) normalize x
    ((topRadial_contDiffAt hn).differentiableAt (by norm_num)) (normalize_contDiffAt hx)]
  ext v
  change extDeriv (topRadial n) (normalize x) (fun i => fderiv ℝ normalize x (v i)) = 0
  apply top_alternating_tangent_zero _ hn
  intro i
  exact sphere_tangent (K := {y : Space (n+1) | y ≠ 0}) hx
    (hopen.uniqueDiffOn x hx)
    ((normalize_contDiffAt hx).differentiableAt (by norm_num))
    (fun _ hy => normalize_norm hy) (v i)

/-- Part (a), for every `1 ≤ k ≤ n` in the actual ambient Euclidean space. -/
theorem omega_closed {n m : ℕ} (h : m+1 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain h) : extDeriv (omega m h) x = 0 := by
  have hn : firstCoordinates h x ≠ 0 := norm_pos_iff.mp hx
  have hw : omega m h = pullback (topRadial m) (firstCoordinates h) := by
    funext y
    simp only [pullback, ContinuousLinearMap.fderiv, omega]
  rw [hw, exterior_pullback (topRadial m) (firstCoordinates h) x
    ((topRadial_contDiffAt hn).differentiableAt (by norm_num))
    (firstCoordinates h).contDiff.contDiffAt]
  ext v
  rw [pullback_apply, topRadial_closed hn]
  rfl

/-- Integrability at the improper lower endpoint. The exponent is greater
than `-1`, including the singular case `k=2`. -/
theorem g_integrable {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    IntervalIntegrable (fun s : ℝ => (1-s^2) ^ (((k : ℝ)-3)/2)) volume (-1) t := by
  let a : ℝ := ((k : ℝ)-3)/2
  have ha : -1 < a := by
    dsimp [a]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hleft : IntervalIntegrable (fun s : ℝ => (1+s)^a) volume (-1) t := by
    have hh := (intervalIntegral.intervalIntegrable_rpow' ha (a := 0) (b := t+1)).comp_add_left 1
    convert hh using 1 <;> ring
  have hright : ContinuousOn (fun s : ℝ => (1-s)^a) (uIcc (-1 : ℝ) t) := by
    rw [uIcc_of_le ht.1.le]
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_const.sub continuousAt_id).rpow_const
    left
    change 1-s ≠ 0
    linarith [hs.2, ht.2]
  apply (hleft.mul_continuousOn hright).congr
  intro s hs
  rw [uIoc_of_le ht.1.le] at hs
  have h1 : 0 ≤ 1+s := by linarith [hs.1]
  have h2 : 0 ≤ 1-s := by linarith [hs.2, ht.2]
  have he : 1-s^2 = (1+s)*(1-s) := by ring
  change (1+s)^a * (1-s)^a = (1-s^2)^a
  rw [he, Real.mul_rpow h1 h2]

/-- The set integral agrees with the oriented interval integral on its source domain. -/
theorem g_eq_intervalIntegral (k : ℕ) {t : ℝ} (ht : -1 < t) :
    g k t = ∫ s in (-1 : ℝ)..t, (1-s^2) ^ (((k : ℝ)-3)/2) := by
  rw [intervalIntegral.integral_of_le ht.le]
  rfl

/-- The actual derivative of the prescribed scalar primitive. -/
theorem g_hasDerivAt {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (g k) ((1-t^2) ^ (((k : ℝ)-3)/2)) t := by
  have hpos : 0 < 1-t^2 := by nlinarith [ht.1, ht.2]
  have hc : ContinuousAt (fun s : ℝ => (1-s^2) ^ (((k : ℝ)-3)/2)) t :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).rpow_const (Or.inl hpos.ne')
  have hm : Measurable (fun s : ℝ => (1-s^2) ^ (((k : ℝ)-3)/2)) := by fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (g_integrable hk ht)
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht.1] with s hs
  exact g_eq_intervalIntegral k hs

/-- The prescribed integral is genuinely an improper endpoint limit. -/
theorem g_improper_limit {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    Filter.Tendsto (fun a : ℝ => ∫ s in a..t, (1-s^2) ^ (((k : ℝ)-3)/2))
      (𝓝[Ioc (-1 : ℝ) t] (-1)) (𝓝 (g k t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (g_integrable hk ht) (show t ∈ uIcc (-1 : ℝ) t from right_mem_uIcc)
  have hl := (hc (-1) left_mem_uIcc).neg
  rw [uIcc_of_le ht.1.le] at hl
  have hh := hl.mono (show Ioc (-1 : ℝ) t ⊆ Icc (-1) t from Ioc_subset_Icc_self)
  rw [g_eq_intervalIntegral k ht.1]
  change Filter.Tendsto (fun b => -(∫ s in t..b, (1-s^2) ^ (((k : ℝ)-3)/2)))
    (𝓝[Ioc (-1 : ℝ) t] (-1))
    (𝓝 (-(∫ s in t..(-1 : ℝ), (1-s^2) ^ (((k : ℝ)-3)/2)))) at hh
  simpa only [← intervalIntegral.integral_symm] using hh

/-- Oriented pullback coefficient in the fixed standard parameter orientation. -/
def fluxDensity {n : ℕ} (σ : Space n → Space (n+1)) (u : Space n) : ℝ :=
  pullback (topRadial n) σ u (fun i => EuclideanSpace.single i 1)

/-- Parametric flux. Integrability is certified separately below. -/
def parametricFlux {n : ℕ} (K : Set (Space n)) (σ : Space n → Space (n+1)) : ℝ :=
  ∫ u in K, fluxDensity σ u

/-- A C² neighborhood extension gives a continuous flux coefficient on a
compact parameter set whose image avoids zero. -/
theorem fluxDensity_continuousOn {n : ℕ} {σ : Space n → Space (n+1)}
    {K U : Set (Space n)} (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hne : ∀ u ∈ K, σ u ≠ 0) :
    ContinuousOn (fluxDensity σ) K := by
  intro u hu
  have hS := (hσ u (hKU hu)).contDiffAt (hU.mem_nhds (hKU hu))
  have hp := Rudin.Support.SimplexStokes.pullback_contDiffAt
    ((topRadial_contDiffAt (hne u hu)).of_le (by norm_num)) hS
  exact ((ContinuousAlternatingMap.apply ℝ (Space n) ℝ
    (fun i => EuclideanSpace.single i 1)).continuous.continuousAt.comp hp.continuousAt).continuousWithinAt

/-- The flux integral is not a default value of a nonintegrable function. -/
theorem fluxDensity_integrable {n : ℕ} {σ : Space n → Space (n+1)}
    {K U : Set (Space n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hne : ∀ u ∈ K, σ u ≠ 0) :
    IntegrableOn (fluxDensity σ) K :=
  (fluxDensity_continuousOn hU hKU hσ hne).integrableOn_compact hK

/-- Radial invariance on every compact parameter set, hence on compact cells
and simplexes. Both maps use the same standard parameter orientation. C²
means extension to the explicitly specified open neighborhood. -/
theorem compact_radial_invariance {n : ℕ} {σ : Space n → Space (n+1)}
    {ρ : Space n → ℝ} {K U : Set (Space n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hρ : ContDiffOn ℝ 2 ρ U)
    (hsphere : ∀ u ∈ K, ‖σ u‖ = 1) (hpos : ∀ u ∈ K, 0 < ρ u) :
    (∀ u ∈ K, ρ u • σ u ≠ 0) ∧
    (∀ u ∈ K, pullback (topRadial n) (fun z => ρ z • σ z) u =
      pullback (topRadial n) σ u) ∧
    IntegrableOn (fluxDensity σ) K ∧
    IntegrableOn (fluxDensity (fun z => ρ z • σ z)) K ∧
    parametricFlux K (fun z => ρ z • σ z) = parametricFlux K σ := by
  have hn (u) (hu : u ∈ K) : σ u ≠ 0 := by
    intro hz
    have hh := hsphere u hu
    simp [hz] at hh
  have hnr (u) (hu : u ∈ K) : ρ u • σ u ≠ 0 :=
    radial_nonzero (hsphere u hu) (hpos u hu)
  have he (u) (hu : u ∈ K) : pullback (topRadial n) (fun z => ρ z • σ z) u =
      pullback (topRadial n) σ u := by
    apply radial_pullback_at
    · exact ((hσ u (hKU hu)).contDiffAt (hU.mem_nhds (hKU hu))).differentiableAt (by norm_num)
    · exact ((hρ u (hKU hu)).contDiffAt (hU.mem_nhds (hKU hu))).differentiableAt (by norm_num)
    · exact hpos u hu
  refine ⟨hnr, he, fluxDensity_integrable hK hU hKU hσ hn,
    fluxDensity_integrable hK hU hKU (hρ.smul hσ) hnr, ?_⟩
  apply setIntegral_congr_fun hK.measurableSet
  intro u hu
  exact congrArg (fun A => A (fun i => EuclideanSpace.single i 1)) (he u hu)

/-- Geometric density is continuous under the source neighborhood-C²
regularity. No flux identity is used in this proof. -/
theorem areaDensity_continuousOn {n p : ℕ} {σ : Space p → Space n}
    {K U : Set (Space p)} (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) : ContinuousOn (areaDensity σ) K := by
  intro u hu
  have hd := ((hσ u (hKU hu)).contDiffAt (hU.mem_nhds (hKU hu))).continuousAt_fderiv
    (by norm_num)
  have hv (i : Fin p) : ContinuousAt (fun z => fderiv ℝ σ z (EuclideanSpace.single i 1)) u :=
    hd.clm_apply continuousAt_const
  have hm : ContinuousAt (fun z => Matrix.gram ℝ
      (fun i => fderiv ℝ σ z (EuclideanSpace.single i 1))) u :=
    continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => (hv i).inner (hv j)))
  exact (continuous_id.matrix_det.continuousAt.comp hm).sqrt.continuousWithinAt

/-- Sphere patch flux is its geometric parametric area. The orientation is
the outward-normal-first orientation inherited from the ball. This is a patch
comparison; it does not by itself construct a whole-sphere chain. -/
theorem compact_sphere_flux_area {n : ℕ} {σ : Space n → Space (n+1)}
    {K U : Set (Space n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hunique : UniqueDiffOn ℝ K)
    (hsphere : ∀ u ∈ K, ‖σ u‖ = 1)
    (horient : ∀ u ∈ K, 0 ≤ coordinateVolume (n+1) (Matrix.vecCons (σ u)
      (fun i => fderiv ℝ σ u (EuclideanSpace.single i 1)))) :
    IntegrableOn (fluxDensity σ) K ∧ IntegrableOn (areaDensity σ) K ∧
      parametricFlux K σ = parametricArea K σ := by
  have hn (u) (hu : u ∈ K) : σ u ≠ 0 := by
    intro hz
    have hh := hsphere u hu
    simp [hz] at hh
  refine ⟨fluxDensity_integrable hK hU hKU hσ hn,
    (areaDensity_continuousOn hU hKU hσ).integrableOn_compact hK, ?_⟩
  apply setIntegral_congr_fun hK.measurableSet
  intro u hu
  exact sphere_flux_density hu (hunique u hu)
    (((hσ u (hKU hu)).contDiffAt (hU.mem_nhds (hKU hu))).differentiableAt (by norm_num))
    hsphere (horient u hu)

/-- The geometric area is strictly positive for a regular patch on a compact
parameter set of positive measure. Rank deficiency is allowed by the separate
radial-invariance theorem, but not used to assert positive area here. -/
theorem parametricArea_pos {n p : ℕ} {σ : Space p → Space n}
    {K U : Set (Space p)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hvol : 0 < volume K)
    (hregular : ∀ u ∈ K, LinearIndependent ℝ
      (fun i => fderiv ℝ σ u (EuclideanSpace.single i 1))) :
    0 < parametricArea K σ := by
  have hi : IntegrableOn (areaDensity σ) K :=
    (areaDensity_continuousOn hU hKU hσ).integrableOn_compact hK
  have hpos (u) (hu : u ∈ K) : 0 < areaDensity σ u := by
    apply Real.sqrt_pos.mpr
    exact (Matrix.posDef_gram_of_linearIndependent (hregular u hu)).det_pos
  apply (integral_pos_iff_support_of_nonneg (fun _ => Real.sqrt_nonneg _) hi).mpr
  have hsub : K ⊆ Function.support (areaDensity σ) := by
    intro u hu
    exact (hpos u hu).ne'
  calc
    0 < (volume.restrict K) K := by simpa [hK.measurableSet] using hvol
    _ ≤ (volume.restrict K) (Function.support (areaDensity σ)) := measure_mono hsub

/-- Agreement with the source square-root formula for `r_k`. -/
theorem radius_source_formula {n k : ℕ} (h : k ≤ n) (x : Space n) :
    radius h x = Real.sqrt (∑ i : Fin k, x (i.castLE h)^2) := by
  simp [radius, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

/-- At top index, the source domain is exactly punctured Euclidean space. -/
theorem radialDomain_top (n : ℕ) : radialDomain (Nat.le_refl n) = {x : Space n | x ≠ 0} := by
  have he : firstCoordinates (Nat.le_refl n) = ContinuousLinearMap.id ℝ (Space n) := by
    ext x i
    rfl
  ext x
  simp [radialDomain, radius, he, norm_pos_iff]

/-- The convention is literally membership in the singleton image `{0}`
after restricting the form to its domain. -/
theorem exactOn_zero_image {n : ℕ} (ω : Form 0 (Space n)) (U : Set (Space n)) :
    ExactOn 0 ω U ↔ (fun x : U => ω x) ∈ ({0} : Set (U → Space n [⋀^Fin 0]→L[ℝ] ℝ)) := by
  simp only [Set.mem_singleton_iff, ExactOn, funext_iff, Pi.zero_apply]
  exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x,hx⟩⟩

/-- The separate `n=1` statement: closed but nonexact on the punctured line,
under the explicitly added degree-zero convention. -/
theorem dimension_one_closed_not_exact :
    (∀ x : Space 1, x ≠ 0 → extDeriv (omega 0 (by omega)) x = 0) ∧
    ¬ ExactOn 0 (omega 0 (by omega)) {x : Space 1 | x ≠ 0} := by
  have hd := radialDomain_top 1
  constructor
  · intro x hx
    apply omega_closed
    simpa [hd] using hx
  · simpa only [hd] using omega_one_not_exact (n := 1) (by omega)

/-- A nonzero standard-oriented frame in every dimension checks the
normalization and sign of the actual determinant form. -/
theorem coordinateVolume_standard (n : ℕ) :
    coordinateVolume n (fun i => EuclideanSpace.single i 1) = 1 := by
  rw [coordinateVolume_apply]
  have hm : (fun i j : Fin n => (EuclideanSpace.single i 1 : Space n) j) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [PiLp.single_apply, Matrix.one_apply, eq_comm]
  rw [hm, Matrix.det_one]

/-- In every dimension the radial form is nonzero on an outward orthonormal
frame. This is not an assumed sphere integral. -/
theorem topRadial_standard (n : ℕ) :
    topRadial n (EuclideanSpace.single 0 1)
      (fun i => EuclideanSpace.single i.succ 1) = 1 := by
  have hc : Matrix.vecCons (EuclideanSpace.single 0 1 : Space (n+1))
      (fun i : Fin n => EuclideanSpace.single i.succ 1) =
      fun i => EuclideanSpace.single i 1 := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change (‖(EuclideanSpace.single 0 1 : Space (n+1))‖ ^ (n+1))⁻¹ *
    coordinateVolume (n+1) (Matrix.vecCons (EuclideanSpace.single 0 1)
      (fun i => EuclideanSpace.single i.succ 1)) = 1
  rw [hc, coordinateVolume_standard]
  simp

/-- A concrete family satisfying the radial-invariance hypotheses in every
dimension: a constant unit direction and the nonconstant positive C² radius
`1+‖u‖²`. This includes the permitted rank-deficient case. -/
theorem compact_radial_model (n : ℕ) (K : Set (Space n)) (hK : IsCompact K) :
    parametricFlux K (fun u => (1+‖u‖^2) • (EuclideanSpace.single 0 1 : Space (n+1))) =
    parametricFlux K (fun _ => (EuclideanSpace.single 0 1 : Space (n+1))) := by
  have hρ : ContDiff ℝ 2 (fun u : Space n => (1 : ℝ)+‖u‖^2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  exact (compact_radial_invariance (U := univ) hK isOpen_univ (subset_univ K)
    contDiff_const.contDiffOn hρ.contDiffOn (fun _ _ => by simp)
    (fun _ _ => by positivity)).2.2.2.2

end Rudin.Chapter10.Exercise23

section
/-! # R10E23.b: the prescribed primitive

The source index is k=m+2. All identities hold on E_(m+1), in every
ambient dimension n ≥ m+2. This helper uses the frozen radial definitions.
-/

set_option backward.isDefEq.respectTransparency false
namespace Rudin.Chapter10.Exercise23.Primitive
open Set MeasureTheory ContinuousAlternatingMap
open scoped RealInnerProductSpace Topology
open Rudin.Support.SimplexIntegration
open Rudin.Chapter10.Exercise20

/-- The squared radii split at the last active coordinate. -/
theorem radius_sq_succ {n k : ℕ} (h : k+1 ≤ n) (x : Space n) :
    radius h x ^ 2 = radius (show k ≤ n by omega) x ^ 2 + x ⟨k, by omega⟩ ^ 2 := by
  simp only [radius, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_castSucc, firstCoordinates_apply]
  rfl

/-- On E_(k-1), the argument of the prescribed integral lies strictly inside its domain. -/
theorem ratio_mem_Ioo {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    x ⟨m+1, by omega⟩ / radius h x ∈ Ioo (-1 : ℝ) 1 := by
  have hs := radius_sq_succ h x
  have hp : 0 < radius (show m+1 ≤ n by omega) x := hx
  have hn : 0 ≤ radius h x := norm_nonneg _
  have hab : |x ⟨m+1, by omega⟩| < radius h x := by
    nlinarith [sq_abs (x ⟨m+1, by omega⟩), abs_nonneg (x ⟨m+1, by omega⟩), sq_pos_of_pos hp]
  have hr : 0 < radius h x := lt_of_le_of_lt (abs_nonneg _) hab
  constructor
  · rw [lt_div_iff₀ hr]
    linarith [neg_abs_le (x ⟨m+1, by omega⟩)]
  · rw [div_lt_iff₀ hr]
    linarith [le_abs_self (x ⟨m+1, by omega⟩)]

theorem radius_pos_succ {n k : ℕ} (h : k+1 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show k ≤ n by omega)) : 0 < radius h x := by
  have hs := radius_sq_succ h x
  have hp : 0 < radius (show k ≤ n by omega) x := hx
  have hn : 0 ≤ radius h x := norm_nonneg _
  nlinarith [sq_nonneg (x ⟨k, by omega⟩)]

/-- Actual differential of the Euclidean active radius. -/
theorem radius_hasFDerivAt {n k : ℕ} (h : k ≤ n) {x : Space n}
    (hx : 0 < radius h x) :
    HasFDerivAt (radius h) ((radius h x)⁻¹ •
      ((innerSL ℝ (firstCoordinates h x)).comp (firstCoordinates h))) x := by
  have hd := ((firstCoordinates h).hasFDerivAt (x := x)).norm_sq.sqrt
    (pow_ne_zero 2 hx.ne')
  have he : (fun y : Space n => Real.sqrt (‖firstCoordinates h y‖ ^ 2)) = radius h := by
    funext y
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he, Real.sqrt_sq (norm_nonneg _)] at hd
  convert! hd using 1
  ext v
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  dsimp [radius]
  ring

/-- Differential of the quotient used by the prescribed primitive. -/
def ratioDifferential {n m : ℕ} (h : m+2 ≤ n) (x : Space n) : Space n →L[ℝ] ℝ :=
  (radius h x)⁻¹ • EuclideanSpace.proj ⟨m+1, by omega⟩ -
    (x ⟨m+1, by omega⟩ / radius h x ^ 3) •
      ((innerSL ℝ (firstCoordinates h x)).comp (firstCoordinates h))

theorem ratio_hasFDerivAt {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : 0 < radius h x) :
    HasFDerivAt (fun y : Space n => y ⟨m+1, by omega⟩ / radius h y)
      (ratioDifferential h x) x := by
  have hd := (EuclideanSpace.proj (⟨m+1, by omega⟩ : Fin n)).hasFDerivAt.mul
    ((hasDerivAt_inv hx.ne').comp_hasFDerivAt x (radius_hasFDerivAt h hx))
  have he : ratioDifferential h x =
      x ⟨m+1, by omega⟩ • (-(radius h x ^ 2)⁻¹ •
        ((radius h x)⁻¹ • ((innerSL ℝ (firstCoordinates h x)).comp (firstCoordinates h)))) +
      (radius h x)⁻¹ • EuclideanSpace.proj ⟨m+1, by omega⟩ := by
    ext v
    simp only [ratioDifferential, _root_.sub_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp
    ring
  rw [he]
  convert! hd using 1

/-- The actual derivative of the composed, signed scalar factor. -/
theorem primitiveFactor_hasFDerivAt {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    HasFDerivAt (primitiveFactor m h)
      (((-1 : ℝ)^(m+2) *
        (1-(x ⟨m+1, by omega⟩ / radius h x)^2)^((((m+2 : ℕ) : ℝ)-3)/2)) •
        ratioDifferential h x) x := by
  have hd := ((g_hasDerivAt (by omega : 2 ≤ m+2) (ratio_mem_Ioo h hx)).comp_hasFDerivAt x
    (ratio_hasFDerivAt h (radius_pos_succ h hx))).const_mul ((-1 : ℝ)^(m+2))
  apply hd.congr_fderiv
  exact smul_smul _ _ _

/-- Cofactor identity with a covector that annihilates the first row.
The vectors and coefficients are arbitrary; no frame condition is used. -/
theorem cofactor_radial {m : ℕ} (x : Fin (m+2) → ℝ)
    (v : Fin (m+1) → Fin (m+2) → ℝ) (a : Fin (m+2) → ℝ)
    (ha : ∑ j, a j * x j = 0) :
    (∑ i : Fin (m+1), (-1 : ℝ)^i.val * (∑ j, a j * v i j) *
      Matrix.det (fun r c : Fin (m+1) =>
        Matrix.vecCons x (fun b => v (i.succAbove b)) r c.castSucc)) =
    (-1 : ℝ)^(m+2) * a (Fin.last (m+1)) *
      Matrix.det (Matrix.vecCons x v) := by
  classical
  let M : Matrix (Fin (m+2)) (Fin (m+2)) ℝ := Matrix.vecCons x v
  let D := M.updateCol (Fin.last (m+1)) (fun r => ∑ j, a j * M r j)
  have hD : D.det = a (Fin.last (m+1)) * M.det := by
    exact Matrix.det_updateCol_sum M _ a
  have he := Matrix.det_succ_column D (Fin.last (m+1))
  rw [Fin.sum_univ_succ] at he
  have hzero : D 0 (Fin.last (m+1)) = 0 := by
    simpa only [D, Matrix.updateCol_apply, ite_true, M, Matrix.cons_val_zero] using ha
  rw [hzero, mul_zero, zero_mul, zero_add] at he
  have hminor (i : Fin (m+1)) :
      D.submatrix i.succ.succAbove (Fin.last (m+1)).succAbove =
        (fun r c : Fin (m+1) =>
          Matrix.vecCons x (fun b => v (i.succAbove b)) r c.castSucc) := by
    ext r c
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, D,
      Matrix.updateCol_apply, Fin.castSucc_ne_last, ite_false]
    refine Fin.cases ?_ (fun b => ?_) r
    · simp [M, Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i)]
    · simp [M, Fin.succ_succAbove_succ]
  simp only [hminor, Fin.val_succ, Fin.val_last, D, Matrix.updateCol_apply, ite_true, M,
    Matrix.cons_val_succ] at he
  have hs : (-1 : ℝ)^(m+2) *
      (∑ i : Fin (m+1), (-1 : ℝ)^i.val * (∑ j, a j * v i j) *
        Matrix.det (fun r c : Fin (m+1) =>
          Matrix.vecCons x (fun b => v (i.succAbove b)) r c.castSucc)) =
      a (Fin.last (m+1)) * M.det := by
    rw [← hD, he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show i.val+1+(m+1) = (m+2)+i.val by omega, pow_add]
    ring
  have hsign : ((-1 : ℝ)^(m+2)) * ((-1 : ℝ)^(m+2)) = 1 := by
    rw [← mul_pow]; simp
  calc
    _ = 1 * _ := (one_mul _).symm
    _ = ((-1 : ℝ)^(m+2) * (-1 : ℝ)^(m+2)) * _ := by rw [hsign]
    _ = _ := by rw [mul_assoc, hs, ← mul_assoc]

/-- Positive-base real-power algebra. This includes the exponent -1/2 at k=2. -/
theorem power_coefficient (m : ℕ) {r R z : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hs : R^2 = r^2 + z^2) :
    (1-(z/R)^2)^((((m+2 : ℕ) : ℝ)-3)/2) * (R⁻¹-z^2/R^3) =
      r^(m+1)/R^(m+2) := by
  have ht : 0 < r/R := div_pos hr hR
  have ht2 : 0 < (r/R)^2 := sq_pos_of_pos ht
  have he : 1-(z/R)^2 = (r/R)^2 := by
    field_simp
    nlinarith
  have hb : R⁻¹-z^2/R^3 = (r/R)^2/R := by
    field_simp
    nlinarith
  rw [he, hb, ← mul_div_assoc]
  rw [← Real.rpow_add_one ht2.ne']
  have hexp : (((m+2 : ℕ) : ℝ)-3)/2 + 1 = (m+1 : ℕ)/2 := by push_cast; ring
  rw [hexp, ← Real.rpow_natCast (r/R) 2, ← Real.rpow_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * ((m+1 : ℕ)/2 : ℝ) = (m+1 : ℕ) by ring,
    Real.rpow_natCast, div_pow, div_div, pow_succ]
  rw [pow_succ R (m+1)]

/-- Coefficients of the actual differential in the active coordinates. -/
def factorCoefficients {n m : ℕ} (h : m+2 ≤ n) (x : Space n) (j : Fin (m+2)) : ℝ :=
  ((-1 : ℝ)^(m+2) * (1-(x ⟨m+1, by omega⟩ / radius h x)^2)^((((m+2 : ℕ) : ℝ)-3)/2)) *
    ((radius h x)⁻¹ * (if j = Fin.last (m+1) then 1 else 0) -
      x ⟨m+1, by omega⟩ / radius h x^3 * x (j.castLE h))

theorem factorCoefficients_apply {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) (v : Space n) :
    fderiv ℝ (primitiveFactor m h) x v =
      ∑ j, factorCoefficients h x j * v (j.castLE h) := by
  rw [(primitiveFactor_hasFDerivAt h hx).fderiv]
  simp only [factorCoefficients, ratioDifferential, _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, firstCoordinates_apply]
  simp only [mul_comm]
  rfl

/-- The first source hint: the genuine differential annihilates the radial vector. -/
theorem factorCoefficients_radial {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    ∑ j, factorCoefficients h x j * x (j.castLE h) = 0 := by
  rw [← factorCoefficients_apply h hx x, (primitiveFactor_hasFDerivAt h hx).fderiv]
  simp only [ratioDifferential, _root_.smul_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]
  change _ * ((radius h x)⁻¹ * x ⟨m+1, by omega⟩ -
    x ⟨m+1, by omega⟩ / radius h x^3 * radius h x^2) = 0
  have hr := (radius_pos_succ h hx).ne'
  field_simp
  ring

/-- The second source hint, including the source sign and normalization. -/
theorem factorCoefficients_last {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    factorCoefficients h x (Fin.last (m+1)) =
      (-1 : ℝ)^(m+2) * radius (show m+1 ≤ n by omega) x^(m+1) / radius h x^(m+2) := by
  simp only [factorCoefficients, ite_true, mul_one]
  change ((-1 : ℝ)^(m+2) * _) * ((radius h x)⁻¹ -
    x ⟨m+1, by omega⟩ / radius h x^3 * x ⟨m+1, by omega⟩) = _
  rw [show x ⟨m+1, by omega⟩ / radius h x^3 * x ⟨m+1, by omega⟩ =
    x ⟨m+1, by omega⟩^2 / radius h x^3 by ring, mul_assoc,
    power_coefficient m hx (radius_pos_succ h hx) (radius_sq_succ h x)]
  ring

/-- The signed wedge identity on all vectors, in every ambient dimension. -/
theorem differentialWedge_eq_omega {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    differentialWedge (primitiveFactor m h) (omega m (by omega)) x =
      omega (m+1) h x := by
  ext v
  rw [differentialWedge_apply]
  simp only [factorCoefficients_apply h hx]
  have he := cofactor_radial (fun j => x (j.castLE h))
    (fun i j => v i (j.castLE h)) (factorCoefficients h x) (factorCoefficients_radial h hx)
  have htop : omega (m+1) h x v = (radius h x^(m+2))⁻¹ *
      Matrix.det (Matrix.vecCons (fun j => x (j.castLE h)) (fun i j => v i (j.castLE h))) := by
    simp only [omega, topRadial, compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, curryLeft_apply_apply, coordinateVolume_apply]
    congr 1
    congr 1
    funext r c
    refine Fin.cases ?_ (fun b => ?_) r <;> rfl
  rw [htop]
  have hform (i : Fin (m+1)) :
      omega m (show m+1 ≤ n by omega) x (fun j => v (i.succAbove j)) =
      (radius (show m+1 ≤ n by omega) x^(m+1))⁻¹ *
        Matrix.det (fun r c : Fin (m+1) => Matrix.vecCons (fun j => x (j.castLE h))
          (fun b j => v (i.succAbove b) (j.castLE h)) r c.castSucc) := by
    simp only [omega, topRadial, compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, curryLeft_apply_apply, coordinateVolume_apply]
    congr 1
    congr 1
    funext r c
    refine Fin.cases ?_ (fun b => ?_) r <;> rfl
  simp only [hform]
  calc
    _ = (radius (show m+1 ≤ n by omega) x^(m+1))⁻¹ *
        (∑ i : Fin (m+1), (-1 : ℝ)^i.val * (∑ j, factorCoefficients h x j * v i (j.castLE h)) *
          Matrix.det (fun r c : Fin (m+1) => Matrix.vecCons (fun j => x (j.castLE h))
            (fun b j => v (i.succAbove b) (j.castLE h)) r c.castSucc)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [he, factorCoefficients_last h hx]
      change _ = (radius h x^(m+2))⁻¹ *
        Matrix.det (Matrix.vecCons (fun j => x (j.castLE h)) (fun i j => v i (j.castLE h)))
      have hs : ((-1 : ℝ)^(m+2)) * ((-1 : ℝ)^(m+2)) = 1 := by rw [← mul_pow]; simp
      have hr : radius (show m+1 ≤ n by omega) x ≠ 0 := ne_of_gt hx
      have hR := (radius_pos_succ h hx).ne'
      field_simp
      rw [sq, hs, one_mul]

/-- Regularity of the lower radial form on its source open domain. -/
theorem omega_contDiffAt {n m : ℕ} (h : m+1 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain h) : ContDiffAt ℝ 2 (omega m h) x := by
  have ht := (topRadial_contDiffAt (norm_pos_iff.mp hx)).comp x
    (firstCoordinates h).contDiff.contDiffAt
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (firstCoordinates h)).contDiff.contDiffAt.comp x ht

/-- The prescribed product has the actual exterior derivative required by the source. -/
theorem exterior_primitive {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    extDeriv (fun y => primitiveFactor m h y • omega m (show m+1 ≤ n by omega) y) x =
      omega (m+1) h x := by
  rw [exterior_product (primitiveFactor_hasFDerivAt h hx).differentiableAt
    ((omega_contDiffAt _ hx).differentiableAt (by norm_num)), omega_closed _ hx,
    smul_zero, zero_add, differentialWedge_eq_omega h hx]

/-- The prescribed integral is C¹ on its full open scalar domain. -/
theorem g_contDiffOn {k : ℕ} (hk : 2 ≤ k) :
    ContDiffOn ℝ 1 (g k) (Ioo (-1 : ℝ) 1) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun t ht => (g_hasDerivAt hk ht).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  have hc : ContinuousOn (fun t : ℝ => (1-t^2)^(((k : ℝ)-3)/2)) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_const.sub (continuousAt_id.pow 2)).rpow_const
    left
    have : 0 < 1-t^2 := by nlinarith [ht.1, ht.2]
    exact this.ne'
  exact hc.congr (fun t ht => (g_hasDerivAt hk ht).deriv)

/-- No regularity premise is added: C¹ follows from the integral and radius formulas. -/
theorem primitiveFactor_contDiffAt {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    ContDiffAt ℝ 1 (primitiveFactor m h) x := by
  have hr := radius_pos_succ h hx
  have hg : ContDiffAt ℝ 1 (g (m+2)) (x ⟨m+1, by omega⟩ / radius h x) :=
    (g_contDiffOn (by omega : 2 ≤ m+2) _ (ratio_mem_Ioo h hx)).contDiffAt
      (isOpen_Ioo.mem_nhds (ratio_mem_Ioo h hx))
  have hq : ContDiffAt ℝ 1 (fun y : Space n => y ⟨m+1, by omega⟩ / radius h y) x :=
    (EuclideanSpace.proj (⟨m+1, by omega⟩ : Fin n)).contDiff.contDiffAt.div
      ((firstCoordinates h).contDiff.contDiffAt.norm ℝ (norm_pos_iff.mp hr)) hr.ne'
  convert! (contDiffAt_const (c := (-1 : ℝ)^(m+2))).mul (hg.comp x hq) using 1

/-- The source's prescribed product is C¹ throughout E_(k-1). -/
theorem primitive_contDiffOn {n m : ℕ} (h : m+2 ≤ n) :
    ContDiffOn ℝ 1 (fun y => primitiveFactor m h y • omega m (show m+1 ≤ n by omega) y)
      (radialDomain (show m+1 ≤ n by omega)) := by
  intro x hx
  exact ((primitiveFactor_contDiffAt h hx).smul
    ((omega_contDiffAt _ hx).of_le (by norm_num))).contDiffWithinAt

/-- Part (b), with the exact prescribed scalar and the actual differential wedge.
Here the source index is k=m+2, with no restriction on unused ambient coordinates. -/
theorem prescribed_primitive {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    omega (m+1) h x =
        extDeriv (fun y => primitiveFactor m h y • omega m (show m+1 ≤ n by omega) y) x ∧
      extDeriv (fun y => primitiveFactor m h y • omega m (show m+1 ≤ n by omega) y) x =
        differentialWedge (primitiveFactor m h) (omega m (show m+1 ≤ n by omega)) x :=
  ⟨(exterior_primitive h hx).symm,
    (exterior_primitive h hx).trans (differentialWedge_eq_omega h hx).symm⟩

/-- Exactness is witnessed by the prescribed C¹ product, not by an assumed primitive. -/
theorem omega_exactOn {n m : ℕ} (h : m+2 ≤ n) :
    ExactOn (m+1) (omega (m+1) h) (radialDomain (show m+1 ≤ n by omega)) :=
  ⟨fun y => primitiveFactor m h y • omega m (show m+1 ≤ n by omega) y,
    primitive_contDiffOn h, fun _ hx => exterior_primitive h hx⟩

/-- The first differential equation in the source hint. -/
theorem primitiveFactor_radial {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    fderiv ℝ (primitiveFactor m h) x x = 0 := by
  rw [factorCoefficients_apply h hx, factorCoefficients_radial h hx]

/-- The last active partial derivative, with the exact source constant. -/
theorem primitiveFactor_last {n m : ℕ} (h : m+2 ≤ n) {x : Space n}
    (hx : x ∈ radialDomain (show m+1 ≤ n by omega)) :
    fderiv ℝ (primitiveFactor m h) x (EuclideanSpace.single ⟨m+1, by omega⟩ 1) =
      (-1 : ℝ)^(m+2) * radius (show m+1 ≤ n by omega) x^(m+1) / radius h x^(m+2) := by
  rw [factorCoefficients_apply h hx]
  have he (j : Fin (m+2)) :
      (EuclideanSpace.single (⟨m+1, by omega⟩ : Fin n) 1) (j.castLE h) =
        if j = Fin.last (m+1) then (1 : ℝ) else 0 := by
    simp [EuclideanSpace.single, PiLp.single_apply, Fin.ext_iff]
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact factorCoefficients_last h hx

end Rudin.Chapter10.Exercise23.Primitive
end

section
namespace Rudin.Chapter10.Exercise23.Sphere
open Set MeasureTheory
open scoped Topology
open Rudin.Support.SimplexIntegration Rudin.Support.SmoothChains

/-- The affine simplex with vertices `(-1,...,-1)` and its translates by
`n+1` times each coordinate vector. The origin has all weights `1/(n+1)`. -/
def solid (n : ℕ) : Simplex n (Space n) :=
  ⟨fun u => (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => -1 + (n+1 : ℝ) * u j),
    univ, isOpen_univ, subset_univ _, by
      apply ContDiff.contDiffOn
      apply (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp
      exact contDiff_pi.mpr fun j => contDiff_const.add
        (contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff)⟩

@[simp] theorem solid_apply (n : ℕ) (u : Space n) (j : Fin n) :
    (solid n).val u j = -1 + (n+1 : ℝ) * u j := rfl

/-- The supporting linear functions, before translation by one. -/
def supportValue {n : ℕ} (x : Space n) : Fin (n+1) → ℝ :=
  Fin.cons (∑ j, x j) (fun j => -x j)

/-- Each barycentric weight is the slack in one supporting inequality. -/
theorem solid_support {n : ℕ} (u : Space n) (i : Fin (n+1)) :
    supportValue ((solid n).val u) i = 1 - (n+1 : ℝ) * weights u i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [supportValue, Fin.cons_zero, solid_apply, weights, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  · simp [supportValue, weights]; ring

/-- Every point on the full affine face lies in its supporting hyperplane. -/
theorem face_support {n : ℕ} (i : Fin (n+2)) (u : Space n) :
    supportValue (((solid (n+1)).face i).val u) i = 1 := by
  change supportValue ((solid (n+1)).val (relabel i.succAbove u)) i = 1
  rw [solid_support, weights_face]
  simp

/-- The full face, not only its relative interior, avoids the singular point. -/
theorem face_ne_zero {n : ℕ} (i : Fin (n+2)) (u : Space n) :
    ((solid (n+1)).face i).val u ≠ 0 := by
  intro hz
  have h := face_support i u
  rw [hz] at h
  have he : supportValue (0 : Space (n+1)) i = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [supportValue]
  linarith

/-- The face with its certified punctured-space image. -/
def puncturedFace (n : ℕ) (i : Fin (n+2)) :
    InDomain n {x : Space (n+1) | x ≠ 0} :=
  ⟨(solid (n+1)).face i, fun u _ => face_ne_zero i u⟩

/-- The actual affine boundary chain, with its boundary orientation. -/
def polyhedronBoundary (n : ℕ) : DomainChain n {x : Space (n+1) | x ≠ 0} :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • FreeAbelianGroup.of (puncturedFace n i)

theorem forget_polyhedronBoundary (n : ℕ) :
    forgetDomain n _ (polyhedronBoundary n) = boundary n (simplex (solid (n+1))) := by
  rw [boundary_simplex]
  simp [polyhedronBoundary, forgetDomain, puncturedFace, simplex]

/-- Cancellation follows from literal face restrictions and boundary squared. -/
theorem polyhedronBoundary_closed (n : ℕ) :
    domainBoundary n _ (polyhedronBoundary (n+1)) = 0 := by
  apply forgetDomain_injective n _
  rw [forgetDomain_boundary, forget_polyhedronBoundary, boundary_squared, map_zero]

theorem normalize_contDiffOn (n : ℕ) :
    ContDiffOn ℝ 2 (normalize : Space n → Space n) {x | x ≠ 0} :=
  fun _ hx => (normalize_contDiffAt hx).contDiffWithinAt

/-- The sphere chain normalizes every entire affine face. -/
def sphereChain (n : ℕ) : Chain n (Space (n+1)) :=
  mapOnChain n normalize {x | x ≠ 0} isOpen_ne (normalize_contDiffOn _) (polyhedronBoundary n)

/-- Nonlinear postcomposition preserves cancellation on the full boundary. -/
theorem sphereChain_closed (n : ℕ) : boundary n (sphereChain (n+1)) = 0 := by
  rw [sphereChain, boundary_mapOnChain, polyhedronBoundary_closed, map_zero]

/-- Each chart is the radial projection of an actual face. -/
def sphereFace (n : ℕ) (i : Fin (n+2)) : Simplex n (Space (n+1)) :=
  (puncturedFace n i).val.mapOn normalize {x | x ≠ 0} isOpen_ne
    (normalize_contDiffOn _) (puncturedFace n i).property

@[simp] theorem sphereFace_apply (n : ℕ) (i : Fin (n+2)) (u : Space n) :
    (sphereFace n i).val u = normalize (((solid (n+1)).face i).val u) := rfl

theorem sphereFace_norm (n : ℕ) (i : Fin (n+2)) (u : Space n) :
    ‖(sphereFace n i).val u‖ = 1 := normalize_norm (face_ne_zero i u)

theorem sphereChain_faces (n : ℕ) : sphereChain n =
    ∑ i : Fin (n+2), (-1 : ℤ)^i.val • simplex (sphereFace n i) := by
  simp [sphereChain, polyhedronBoundary, mapOnChain, simplex, sphereFace]

/-- Cartesian parameters reconstructed from barycentric coordinates. -/
def fromWeights {n : ℕ} (w : Fin (n+1) → ℝ) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => w j.succ)

theorem weights_fromWeights {n : ℕ} (w : Fin (n+1) → ℝ) (hw : ∑ i, w i = 1) :
    weights (fromWeights w) = w := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  rw [Fin.sum_univ_succ] at hw
  change 1 - ∑ j : Fin n, w j.succ = w 0
  linarith

theorem weights_injective {n : ℕ} : Function.Injective (weights (n := n)) := by
  intro u v h
  ext j
  exact congrFun h j.succ

/-- A zero barycentric coordinate gives an actual face parameter, including
all edges and vertices. -/
theorem face_parameter {n : ℕ} {u : Space (n+1)}
    (hu : u ∈ standardSimplex (n+1)) (i : Fin (n+2)) (hi : weights u i = 0) :
    ∃ v ∈ standardSimplex n, relabel i.succAbove v = u := by
  let w := fun j => weights u (i.succAbove j)
  have hw : ∑ j, w j = 1 := by
    have h := sum_weights u
    rw [Fin.sum_univ_succAbove _ i, hi, zero_add] at h
    exact h
  refine ⟨fromWeights w, ?_, ?_⟩
  · rw [mem_simplex_iff_weights, weights_fromWeights w hw]
    exact fun j => (mem_simplex_iff_weights u).mp hu _
  · apply weights_injective
    rw [weights_face, weights_fromWeights w hw]
    funext j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa using hi.symm
    · simp [w]

/-- An explicit inverse to the affine solid map. -/
def solidInverse {n : ℕ} (x : Space n) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => (x j + 1)/(n+1 : ℝ))

theorem solid_right_inverse {n : ℕ} (x : Space n) :
    (solid n).val (solidInverse x) = x := by
  ext j
  change -1 + (n+1 : ℝ) * ((x j+1)/(n+1 : ℝ)) = x j
  have h : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem solid_left_inverse {n : ℕ} (u : Space n) :
    solidInverse ((solid n).val u) = u := by
  ext j
  change ((-1+(n+1 : ℝ)*u j)+1)/(n+1 : ℝ) = u j
  have h : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem solid_mem_iff {n : ℕ} (x : Space n) :
    solidInverse x ∈ standardSimplex n ↔ ∀ i, supportValue x i ≤ 1 := by
  rw [mem_simplex_iff_weights]
  have h (i) := solid_support (solidInverse x) i
  rw [solid_right_inverse] at h
  constructor
  · intro hw i
    rw [h i]
    have hn : (0 : ℝ) < n+1 := by positivity
    nlinarith [hw i]
  · intro hs i
    have hn : (0 : ℝ) < n+1 := by positivity
    have hh := hs i
    rw [h i] at hh
    nlinarith

/-- The maximum supporting linear value on any nonzero ray is positive. -/
theorem exists_support_max {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ∃ i : Fin (n+1), 0 < supportValue x i ∧ ∀ j, supportValue x j ≤ supportValue x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (supportValue x) Finset.univ_nonempty
  have hm : ∀ j, supportValue x j ≤ supportValue x i := fun j => hi j (Finset.mem_univ j)
  refine ⟨i, ?_, hm⟩
  by_contra hp
  have hn : ∀ j, 0 ≤ x j := by
    intro j
    have h := (hm j.succ).trans (le_of_not_gt hp)
    simpa [supportValue] using h
  have hs : ∑ j, x j ≤ 0 := (hm 0).trans (le_of_not_gt hp)
  apply hx
  ext j
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hn k) (Finset.mem_univ j)
  exact le_antisymm (hh.trans hs) (hn j)

theorem supportValue_smul {n : ℕ} (r : ℝ) (x : Space n) (i : Fin (n+1)) :
    supportValue (r • x) i = r * supportValue x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [supportValue, Finset.mul_sum]
  · simp [supportValue]

/-- Every unit vector is the normalization of a point on an actual face.
This is coverage of the whole sphere, not just of a patch. -/
theorem sphere_coverage {n : ℕ} {x : Space (n+1)} (hx : ‖x‖ = 1) :
    ∃ i : Fin (n+2), ∃ u ∈ standardSimplex n, (sphereFace n i).val u = x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨i, hi, hmax⟩ := exists_support_max hx0
  let r := (supportValue x i)⁻¹
  let y := r • x
  have hr : 0 < r := inv_pos.mpr hi
  have hy (j) : supportValue y j ≤ 1 := by
    rw [supportValue_smul]
    calc
      r * supportValue x j ≤ r * supportValue x i := mul_le_mul_of_nonneg_left (hmax j) hr.le
      _ = 1 := inv_mul_cancel₀ hi.ne'
  have hyi : supportValue y i = 1 := by
    rw [supportValue_smul]
    exact inv_mul_cancel₀ hi.ne'
  have hu : solidInverse y ∈ standardSimplex (n+1) := (solid_mem_iff y).mpr hy
  have hui : weights (solidInverse y) i = 0 := by
    have h := solid_support (solidInverse y) i
    rw [solid_right_inverse, hyi] at h
    have hn : (0 : ℝ) < (n+1 : ℕ)+1 := by positivity
    nlinarith
  obtain ⟨u, hu, he⟩ := face_parameter hu i hui
  refine ⟨i, u, hu, ?_⟩
  rw [sphereFace_apply]
  change normalize ((solid (n+1)).val (relabel i.succAbove u)) = x
  rw [he, solid_right_inverse]
  simp [y, normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx,
    smul_smul, inv_mul_cancel₀ hr.ne']

/-- The union of the actual compact chart images is exactly the unit sphere. -/
theorem wholeSphere :
    ∀ n, (⋃ i : Fin (n+2), (sphereFace n i).val '' standardSimplex n) =
      {x : Space (n+1) | ‖x‖ = 1} := by
  intro n
  ext x
  simp only [mem_iUnion, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨i, u, _, rfl⟩
    exact sphereFace_norm n i u
  · exact sphere_coverage

/-- The closed affine simplex is the intersection of its supporting halfspaces. -/
def polyhedronSurface (n : ℕ) : Set (Space n) :=
  {x | (∀ i, supportValue x i ≤ 1) ∧ ∃ i, supportValue x i = 1}

theorem face_mem_surface {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) : ((solid (n+1)).face i).val u ∈ polyhedronSurface (n+1) := by
  refine ⟨?_, i, face_support i u⟩
  intro j
  change supportValue ((solid (n+1)).val (relabel i.succAbove u)) j ≤ 1
  rw [solid_support]
  have h := (mem_simplex_iff_weights _).mp (relabel_mem i.succAbove hu) j
  have hn : (0 : ℝ) < (n+1 : ℕ)+1 := by positivity
  nlinarith

/-- A ray meets this polyhedron boundary at only one point. -/
theorem surface_ray_unique {n : ℕ} {y z : Space n}
    (hy : y ∈ polyhedronSurface n) (hz : z ∈ polyhedronSurface n)
    {r : ℝ} (hr : 0 < r) (he : y = r • z) : r = 1 := by
  obtain ⟨i, hi⟩ := hy.2
  obtain ⟨j, hj⟩ := hz.2
  have hle := hy.1 j
  rw [he, supportValue_smul, hj, mul_one] at hle
  have hge := mul_le_mul_of_nonneg_left (hz.1 i) hr.le
  rw [← supportValue_smul, ← he, hi, mul_one] at hge
  exact le_antisymm hle hge

theorem norm_smul_normalize {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ‖x‖ • normalize x = x := by
  simp [normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Normalization is injective on the complete affine boundary. -/
theorem normalize_surface_injective {n : ℕ} {y z : Space n}
    (hy : y ∈ polyhedronSurface n) (hz : z ∈ polyhedronSurface n)
    (hy0 : y ≠ 0) (hz0 : z ≠ 0) (he : normalize y = normalize z) : y = z := by
  have hr : 0 < ‖y‖ / ‖z‖ := div_pos (norm_pos_iff.mpr hy0) (norm_pos_iff.mpr hz0)
  have hs : y = (‖y‖ / ‖z‖) • z := calc
    y = ‖y‖ • normalize y := (norm_smul_normalize hy0).symm
    _ = ‖y‖ • normalize z := congrArg (fun t => ‖y‖ • t) he
    _ = (‖y‖ / ‖z‖) • z := by simp [normalize, smul_smul, div_eq_mul_inv]
  rw [surface_ray_unique hy hz hr hs, one_smul] at hs
  exact hs

/-- Charts have no self-overlap, even on their boundary. -/
theorem sphereFace_injective {n : ℕ} (i : Fin (n+2)) :
    InjOn (sphereFace n i).val (standardSimplex n) := by
  intro u hu v hv he
  have h := normalize_surface_injective (face_mem_surface i hu) (face_mem_surface i hv)
    (face_ne_zero i u) (face_ne_zero i v) he
  have h' := congrArg solidInverse h
  change solidInverse ((solid (n+1)).val (relabel i.succAbove u)) =
    solidInverse ((solid (n+1)).val (relabel i.succAbove v)) at h'
  simp only [solid_left_inverse] at h'
  have hw := congrArg weights h'
  rw [weights_face, weights_face] at hw
  apply weights_injective
  funext j
  have hj := congrFun hw (i.succAbove j)
  simpa using hj

/-- Strict barycentric inequalities describe the parameter simplex interior. -/
def strictSimplex (n : ℕ) : Set (Space n) := {u | ∀ i, 0 < weights u i}

theorem strictSimplex_isOpen (n : ℕ) : IsOpen (strictSimplex n) := by
  simp only [strictSimplex, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (weights_smooth i).continuous

theorem strictSimplex_subset (n : ℕ) : strictSimplex n ⊆ standardSimplex n := by
  intro u hu
  exact (mem_simplex_iff_weights u).mpr fun i => (hu i).le

/-- The centroid has strictly positive barycentric coordinates in every dimension. -/
def centroid (n : ℕ) : Space n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => (n+1 : ℝ)⁻¹)

theorem weights_centroid (n : ℕ) (i : Fin (n+1)) :
    weights (centroid n) i = (n+1 : ℝ)⁻¹ := by
  refine Fin.cases ?_ (fun j => rfl) i
  change 1 - ∑ _j : Fin n, (n+1 : ℝ)⁻¹ = (n+1 : ℝ)⁻¹
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem centroid_mem_strict (n : ℕ) : centroid n ∈ strictSimplex n := by
  intro i
  rw [weights_centroid]
  positivity

theorem simplex_interior_nonempty (n : ℕ) : (interior (standardSimplex n)).Nonempty :=
  ⟨centroid n, (interior_mono (strictSimplex_subset n))
    (by rw [(strictSimplex_isOpen n).interior_eq]; exact centroid_mem_strict n)⟩

theorem simplex_convex (n : ℕ) : Convex ℝ (standardSimplex n) := by
  intro u hu v hv a b ha hb hab
  constructor
  · intro j
    change 0 ≤ a * u j + b * v j
    exact add_nonneg (mul_nonneg ha (hu.1 j)) (mul_nonneg hb (hv.1 j))
  · change (∑ j, (a * u j + b * v j)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hu.2 ha, mul_le_mul_of_nonneg_left hv.2 hb]

/-- Unique differentiation is proved for the actual compact parameter simplex. -/
theorem simplex_uniqueDiffOn (n : ℕ) : UniqueDiffOn ℝ (standardSimplex n) :=
  uniqueDiffOn_convex (simplex_convex n) (simplex_interior_nonempty n)

/-- Positive measure is geometric and independent of a flux integral. -/
theorem simplex_volume_pos (n : ℕ) : 0 < volume (standardSimplex n) :=
  Measure.measure_pos_of_nonempty_interior _ (simplex_interior_nonempty n)

/-- Distinct charts have disjoint barycentric relative interiors. -/
theorem sphereFace_strict_disjoint {n : ℕ} {i j : Fin (n+2)} (hij : i ≠ j) :
    Disjoint ((sphereFace n i).val '' strictSimplex n)
      ((sphereFace n j).val '' strictSimplex n) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  have h := normalize_surface_injective
    (face_mem_surface j (strictSimplex_subset n hv))
    (face_mem_surface i (strictSimplex_subset n hu)) (face_ne_zero j v) (face_ne_zero i u) he
  have hh := congrArg solidInverse h
  change solidInverse ((solid (n+1)).val (relabel j.succAbove v)) =
    solidInverse ((solid (n+1)).val (relabel i.succAbove u)) at hh
  simp only [solid_left_inverse] at hh
  have hw := congrArg weights hh
  rw [weights_face, weights_face] at hw
  have hi := congrFun hw i
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
  have hz : weights v k = 0 := by
    have hz' : (j.insertNth (α := fun _ => ℝ) 0 (weights v)) i = 0 := by simpa using hi
    rw [← hk] at hz'
    simpa using hz'
  exact (hv k).ne' hz

theorem weights_line {n : ℕ} (u v : Space n) (t : ℝ) (i : Fin (n+1)) :
    weights ((1-t) • u + t • v) i = (1-t) * weights u i + t * weights v i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [weights, Fin.cons_zero, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · rfl

/-- Barycentric relative interiors here are exactly the ordinary interiors of
these full-dimensional parameter cells. -/
theorem strictSimplex_eq_interior (n : ℕ) : strictSimplex n = interior (standardSimplex n) := by
  apply subset_antisymm
  · exact (strictSimplex_isOpen n).subset_interior_iff.mpr (strictSimplex_subset n)
  · intro u hu i
    have hnon := (mem_simplex_iff_weights u).mp (interior_subset hu) i
    by_contra hn
    have hz : weights u i = 0 := le_antisymm (le_of_not_gt hn) hnon
    let line : ℝ → Space n := fun t => (1-t) • u + t • centroid n
    have hc : Continuous line := by unfold line; fun_prop
    have ht : Filter.Tendsto line (𝓝[<] (0 : ℝ)) (𝓝 u) := by
      have hh := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
      simpa [line] using hh
    have he : ∀ᶠ t in 𝓝[<] (0 : ℝ), line t ∈ standardSimplex n :=
      ht.eventually (mem_interior_iff_mem_nhds.mp hu)
    have hn' : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
    obtain ⟨t, htm, htneg⟩ := (he.and hn').exists
    have hw := (mem_simplex_iff_weights (line t)).mp htm i
    dsimp [line] at hw
    rw [weights_line, hz, weights_centroid, mul_zero, zero_add] at hw
    have hp : (0 : ℝ) < (n+1 : ℝ)⁻¹ := by positivity
    exact (mul_neg_of_neg_of_pos htneg hp).not_ge hw

/-- Distinct charts have disjoint parameter-interior images. -/
theorem sphereFace_interior_disjoint {n : ℕ} {i j : Fin (n+2)} (hij : i ≠ j) :
    Disjoint ((sphereFace n i).val '' interior (standardSimplex n))
      ((sphereFace n j).val '' interior (standardSimplex n)) := by
  rw [← strictSimplex_eq_interior]
  exact sphereFace_strict_disjoint hij

/-- A chart interior does not meet any other full chart, including its edges. -/
theorem sphereFace_interior_avoids_other {n : ℕ} {i j : Fin (n+2)} (hij : i ≠ j) :
    Disjoint ((sphereFace n i).val '' interior (standardSimplex n))
      ((sphereFace n j).val '' standardSimplex n) := by
  rw [← strictSimplex_eq_interior, Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  have h := normalize_surface_injective (face_mem_surface j hv)
    (face_mem_surface i (strictSimplex_subset n hu)) (face_ne_zero j v) (face_ne_zero i u) he
  have hh := congrArg solidInverse h
  change solidInverse ((solid (n+1)).val (relabel j.succAbove v)) =
    solidInverse ((solid (n+1)).val (relabel i.succAbove u)) at hh
  simp only [solid_left_inverse] at hh
  have hw := congrArg weights hh
  rw [weights_face, weights_face] at hw
  have hj := congrFun hw j
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : (i.insertNth (α := fun _ => ℝ) 0 (weights u)) j = 0 := by simpa using hj.symm
  rw [← hk] at hz
  have hz' : weights u k = 0 := by simpa using hz
  exact (hu k).ne' hz'

/-- All parameter seams have zero measure; they do not add area in the chart sum. -/
theorem simplex_frontier_volume (n : ℕ) : volume (frontier (standardSimplex n)) = 0 :=
  (simplex_convex n).addHaar_frontier volume

/-- Every overlap between different charts is confined to parameter seams. -/
theorem sphereFace_overlap_frontier {n : ℕ} {i j : Fin (n+2)} (hij : i ≠ j)
    {u v : Space n} (hu : u ∈ standardSimplex n) (hv : v ∈ standardSimplex n)
    (he : (sphereFace n i).val u = (sphereFace n j).val v) :
    u ∈ frontier (standardSimplex n) ∧ v ∈ frontier (standardSimplex n) := by
  have hi : u ∉ interior (standardSimplex n) := by
    intro h
    exact (Set.disjoint_left.mp (sphereFace_interior_avoids_other hij))
      ⟨u, h, rfl⟩ ⟨v, hv, he.symm⟩
  have hj : v ∉ interior (standardSimplex n) := by
    intro h
    exact (Set.disjoint_left.mp (sphereFace_interior_avoids_other hij.symm))
      ⟨v, h, rfl⟩ ⟨u, hu, he⟩
  exact ⟨⟨subset_closure hu, hi⟩, ⟨subset_closure hv, hj⟩⟩

theorem supportValue_continuous {n : ℕ} (i : Fin (n+1)) :
    Continuous (fun x : Space n => supportValue x i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun x : Space n => ∑ j, x j)
    exact continuous_finsetSum _ fun j _ => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.neg

/-- The solid simplex contains the origin strictly, in every ambient dimension. -/
theorem origin_mem_interior_solid (n : ℕ) :
    (0 : Space n) ∈ interior ((solid n).val '' standardSimplex n) := by
  let O : Set (Space n) := {x | ∀ i, supportValue x i < 1}
  have ho : IsOpen O := by
    simp only [O, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (supportValue_continuous i) continuous_const
  have hzero : (0 : Space n) ∈ O := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [supportValue]
  have hsub : O ⊆ (solid n).val '' standardSimplex n := by
    intro x hx
    exact ⟨solidInverse x, (solid_mem_iff x).mpr (fun i => (hx i).le), solid_right_inverse x⟩
  exact (ho.subset_interior_iff.mpr hsub) hzero

end Rudin.Chapter10.Exercise23.Sphere
end

section
namespace Rudin.Chapter10.Exercise23.Sphere
open Set MeasureTheory ContinuousAlternatingMap
open Rudin.Support.SimplexIntegration Rudin.Support.SmoothChains
open Rudin.Support.SmoothChainIntegration

/-- The coordinate contraction on an omitted ordered basis has its exact sign. -/
theorem coordinateVolume_omit {n : ℕ} (x : Space (n+1)) (i : Fin (n+1)) :
    coordinateVolume (n+1) (Matrix.vecCons x
      (fun j => EuclideanSpace.single (i.succAbove j) 1)) = (-1 : ℝ)^i.val * x i := by
  classical
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun a b =>
    (Matrix.vecCons x (fun j => EuclideanSpace.single (i.succAbove j) 1) a) b
  change M.det = _
  rw [Matrix.det_succ_column M i, Fin.sum_univ_succ]
  dsimp only [M]
  have hm : (fun a b : Fin n =>
      (EuclideanSpace.single (i.succAbove a) (1 : ℝ) : Space (n+1)) (i.succAbove b)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext a b
    simp [PiLp.single_apply, Matrix.one_apply, Fin.succAbove_right_injective.eq_iff, eq_comm]
  simp only [Matrix.vecCons, Fin.cons_zero, Fin.val_zero, zero_add, Matrix.submatrix,
    Fin.cons_succ, Fin.succAbove_zero]
  rw [hm]
  simp only [PiLp.single_apply, Fin.ne_succAbove, ↓reduceIte,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  change (-1 : ℝ)^i.val * x i * (1 : Matrix (Fin n) (Fin n) ℝ).det = _
  rw [Matrix.det_one, mul_one]

/-- The sloping-face frame has contraction equal to the coordinate sum. -/
theorem coordinateVolume_upper {n : ℕ} (x : Space (n+1)) :
    coordinateVolume (n+1) (Matrix.vecCons x
      (fun j => EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1)) = ∑ i, x i := by
  let A := ((coordinateVolume (n+1)).curryLeft x).compContinuousLinearMap
    (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm.toContinuousLinearMap
  have h := Rudin.Support.SimplexStokes.alternating_upperFace A
  change coordinateVolume (n+1) (Matrix.vecCons x
    (fun j => EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1)) =
    ∑ i : Fin (n+1), (-1 : ℝ)^i.val * coordinateVolume (n+1)
      (Matrix.vecCons x (fun j => EuclideanSpace.single (i.succAbove j) 1)) at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateVolume_omit, ← mul_assoc, ← pow_add]
  simp [← two_mul, pow_mul]

/-- The full affine solid has its expected actual derivative. -/
theorem solid_hasFDerivAt (n : ℕ) (u : Space n) :
    HasFDerivAt (solid n).val ((n+1 : ℝ) • ContinuousLinearMap.id ℝ (Space n)) u := by
  have he : (solid n).val = fun u =>
      (EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => (-1 : ℝ)) + (n+1 : ℝ) • u := by
    funext u
    ext j
    rfl
  rw [he]
  exact ((hasFDerivAt_id u).const_smul (n+1 : ℝ)).const_add _

theorem face_fderiv_basis {n : ℕ} (i : Fin (n+2)) (u : Space n) (j : Fin n) :
    fderiv ℝ ((solid (n+1)).face i).val u (EuclideanSpace.single j 1) =
      (n+2 : ℝ) • (vertex (i.succAbove j.succ) - vertex (i.succAbove 0)) := by
  change fderiv ℝ ((solid (n+1)).val ∘ relabel i.succAbove) u _ = _
  rw [fderiv_comp u (solid_hasFDerivAt _ _).differentiableAt
    (relabel_hasFDerivAt _ _).differentiableAt,
    (solid_hasFDerivAt _ _).fderiv, fderiv_relabel]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, relabelLinear_single, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem face_zero_fderiv_basis {n : ℕ} (u : Space n) (j : Fin n) :
    fderiv ℝ ((solid (n+1)).face 0).val u (EuclideanSpace.single j 1) =
      (n+2 : ℝ) • (EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1) := by
  rw [face_fderiv_basis]
  simp only [Fin.succAbove_zero, vertex_succ]

theorem face_succ_fderiv_basis {n : ℕ} (i : Fin (n+1)) (u : Space n) (j : Fin n) :
    fderiv ℝ ((solid (n+1)).face i.succ).val u (EuclideanSpace.single j 1) =
      (n+2 : ℝ) • EuclideanSpace.single (i.succAbove j) 1 := by
  rw [face_fderiv_basis]
  simp

/-- The actual boundary sign makes every affine face radial numerator positive. -/
theorem signed_face_determinant {n : ℕ} (i : Fin (n+2)) (u : Space n) :
    (-1 : ℝ)^i.val * coordinateVolume (n+1)
      (Matrix.vecCons (((solid (n+1)).face i).val u)
        (fun j => fderiv ℝ ((solid (n+1)).face i).val u (EuclideanSpace.single j 1))) =
      (n+2 : ℝ)^n := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [Fin.val_zero, pow_zero, one_mul, face_zero_fderiv_basis]
    change ((coordinateVolume (n+1)).curryLeft _)
      (fun j => (n+2 : ℝ) • (EuclideanSpace.single j.succ 1 - EuclideanSpace.single 0 1)) = _
    rw [map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    change (n+2 : ℝ)^n * coordinateVolume (n+1) (Matrix.vecCons _ _) = _
    rw [coordinateVolume_upper]
    have h := face_support (0 : Fin (n+2)) u
    change (∑ j, (((solid (n+1)).face 0).val u) j) = 1 at h
    rw [h, mul_one]
  · simp only [face_succ_fderiv_basis]
    change (-1 : ℝ)^k.succ.val * ((coordinateVolume (n+1)).curryLeft _)
      (fun j => (n+2 : ℝ) • EuclideanSpace.single (k.succAbove j) 1) = _
    rw [map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    change (-1 : ℝ)^k.succ.val * ((n+2 : ℝ)^n * coordinateVolume (n+1)
      (Matrix.vecCons _ (fun j => EuclideanSpace.single (k.succAbove j) 1))) = _
    rw [coordinateVolume_omit]
    have h := face_support k.succ u
    change -(((solid (n+1)).face k.succ).val u) k = 1 at h
    have hx : (((solid (n+1)).face k.succ).val u) k = -1 := by linarith
    rw [hx, Fin.val_succ, pow_succ]
    have hp : (-1 : ℝ)^k.val * (-1 : ℝ)^k.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc
      _ = (n+2 : ℝ)^n * ((-1 : ℝ)^k.val * (-1 : ℝ)^k.val) := by ring
      _ = _ := by rw [hp, mul_one]

/-- The solid simplex has positive Cartesian orientation, before taking its
alternating boundary. -/
theorem solid_positive_orientation (n : ℕ) (u : Space n) :
    coordinateVolume n (fun j => fderiv ℝ (solid n).val u (EuclideanSpace.single j 1)) =
      (n+1 : ℝ)^n ∧ 0 < (n+1 : ℝ)^n := by
  constructor
  · rw [(solid_hasFDerivAt n u).fderiv]
    change coordinateVolume n (fun j => (n+1 : ℝ) • EuclideanSpace.single j 1) = _
    rw [map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [coordinateVolume_standard, mul_one]
  · positivity

end Rudin.Chapter10.Exercise23.Sphere
end

section
namespace Rudin.Chapter10.Exercise23.Sphere
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support.SmoothChains
open Rudin.Support.SmoothChainIntegration Rudin.Support.MultivariateRiemann

/-- Each normalized face lies in the actual domain of the radial form. -/
theorem sphereFace_ne_zero (n : ℕ) (i : Fin (n+2)) (u : Space n) :
    (sphereFace n i).val u ≠ 0 := by
  intro h
  have hn := sphereFace_norm n i u
  rw [h, norm_zero] at hn
  norm_num at hn

def sphereDomainFace (n : ℕ) (i : Fin (n+2)) :
    InDomain n {x : Space (n+1) | x ≠ 0} :=
  ⟨sphereFace n i, fun u _ => sphereFace_ne_zero n i u⟩

def sphereDomainChain (n : ℕ) : DomainChain n {x : Space (n+1) | x ≠ 0} :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • FreeAbelianGroup.of (sphereDomainFace n i)

theorem forget_sphereDomainChain (n : ℕ) :
    forgetDomain n _ (sphereDomainChain n) = sphereChain n := by
  rw [sphereChain_faces]
  simp [forgetDomain, sphereDomainChain, sphereDomainFace, simplex]

/-- Actual Stokes forces every C¹ exact form to have zero sphere-chain integral. -/
theorem sphere_exact_integral_zero {n : ℕ} (η : Form n (Space (n+2)))
    (hη : ContDiffOn ℝ 1 η {x | x ≠ 0}) :
    integral (extDeriv η) (sphereChain (n+1)) = 0 := by
  rw [← forget_sphereDomainChain]
  rw [Rudin.Support.SimplexStokes.domainChain_stokes η isOpen_ne hη,
    forget_sphereDomainChain, sphereChain_closed, map_zero]

/-- The literal source repeated Riemann integrals exist for each full sphere
face in every coordinate order. -/
theorem sphereFace_source (n : ℕ) (i : Fin (n+2)) :
    IntegrableOn (fluxDensity (sphereFace n i).val) (standardSimplex n) ∧
    ∀ σ : Equiv.Perm (Fin n), HasSourceIntegral n 0 1
      (simplexZeroExtension (fluxDensity (sphereFace n i).val ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ coordinatePermutation σ)
      (integral (topRadial n) (simplex (sphereFace n i))) := by
  apply orientedIntegral_source_on (topRadial n) (sphereFace n i)
    (U := {x | x ≠ 0})
  · exact fun x hx => ((topRadial_contDiffAt hx).of_le (by norm_num)).contDiffWithinAt
  · rintro x ⟨u, _, rfl⟩
    exact sphereFace_ne_zero n i u

/-- Source Riemann witnesses for geometric Gram density, independently of flux. -/
theorem sphereFace_area_source (n : ℕ) (i : Fin (n+2)) :
    IntegrableOn (areaDensity (sphereFace n i).val) (standardSimplex n) ∧
    ∀ σ : Equiv.Perm (Fin n), HasSourceIntegral n 0 1
      (simplexZeroExtension (areaDensity (sphereFace n i).val ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ coordinatePermutation σ)
      (parametricArea (standardSimplex n) (sphereFace n i).val) := by
  obtain ⟨U, hU, hKU, hS⟩ := (sphereFace n i).property
  have hc := areaDensity_continuousOn hU hKU hS
  exact ⟨hc.integrableOn_compact (standardSimplex_isCompact n),
    fun σ => (euclidean_simplex_source hc σ).2.1⟩

/-- For compact convex parameter domains, source repeated integrals use the
literal closed-domain zero extension. This includes every compact cell and
simplex, without any rank condition. -/
theorem compact_flux_source {n : ℕ} {K U : Set (Space n)}
    {σ : Space n → Space (n+1)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hne : ∀ u ∈ K, σ u ≠ 0) :
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      K ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b ∧
      IntegrableOn (fluxDensity σ) K ∧ ∀ π : Equiv.Perm (Fin n),
      HasSourceIntegral n (a ∘ π) (b ∘ π)
        (K.indicator (fluxDensity σ) ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
          coordinatePermutation π) (parametricFlux K σ) :=
  Rudin.Chapter10.Exercise01.existence_real hK hconv
    (fluxDensity_continuousOn hU hKU hσ hne)

/-- The fixed radial-invariance extension, with source integral witnesses for
both maps and with the same oriented integral value. -/
theorem compact_radial_source {n : ℕ} {K U : Set (Space n)}
    {σ : Space n → Space (n+1)} {ρ : Space n → ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hρ : ContDiffOn ℝ 2 ρ U)
    (hsphere : ∀ u ∈ K, ‖σ u‖ = 1) (hpos : ∀ u ∈ K, 0 < ρ u) :
    (∀ u ∈ K, pullback (topRadial n) (fun z => ρ z • σ z) u = pullback (topRadial n) σ u) ∧
    IntegrableOn (fluxDensity σ) K ∧ IntegrableOn (fluxDensity (fun z => ρ z • σ z)) K ∧
    parametricFlux K (fun z => ρ z • σ z) = parametricFlux K σ ∧
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      K ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b ∧
      ∀ π : Equiv.Perm (Fin n),
      HasSourceIntegral n (a ∘ π) (b ∘ π)
        (K.indicator (fluxDensity σ) ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
          coordinatePermutation π) (parametricFlux K σ) ∧
      HasSourceIntegral n (a ∘ π) (b ∘ π)
        (K.indicator (fluxDensity (fun z => ρ z • σ z)) ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation π) (parametricFlux K σ) := by
  obtain ⟨hnr, he, hi, hir, hv⟩ := compact_radial_invariance hK hU hKU hσ hρ hsphere hpos
  have hn (u) (hu : u ∈ K) : σ u ≠ 0 := by
    intro hz
    have hh := hsphere u hu
    simp [hz] at hh
  obtain ⟨a, b, hab, hbox, _, hs⟩ := compact_flux_source hK hconv hU hKU hσ hn
  refine ⟨he, hi, hir, hv, a, b, hab, hbox, fun π => ⟨hs π, ?_⟩⟩
  apply source_congr (fun i => (hab (π i)).le) ?_ (hs π)
  intro x _hx
  simp only [Function.comp_apply]
  by_cases hm : (EuclideanSpace.equiv (Fin n) ℝ).symm (coordinatePermutation π x) ∈ K
  · simp only [indicator_of_mem hm]
    exact (congrArg (fun A => A (fun i => EuclideanSpace.single i 1)) (he _ hm)).symm
  · simp only [indicator_of_notMem hm]

/-- Actual compact Cartesian parameter cells in Euclidean coordinates. -/
def compactCell {n : ℕ} (a b : Fin n → ℝ) : Set (Space n) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b

theorem compactCell_isCompact {n : ℕ} (a b : Fin n → ℝ) : IsCompact (compactCell a b) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

theorem compactCell_convex {n : ℕ} (a b : Fin n → ℝ) : Convex ℝ (compactCell a b) :=
  (convex_Icc a b).linear_preimage (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap

/-- Source witnesses for the actual simplex, with no abstract convexity or
unique-differentiation premise remaining. -/
theorem simplex_radial_source {n : ℕ} {U : Set (Space n)}
    {σ : Space n → Space (n+1)} {ρ : Space n → ℝ}
    (hU : IsOpen U) (hKU : standardSimplex n ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hρ : ContDiffOn ℝ 2 ρ U)
    (hsphere : ∀ u ∈ standardSimplex n, ‖σ u‖ = 1)
    (hpos : ∀ u ∈ standardSimplex n, 0 < ρ u) :
    ∀ π : Equiv.Perm (Fin n),
      HasSourceIntegral n 0 1
        (simplexZeroExtension (fluxDensity σ ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘
          coordinatePermutation π) (parametricFlux (standardSimplex n) σ) ∧
      HasSourceIntegral n 0 1
        (simplexZeroExtension (fluxDensity (fun z => ρ z • σ z) ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ coordinatePermutation π)
        (parametricFlux (standardSimplex n) σ) := by
  have hn (u) (hu : u ∈ standardSimplex n) : σ u ≠ 0 := by
    intro hz
    have hh := hsphere u hu
    simp [hz] at hh
  have hc := fluxDensity_continuousOn hU hKU hσ hn
  have hcr := fluxDensity_continuousOn hU hKU (hρ.smul hσ)
    (fun u hu => radial_nonzero (hsphere u hu) (hpos u hu))
  have he := (compact_radial_invariance (standardSimplex_isCompact n) hU hKU hσ hρ hsphere hpos).2.2.2.2
  intro π
  refine ⟨(euclidean_simplex_source hc π).2.1, ?_⟩
  rw [← he]
  exact (euclidean_simplex_source hcr π).2.1

/-- The fixed radial extension on compact cells, including empty or degenerate
cells. The conclusion includes literal source witnesses for both maps. -/
theorem cell_radial_source {n : ℕ} (a b : Fin n → ℝ) {U : Set (Space n)}
    {σ : Space n → Space (n+1)} {ρ : Space n → ℝ}
    (hU : IsOpen U) (hKU : compactCell a b ⊆ U)
    (hσ : ContDiffOn ℝ 2 σ U) (hρ : ContDiffOn ℝ 2 ρ U)
    (hsphere : ∀ u ∈ compactCell a b, ‖σ u‖ = 1)
    (hpos : ∀ u ∈ compactCell a b, 0 < ρ u) :
    (∀ u ∈ compactCell a b, pullback (topRadial n) (fun z => ρ z • σ z) u =
      pullback (topRadial n) σ u) ∧
    IntegrableOn (fluxDensity σ) (compactCell a b) ∧
    IntegrableOn (fluxDensity (fun z => ρ z • σ z)) (compactCell a b) ∧
    parametricFlux (compactCell a b) (fun z => ρ z • σ z) = parametricFlux (compactCell a b) σ ∧
    ∃ c d : Fin n → ℝ, (∀ i, c i < d i) ∧
      compactCell a b ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc c d ∧
      ∀ π : Equiv.Perm (Fin n),
      HasSourceIntegral n (c ∘ π) (d ∘ π)
        ((compactCell a b).indicator (fluxDensity σ) ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
          coordinatePermutation π) (parametricFlux (compactCell a b) σ) ∧
      HasSourceIntegral n (c ∘ π) (d ∘ π)
        ((compactCell a b).indicator (fluxDensity (fun z => ρ z • σ z)) ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation π)
        (parametricFlux (compactCell a b) σ) :=
  compact_radial_source (compactCell_isCompact a b) (compactCell_convex a b)
    hU hKU hσ hρ hsphere hpos

end Rudin.Chapter10.Exercise23.Sphere
end

section
namespace Rudin.Chapter10.Exercise23.Sphere
open Set MeasureTheory
open scoped RealInnerProductSpace
open Rudin.Support.SimplexIntegration Rudin.Support.SmoothChains
open Rudin.Support.SmoothChainIntegration

/-- Radial projection preserves each actual face coefficient. -/
theorem sphereFace_flux {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    fluxDensity (sphereFace n i).val u = fluxDensity ((solid (n+1)).face i).val u := by
  have hF := ((solid (n+1)).face i).differentiableAt hu
  have hN := (normalize_contDiffAt (face_ne_zero i u)).differentiableAt (by norm_num)
  have h := pullback_comp (topRadial n) normalize ((solid (n+1)).face i).val u hN hF
  change pullback (topRadial n) (normalize ∘ ((solid (n+1)).face i).val) u _ = _
  rw [h]
  change (pullback (topRadial n) normalize (((solid (n+1)).face i).val u)) _ = _
  rw [normalize_pullback (face_ne_zero i u)]
  rfl

/-- The signed coefficient has a positive, explicit formula. -/
theorem signed_sphereFace_flux {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    (-1 : ℝ)^i.val * fluxDensity (sphereFace n i).val u =
      (n+2 : ℝ)^n / ‖((solid (n+1)).face i).val u‖^(n+1) := by
  rw [sphereFace_flux i hu]
  change (-1 : ℝ)^i.val * ((‖((solid (n+1)).face i).val u‖^(n+1))⁻¹ *
    coordinateVolume (n+1) (Matrix.vecCons _ _)) = _
  rw [← mul_assoc, mul_comm ((-1 : ℝ)^i.val), mul_assoc]
  have h := congrArg (fun t : ℝ => (‖((solid (n+1)).face i).val u‖^(n+1))⁻¹ * t)
    (signed_face_determinant i u)
  calc
    _ = _ := h
    _ = _ := (div_eq_inv_mul _ _).symm

theorem signed_sphereFace_flux_pos {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) : 0 < (-1 : ℝ)^i.val * fluxDensity (sphereFace n i).val u := by
  rw [signed_sphereFace_flux i hu]
  exact div_pos (pow_pos (by positivity) _) (pow_pos (norm_pos_iff.mpr (face_ne_zero i u)) _)

/-- On a unit sphere the flux coefficient is the outward-normal-first determinant. -/
theorem sphereFace_flux_determinant {n : ℕ} (i : Fin (n+2)) (u : Space n) :
    fluxDensity (sphereFace n i).val u = coordinateVolume (n+1)
      (Matrix.vecCons ((sphereFace n i).val u)
        (fun j => fderiv ℝ (sphereFace n i).val u (EuclideanSpace.single j 1))) := by
  change (‖(sphereFace n i).val u‖^(n+1))⁻¹ * _ = _
  rw [sphereFace_norm, one_pow, inv_one, one_mul]
  rfl

/-- The boundary signs give the unit ball's outward-normal-first orientation. -/
theorem sphereFace_outward {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    0 < (-1 : ℝ)^i.val * coordinateVolume (n+1)
      (Matrix.vecCons ((sphereFace n i).val u)
        (fun j => fderiv ℝ (sphereFace n i).val u (EuclideanSpace.single j 1))) := by
  rw [← sphereFace_flux_determinant]
  exact signed_sphereFace_flux_pos i hu

/-- Actual tangency identifies the square of the signed flux with the tangent
Gram determinant. This is independent of the area definition. -/
theorem sphereFace_gram {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    ((-1 : ℝ)^i.val * fluxDensity (sphereFace n i).val u)^2 =
      (Matrix.gram ℝ (fun j => fderiv ℝ (sphereFace n i).val u
        (EuclideanSpace.single j 1))).det := by
  rw [mul_pow]
  have hs : ((-1 : ℝ)^i.val)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [hs, one_mul, sphereFace_flux_determinant, coordinateVolume_sq]
  apply gram_cons_unit_normal _ _ (sphereFace_norm n i u)
  intro j
  exact sphere_tangent hu (simplex_uniqueDiffOn n u hu) ((sphereFace n i).differentiableAt hu)
    (fun z _ => sphereFace_norm n i z) _

/-- Every sphere chart has full tangent rank, including on its compact boundary. -/
theorem sphereFace_regular {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    LinearIndependent ℝ (fun j => fderiv ℝ (sphereFace n i).val u (EuclideanSpace.single j 1)) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [← sphereFace_gram i hu]
  exact pow_ne_zero _ (signed_sphereFace_flux_pos i hu).ne'

/-- The actual signed pullback density equals geometric Gram area density. -/
theorem signed_sphereFace_area {n : ℕ} (i : Fin (n+2)) {u : Space n}
    (hu : u ∈ standardSimplex n) :
    (-1 : ℝ)^i.val * fluxDensity (sphereFace n i).val u = areaDensity (sphereFace n i).val u := by
  unfold areaDensity
  rw [← sphereFace_gram i hu, Real.sqrt_sq (signed_sphereFace_flux_pos i hu).le]

/-- Finite geometric chart area. Coverage and disjoint interior images were
proved in `wholeSphere` and `sphereFace_interior_disjoint`. No flux defines it. -/
def wholeSphereArea (n : ℕ) : ℝ :=
  ∑ i : Fin (n+2), parametricArea (standardSimplex n) (sphereFace n i).val

theorem sphereFace_area_pos (n : ℕ) (i : Fin (n+2)) :
    0 < parametricArea (standardSimplex n) (sphereFace n i).val := by
  obtain ⟨U, hU, hKU, hS⟩ := (sphereFace n i).property
  exact parametricArea_pos (standardSimplex_isCompact n) hU hKU hS (simplex_volume_pos n)
    (fun _ hu => sphereFace_regular i hu)

theorem wholeSphereArea_pos (n : ℕ) : 0 < wholeSphereArea n := by
  apply Finset.sum_pos
  · intro i _
    exact sphereFace_area_pos n i
  · exact Finset.univ_nonempty

/-- The full sphere flux theorem, with the actual boundary signs, whole-sphere
coverage, face cancellation, and independently defined positive Gram area. -/
theorem wholeSphere_flux (n : ℕ) : integral (topRadial n) (sphereChain n) = wholeSphereArea n := by
  rw [sphereChain_faces]
  simp only [map_sum, map_zsmul, integral_simplex, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, wholeSphereArea]
  apply Finset.sum_congr rfl
  intro i _
  change (-1 : ℝ)^i.val * (∫ u in standardSimplex n, fluxDensity (sphereFace n i).val u) = _
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (standardSimplex_isCompact n).measurableSet
  intro u hu
  exact signed_sphereFace_area i hu

theorem wholeSphere_flux_pos (n : ℕ) : 0 < integral (topRadial n) (sphereChain n) := by
  rw [wholeSphere_flux]
  exact wholeSphereArea_pos n

/-- Positive-degree exactness contradicts the actual all-degree Stokes theorem
on the outward-oriented whole-sphere chain. Ambient dimension is `n+2`. -/
theorem topRadial_not_exact (n : ℕ) :
    ¬ ExactOn (n+1) (topRadial (n+1)) {x : Space (n+2) | x ≠ 0} := by
  rintro ⟨η, hη, he⟩
  have heq : integral (extDeriv η) (sphereChain (n+1)) =
      integral (topRadial (n+1)) (sphereChain (n+1)) := by
    rw [sphereChain_faces]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [integral_simplex, integral_simplex]
    apply setIntegral_congr_fun (standardSimplex_isCompact (n+1)).measurableSet
    intro u _hu
    change extDeriv η ((sphereFace (n+1) i).val u) _ = _
    rw [he _ (sphereFace_ne_zero (n+1) i u)]
    rfl
  have hz := sphere_exact_integral_zero η hη
  have hp := wholeSphere_flux_pos (n+1)
  rw [← heq, hz] at hp
  exact (lt_irrefl 0) hp

/-- The top-index source form is literally the radial form in its own coordinates. -/
theorem omega_top (n : ℕ) : omega n (Nat.le_refl (n+1)) = topRadial n := by
  have h : firstCoordinates (Nat.le_refl (n+1)) = ContinuousLinearMap.id ℝ (Space (n+1)) := by
    ext x i
    rfl
  ext x v
  simp [omega, h]

/-- Source part (c) in every dimension at least two, with genuine closedness
and nonexactness on the source punctured-space domain. -/
theorem dimension_ge_two_closed_not_exact (n : ℕ) :
    (∀ x : Space (n+2), x ≠ 0 → extDeriv (omega (n+1) (Nat.le_refl (n+2))) x = 0) ∧
    ¬ ExactOn (n+1) (omega (n+1) (Nat.le_refl (n+2))) {x : Space (n+2) | x ≠ 0} := by
  rw [omega_top (n+1)]
  exact ⟨fun _ hx => topRadial_closed hx, topRadial_not_exact n⟩

/-- The zero-dimensional geometric density is one at each of the two points. -/
theorem sphere_zero_face_area (i : Fin 2) :
    parametricArea (standardSimplex 0) (sphereFace 0 i).val = 1 := by
  have hs : standardSimplex 0 = (univ : Set (Space 0)) := by
    ext u
    simp [standardSimplex]
  simp [parametricArea, areaDensity, hs, volume_euclideanSpace_eq_dirac]

/-- The separate `S⁰` convention is counting area two and signed endpoint flux
two. This does not introduce a negative-degree primitive. -/
theorem sphere_zero_area_and_flux :
    wholeSphereArea 0 = 2 ∧ integral (topRadial 0) (sphereChain 0) = 2 := by
  have h : wholeSphereArea 0 = 2 := by simp [wholeSphereArea, sphere_zero_face_area]
  exact ⟨h, (wholeSphere_flux 0).trans h⟩

/-- Ordinary degree-zero boundary remains zero, without augmentation. -/
theorem sphere_zero_ordinaryBoundary : ordinaryBoundary 0 (sphereChain 0) = 0 := rfl

/-- The full chart chain remains closed in the existing orientation quotient. -/
theorem orientedSphere_closed (n : ℕ) :
    orientedBoundary n (project (n+1) (sphereChain (n+1))) = 0 := by
  change project n (boundary n (sphereChain (n+1))) = 0
  rw [sphereChain_closed, map_zero]

/-- Geometric flux also holds for the orientation-quotient integration API. -/
theorem orientedSphere_flux (n : ℕ) :
    orientedIntegral (topRadial n) (project n (sphereChain n)) = wholeSphereArea n :=
  wholeSphere_flux n

/-- The sphere class is nonzero, as witnessed by its proved positive integral. -/
theorem orientedSphere_ne_zero (n : ℕ) : project n (sphereChain n) ≠ 0 := by
  intro hz
  have h := orientedSphere_flux n
  rw [hz, map_zero] at h
  exact (wholeSphereArea_pos n).ne' h.symm

end Rudin.Chapter10.Exercise23.Sphere
end
