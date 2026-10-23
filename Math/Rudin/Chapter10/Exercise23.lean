module

public import Math.Rudin.Support.SimplexStokes
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exercise 10.23: radial forms

Draft. The form indexed by `m` below is the source's `omega_(m+1)`.
All statements about a singular form require its radial domain.
The Euclidean norm, not the coordinate supremum norm, is used throughout.
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
