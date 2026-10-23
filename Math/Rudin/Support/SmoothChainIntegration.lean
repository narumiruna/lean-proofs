module

public import Math.Rudin.Support.SimplexStokes
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integration on permutation-oriented smooth chains

Sources: Rudin 10.26–10.33. The quotient is the existing full-map permutation
quotient of `SmoothChains`; no additional relations are imposed.
-/

@[expose] public section
noncomputable section
namespace Rudin.Support.SmoothChainIntegration
open Set MeasureTheory SimplexIntegration SmoothChains

/-- The linear tangent of a barycentric vertex map. -/
def relabelLinear {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) : Param n →L[ℝ] Param m :=
  ∑ i : Fin n, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
    (vertex (f i.succ) - vertex (f 0))

@[simp] theorem vertex_zero (n : ℕ) : vertex (0 : Fin (n+1)) = 0 := by
  ext j
  have h := weights_vertex (0 : Fin (n+1)) j.succ
  simpa [weights, Ne.symm (Fin.succ_ne_zero j)] using h

@[simp] theorem vertex_succ {n : ℕ} (i : Fin n) :
    vertex i.succ = EuclideanSpace.single i 1 := by
  ext j
  have h := weights_vertex i.succ j.succ
  simpa [weights, Pi.single_apply, eq_comm] using h

@[simp] theorem affine_vertices (n : ℕ) : affine (vertex (n := n)) = identitySimplex n := by
  apply Subtype.ext
  funext u
  rw [affine_formula]
  simp only [vertex_zero, vertex_succ, sub_zero, zero_add]
  ext j
  simp [Pi.single_apply, identitySimplex]

theorem relabel_eq_affine {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (u : Param n) :
    relabel f u = vertex (f 0) + relabelLinear f u := by
  have h := congrArg (fun S : Simplex n (Param m) => S.val u)
    (affine_reparam (vertex (n := m)) f)
  rw [affine_vertices] at h
  change relabel f u = (affine (vertex ∘ f)).val u at h
  rw [h, affine_formula]
  simp [relabelLinear]

theorem relabel_hasFDerivAt {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (u : Param n) :
    HasFDerivAt (relabel f) (relabelLinear f) u := by
  simp_rw [funext (relabel_eq_affine f)]
  exact (relabelLinear f).hasFDerivAt.const_add _

@[simp] theorem fderiv_relabel {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (u : Param n) :
    fderiv ℝ (relabel f) u = relabelLinear f := (relabel_hasFDerivAt f u).fderiv

/-- A vertex permutation is a homeomorphism of the full parameter space. -/
def relabelHomeomorph {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) : Param n ≃ₜ Param n where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv u := by
    rw [relabel_comp]
    rw [σ.symm_comp_self]
    exact relabel_id u
  right_inv u := by
    rw [relabel_comp]
    rw [σ.self_comp_symm]
    exact relabel_id u
  continuous_toFun := (relabel_smooth σ).continuous
  continuous_invFun := (relabel_smooth σ.symm).continuous

@[simp] theorem relabel_preimage_simplex {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    relabel σ ⁻¹' standardSimplex n = standardSimplex n := by
  ext u
  constructor
  · intro h
    have := relabel_mem σ.symm h
    exact ((relabelHomeomorph σ).symm_apply_apply u) ▸ this
  · exact relabel_mem σ

/-- Top-degree alternating evaluation transforms by the actual determinant. -/
theorem alternating_linear {n : ℕ} (A : Param n [⋀^Fin n]→L[ℝ] ℝ)
    (L : Param n →L[ℝ] Param n) :
    A (fun i => L (EuclideanSpace.single i 1)) =
      LinearMap.det L.toLinearMap * A (fun i => EuclideanSpace.single i 1) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b := by
    funext i
    exact (EuclideanSpace.basisFun_apply (Fin n) ℝ i).symm
  change A.toAlternatingMap (L.toLinearMap ∘ (fun i => EuclideanSpace.single i 1)) = _
  rw [hb]
  rw [AlternatingMap.eq_smul_basis_det b A.toAlternatingMap]
  simp only [smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one]
  exact mul_comm _ _

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The determinant sign of affine vertex differences follows from an
alternating form in one additional coordinate. -/
theorem alternating_vertex_permutation {n : ℕ} (A : E [⋀^Fin n]→L[ℝ] ℝ)
    (v : Fin (n+1) → E) (σ : Equiv.Perm (Fin (n+1))) :
    A (fun j => v (σ j.succ) - v (σ 0)) =
      (σ.sign : ℤ) • A (fun j => v j.succ - v 0) := by
  let l : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E
  let A' := A.compContinuousLinearMap (ContinuousLinearMap.snd ℝ ℝ E)
  let B := ContinuousAlternatingMap.alternatizeUncurryFin (l.smulRight A')
  let w : Fin (n+1) → ℝ × E := fun i => (1, v i)
  have hb (z : Fin (n+1) → E) :
      B (fun i => (1, z i)) = A (fun j => z j.succ - z 0) := by
    rw [← SimplexStokes.alternating_sub_first B (fun i => (1, z i))]
    simp [B, l, A', ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      Fin.sum_univ_succ, Function.comp_def]
  have hp := B.toAlternatingMap.map_perm w σ
  change B (w ∘ σ) = (σ.sign : ℤ) • B w at hp
  simpa only [w, Function.comp_def, hb] using hp

@[simp] theorem relabelLinear_single {n m : ℕ}
    (f : Fin (n+1) → Fin (m+1)) (i : Fin n) :
    relabelLinear f (EuclideanSpace.single i 1) = vertex (f i.succ) - vertex (f 0) := by
  simp [relabelLinear, eq_comm]

/-- The standard Cartesian volume form, with value one on the ordered basis. -/
def parameterVolume (n : ℕ) : Param n [⋀^Fin n]→L[ℝ] ℝ :=
  ({ toAlternatingMap := Matrix.detRowAlternating
     cont := continuous_id.matrix_det } : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ).compContinuousLinearMap
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

@[simp] theorem parameterVolume_basis (n : ℕ) :
    parameterVolume n (fun i => EuclideanSpace.single i 1) = 1 := by
  change Matrix.det (fun i j : Fin n => Pi.single i (1 : ℝ) j) = 1
  have h : (fun i j : Fin n => (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [h, Matrix.det_one]

/-- Every vertex permutation has its actual orientation sign as determinant.
This includes dimension zero and permutations that move the missing vertex. -/
theorem det_relabelLinear {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    LinearMap.det (relabelLinear σ).toLinearMap = ((σ.sign : ℤ) : ℝ) := by
  have h := alternating_vertex_permutation (parameterVolume n) vertex σ
  have hl := alternating_linear (parameterVolume n) (relabelLinear σ)
  simp only [relabelLinear_single, parameterVolume_basis, mul_one] at hl
  rw [← hl]
  simpa only [vertex_zero, vertex_succ, sub_zero, parameterVolume_basis,
    zsmul_eq_mul, mul_one] using h

/-- The actual tangent of a reparameterized simplex is the composed Fréchet
derivative. This also applies to the noninvertible maps that define faces. -/
theorem fderiv_reparam {n m : ℕ} (S : Simplex m E)
    (f : Fin (n+1) → Fin (m+1)) {u : Param n} (hu : u ∈ standardSimplex n) :
    fderiv ℝ (S.reparam f).val u =
      (fderiv ℝ S.val (relabel f u)).comp (relabelLinear f) := by
  change fderiv ℝ (S.val ∘ relabel f) u = _
  rw [fderiv_comp u (S.differentiableAt (relabel_mem f hu))
    (relabel_hasFDerivAt f u).differentiableAt, fderiv_relabel]

/-- The chain rule applies on the closed simplex using its stored C² neighborhood. -/
theorem coefficient_reparam_det {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (σ : Equiv.Perm (Fin (n+1))) {u : Param n} (hu : u ∈ standardSimplex n) :
    simplexCoefficient ω (S.reparam σ).toSmooth u =
      LinearMap.det (relabelLinear σ).toLinearMap *
        simplexCoefficient ω S.toSmooth (relabel σ u) := by
  simp only [simplexCoefficient, pullback_apply]
  change (ω ((S.reparam σ).val u))
    (fun i => fderiv ℝ (S.reparam σ).val u (EuclideanSpace.single i 1)) = _
  rw [fderiv_reparam S σ hu]
  exact alternating_linear
    ((ω (S.val (relabel σ u))).compContinuousLinearMap
      (fderiv ℝ S.val (relabel σ u))) (relabelLinear σ)

/-- An affine parameter permutation with unit absolute determinant preserves
full Lebesgue measure, not only continuous-coefficient integrals. -/
theorem relabel_volume_of_abs_det {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (hdet : |LinearMap.det (relabelLinear σ).toLinearMap| = 1) :
    MeasurePreserving (relabel σ) volume volume := by
  have hn : LinearMap.det (relabelLinear σ).toLinearMap ≠ 0 := by
    intro h
    simp [h] at hdet
  have hL : MeasurePreserving (relabelLinear σ) volume volume := by
    refine ⟨(relabelLinear σ).continuous.measurable, ?_⟩
    change Measure.map (relabelLinear σ).toLinearMap volume = volume
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn, abs_inv, hdet]
    simp
  have h := (measurePreserving_add_left (volume : Measure (Param n)) (vertex (σ 0))).comp hL
  convert h using 1
  funext u
  exact relabel_eq_affine σ u

/-- Full Lebesgue measure is preserved for every vertex permutation. -/
theorem relabel_volume {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) :
    MeasurePreserving (relabel σ) volume volume := by
  apply relabel_volume_of_abs_det
  rw [det_relabelLinear]
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]

/-- Change of variables for every totalized scalar function. No measurability,
integrability, or extension outside a neighborhood is assumed. -/
theorem integral_relabel {n : ℕ} (f : Param n → ℝ) (σ : Equiv.Perm (Fin (n+1))) :
    (∫ u in standardSimplex n, f (relabel σ u)) = ∫ u in standardSimplex n, f u := by
  have h := (relabel_volume σ).setIntegral_preimage_emb
    (relabelHomeomorph σ).measurableEmbedding f (standardSimplex n)
  rwa [relabel_preimage_simplex] at h

/-- The actual pullback coefficient transforms by the permutation sign. -/
theorem coefficient_reparam {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (σ : Equiv.Perm (Fin (n+1))) {u : Param n} (hu : u ∈ standardSimplex n) :
    simplexCoefficient ω (S.reparam σ).toSmooth u =
      (σ.sign : ℤ) • simplexCoefficient ω S.toSmooth (relabel σ u) := by
  rw [coefficient_reparam_det ω S σ hu, det_relabelLinear, zsmul_eq_mul]

/-- Integration changes by the sign of every vertex permutation, without
regularity assumptions on the form. The simplex still has its C² neighborhood. -/
theorem simplexIntegral_reparam {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (σ : Equiv.Perm (Fin (n+1))) :
    simplexIntegral ω (S.reparam σ).toSmooth = (σ.sign : ℤ) • simplexIntegral ω S.toSmooth := by
  unfold simplexIntegral
  rw [setIntegral_congr_fun (standardSimplex_isCompact n).measurableSet
    (fun u hu => coefficient_reparam ω S σ hu)]
  simp_rw [zsmul_eq_mul]
  rw [integral_const_mul, integral_relabel]

/-- All defining relations of the existing unsaturated quotient integrate to zero. -/
theorem integral_orientationRelations {n : ℕ} (ω : Form n E) :
    orientationRelations n E ≤ (SmoothChains.integral ω).ker := by
  apply (AddSubgroup.closure_le _).mpr
  rintro r ⟨S, σ, rfl⟩
  change SmoothChains.integral ω (simplex (S.reparam σ) - (σ.sign : ℤ) • simplex S) = 0
  simp [simplexIntegral_reparam]

/-- Genuine integration on the frozen permutation quotient. It is not a new
quotient and does not identify chains by their integral values. -/
def orientedIntegral {n : ℕ} (ω : Form n E) : Oriented n E →+ ℝ :=
  QuotientAddGroup.lift (orientationRelations n E) (SmoothChains.integral ω)
    (integral_orientationRelations ω)

@[simp] theorem orientedIntegral_project {n : ℕ} (ω : Form n E) (c : Chain n E) :
    orientedIntegral ω (project n c) = SmoothChains.integral ω c := rfl

@[simp] theorem orientedIntegral_simplex {n : ℕ} (ω : Form n E) (S : Simplex n E) :
    orientedIntegral ω (project n (simplex S)) = simplexIntegral ω S.toSmooth :=
  integral_simplex ω S

theorem orientedIntegral_reparam {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (σ : Equiv.Perm (Fin (n+1))) :
    orientedIntegral ω (project n (simplex (S.reparam σ))) =
      (σ.sign : ℤ) • orientedIntegral ω (project n (simplex S)) := by
  simp [simplexIntegral_reparam]

theorem orientedIntegral_multiplicity {n : ℕ} (ω : Form n E) (z : ℤ) (c : Oriented n E) :
    orientedIntegral ω (z • c) = z • orientedIntegral ω c := map_zsmul _ _ _

/-- Degree zero is signed evaluation; it is not an augmented boundary integral. -/
theorem orientedIntegral_zero (ω : Form 0 E) (S : Simplex 0 E) (z : ℤ) :
    orientedIntegral ω (z • project 0 (simplex S)) =
      z • ω (S.val 0) (fun i => Fin.elim0 i) := by
  rw [map_zsmul, orientedIntegral_project, SmoothChains.integral_zero]

/-- The quotient value has integrability and all coordinate-order source
Riemann witnesses when the form is continuous on the actual image. -/
theorem orientedIntegral_source {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (hω : ContinuousOn ω (S.val '' standardSimplex n)) :
    IntegrableOn (simplexCoefficient ω S.toSmooth) (standardSimplex n) ∧
    ∀ σ : Equiv.Perm (Fin n), MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω S.toSmooth ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (orientedIntegral ω (project n (simplex S))) :=
  ⟨integral_integrable ω S hω, fun σ => integral_source ω S hω σ⟩

/-- Local C¹ forms need no continuous extension outside the open form domain. -/
theorem orientedIntegral_source_on {n : ℕ} (ω : Form n E) (S : Simplex n E)
    {U : Set E} (hω : ContDiffOn ℝ 1 ω U)
    (hS : S.val '' standardSimplex n ⊆ U) :
    IntegrableOn (simplexCoefficient ω S.toSmooth) (standardSimplex n) ∧
    ∀ σ : Equiv.Perm (Fin n), MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω S.toSmooth ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (orientedIntegral ω (project n (simplex S))) :=
  orientedIntegral_source ω S (hω.continuousOn.mono hS)

/-- Naturality on the existing quotient follows from the actual chain rule. -/
theorem orientedIntegral_map {n : ℕ} (ω : Form n F) (f : E → F) (hf : ContDiff ℝ 2 f)
    (c : Oriented n E) :
    orientedIntegral ω (orientedMap n f hf c) = orientedIntegral (pullback ω f) c := by
  induction c using QuotientAddGroup.induction_on with
  | H c => exact integral_map ω f hf c

/-- Naturality also holds for C² target maps defined only near the image. -/
theorem orientedIntegral_mapOn {n : ℕ} (ω : Form n F) (S : Simplex n E)
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hS : MapsTo S.val (standardSimplex n) U) :
    orientedIntegral ω (project n (simplex (S.mapOn f U hU hf hS))) =
      orientedIntegral (pullback ω f) (project n (simplex S)) := by
  simp only [orientedIntegral_simplex, simplexIntegral]
  apply setIntegral_congr_fun (standardSimplex_isCompact n).measurableSet
  intro u hu
  exact congrArg (fun a => a (fun i => EuclideanSpace.single i 1))
    (pullback_comp ω f S.val u
      ((hf _ (hS hu)).contDiffAt (hU.mem_nhds (hS hu)) |>.differentiableAt (by norm_num))
      (S.differentiableAt hu))

/-- The local postcomposition comparison extends to integer chains. -/
theorem orientedIntegral_mapOnChain {n : ℕ} (ω : Form n F) (f : E → F)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (c : DomainChain n U) :
    orientedIntegral ω (project n (mapOnChain n f U hU hf c)) =
      orientedIntegral (pullback ω f) (project n (forgetDomain n U c)) := by
  have h : (SmoothChains.integral ω).comp (mapOnChain n f U hU hf) =
      (SmoothChains.integral (pullback ω f)).comp (forgetDomain n U) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    exact orientedIntegral_mapOn ω S.val f U hU hf S.property
  exact DFunLike.congr_fun h c

/-- Stokes for a chain in an open form domain, after projection to the existing
orientation quotient. Integer coefficients are unrestricted. -/
theorem orientedIntegral_domain_stokes {n : ℕ} (ω : Form n E) {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (c : DomainChain (n+1) U) :
    orientedIntegral (extDeriv ω) (project (n+1) (forgetDomain (n+1) U c)) =
      orientedIntegral ω (orientedBoundary n (project (n+1) (forgetDomain (n+1) U c))) :=
  SimplexStokes.domainChain_stokes ω hU hω c

/-- Stokes for any quotient class with a representative whose generators lie
in the open form domain. This is a support hypothesis, not a transformation law. -/
theorem orientedIntegral_stokes {n : ℕ} (ω : Form n E) {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (c : Oriented (n+1) E)
    (hc : ∃ d : DomainChain (n+1) U, project (n+1) (forgetDomain (n+1) U d) = c) :
    orientedIntegral (extDeriv ω) c = orientedIntegral ω (orientedBoundary n c) := by
  obtain ⟨d, rfl⟩ := hc
  exact orientedIntegral_domain_stokes ω hU hω d

/-- Generator Stokes, with source witnesses for the exterior integral and all
actual frozen faces. The exterior source value is the quotient boundary value. -/
theorem orientedIntegral_stokes_source {n : ℕ} (ω : Form n E) (S : Simplex (n+1) E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (hS : S.val '' standardSimplex (n+1) ⊆ U) :
    IntegrableOn (simplexCoefficient (extDeriv ω) S.toSmooth) (standardSimplex (n+1)) ∧
    (∀ σ : Equiv.Perm (Fin (n+1)), MultivariateRiemann.HasSourceIntegral (n+1) 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient (extDeriv ω) S.toSmooth ∘
        (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (orientedIntegral ω (orientedBoundary n (project (n+1) (simplex S))))) ∧
    ∀ i : Fin (n+2),
      IntegrableOn (simplexCoefficient ω (S.face i).toSmooth) (standardSimplex n) ∧
      ∀ σ : Equiv.Perm (Fin n), MultivariateRiemann.HasSourceIntegral n 0 1
        (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω (S.face i).toSmooth ∘
          (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
        (orientedIntegral ω (project n (simplex (S.face i)))) := by
  have he := SimplexStokes.exterior_integral_source ω S.toSmooth hU hω hS
  refine ⟨(he (Equiv.refl _)).1, ?_, ?_⟩
  · intro σ
    have hst := SimplexStokes.smoothChains_stokes ω S hU hω hS
    change MultivariateRiemann.HasSourceIntegral _ _ _ _
      (SmoothChains.integral ω (boundary n (simplex S)))
    rw [← hst, integral_simplex]
    exact (he σ).2
  · intro i
    apply orientedIntegral_source_on ω (S.face i) hω
    rintro y ⟨u, hu, rfl⟩
    exact hS ⟨relabel i.succAbove u, relabel_mem i.succAbove hu, rfl⟩

/-- Local exact-form integrals depend only on the quotient boundary. -/
theorem orientedIntegral_exact_eq {n : ℕ} (ω : Form n E) {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) (c d : DomainChain (n+1) U)
    (hboundary : orientedBoundary n (project (n+1) (forgetDomain (n+1) U c)) =
      orientedBoundary n (project (n+1) (forgetDomain (n+1) U d))) :
    orientedIntegral (extDeriv ω) (project (n+1) (forgetDomain (n+1) U c)) =
      orientedIntegral (extDeriv ω) (project (n+1) (forgetDomain (n+1) U d)) := by
  rw [orientedIntegral_domain_stokes ω hU hω, orientedIntegral_domain_stokes ω hU hω,
    hboundary]

/-- This functional extends the frozen degree-one path-integral comparison. -/
theorem orientedIntegral_eq_pathIntegral (ω : Form 1 E) (hω : Continuous ω)
    (c : Oriented 1 E) :
    orientedIntegral ω c = orientedPathIntegral (PathIntegration.fromAlternating ω) c := by
  induction c using QuotientAddGroup.induction_on with
  | H c => exact (orientedPathIntegral_project ω hω c).symm

/-- Affine vertex permutation compatibility concerns the genuine functional,
not an isomorphism with the stronger repeated-vertex quotient. -/
theorem affine_integral_permutation {n : ℕ} (ω : Form n E) (v : Fin (n+1) → E)
    (σ : Equiv.Perm (Fin (n+1))) :
    orientedIntegral ω (project n (simplex (affine (v ∘ σ)))) =
      (σ.sign : ℤ) • orientedIntegral ω (project n (simplex (affine v))) := by
  rw [← affine_reparam]
  exact orientedIntegral_reparam ω (affine v) σ

/-- Repeated affine vertices give zero integrals. This does not assert that
the corresponding class is zero in the unsaturated permutation quotient. -/
theorem affine_integral_repeated {n : ℕ} (ω : Form n E) (v : Fin (n+1) → E)
    (i j : Fin (n+1)) (hij : i ≠ j) (hv : v i = v j) :
    orientedIntegral ω (project n (simplex (affine v))) = 0 := by
  classical
  have he : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hv]
    by_cases hkj : k = j
    · subst k; simp [hv]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := affine_integral_permutation ω v (Equiv.swap i j)
  rw [he, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h
  linarith

/-- Constants are allowed generators. Their positive-degree integrals vanish. -/
theorem affine_integral_constant (n : ℕ) (ω : Form (n+1) E) (p : E) :
    orientedIntegral ω (project (n+1) (simplex (affine (fun _ => p)))) = 0 :=
  affine_integral_repeated ω (fun _ => p) 0 (Fin.succ 0)
    (Ne.symm (Fin.succ_ne_zero 0)) rfl

/-- The genuine integral detects the positively oriented identity generator
in every degree, including zero. Its value is the normalized simplex volume. -/
theorem orientedIntegral_identity (n : ℕ) :
    orientedIntegral (fun _ => parameterVolume n)
      (project n (simplex (identitySimplex n))) = 1 / (n.factorial : ℝ) := by
  rw [orientedIntegral_simplex]
  have hc (u : Param n) :
      simplexCoefficient (fun _ => parameterVolume n) (identitySimplex n).toSmooth u = 1 := by
    simp [simplexCoefficient, pullback_apply, identitySimplex, Simplex.toSmooth]
  simp_rw [simplexIntegral, hc]
  simpa using MultivariateRiemann.standardSimplex_volume n

/-- Integration itself proves infinite order of the identity class. -/
theorem integral_detects_identity_multiplicity (n : ℕ) :
    Function.Injective (fun z : ℤ => z • project n (simplex (identitySimplex n))) := by
  intro z w h
  have hh := congrArg (orientedIntegral (fun _ => parameterVolume n)) h
  simp only [map_zsmul, orientedIntegral_identity, zsmul_eq_mul] at hh
  have hn : (1 : ℝ) / (n.factorial : ℝ) ≠ 0 := by positivity
  exact Int.cast_injective (mul_right_cancel₀ hn hh)

namespace Tests

/-- The full nonlinear map `(x,y) ↦ (x,y²)`, not its affine vertex interpolation. -/
def nonlinearSimplex : Simplex 2 (ℝ × ℝ) :=
  Simplex.ofSmooth (SimplexStokes.pairSimplex verticalSquare verticalSquare_smooth)

def nonlinearForm : Form 1 (ℝ × ℝ) :=
  TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1)

/-- A nonconstant exterior coefficient has nonzero quotient integral. -/
theorem nonlinear_integral :
    orientedIntegral (extDeriv nonlinearForm) (project 2 (simplex nonlinearSimplex)) = 2 / 3 := by
  rw [orientedIntegral_simplex]
  exact SimplexStokes.nonlinear_both_stokes.1

/-- Swapping the missing vertex with a Cartesian vertex reverses a nonlinear integral. -/
theorem nonlinear_reflection :
    orientedIntegral (extDeriv nonlinearForm)
      (project 2 (simplex (nonlinearSimplex.reparam (Equiv.swap 0 1)))) = -(2 / 3) := by
  rw [orientedIntegral_reparam, nonlinear_integral, Equiv.Perm.sign_swap (by decide)]
  norm_num

/-- A Cartesian coordinate swap also reverses that integral. -/
theorem nonlinear_coordinate_swap :
    orientedIntegral (extDeriv nonlinearForm)
      (project 2 (simplex (nonlinearSimplex.reparam (Equiv.swap 1 2)))) = -(2 / 3) := by
  rw [orientedIntegral_reparam, nonlinear_integral, Equiv.Perm.sign_swap (by decide)]
  norm_num

/-- Negative integer multiplicity is retained on the quotient. -/
theorem nonlinear_negative_multiplicity :
    orientedIntegral (extDeriv nonlinearForm)
      ((-3 : ℤ) • project 2 (simplex nonlinearSimplex)) = -2 := by
  rw [map_zsmul, nonlinear_integral]
  norm_num

/-- The computed nonlinear class is nonzero in the actual permutation quotient. -/
theorem nonlinear_class_ne_zero : project 2 (simplex nonlinearSimplex) ≠ 0 := by
  intro h
  have hi := nonlinear_integral
  rw [h, map_zero] at hi
  norm_num at hi

/-- A repeated-vertex triangle has zero integrals, without a class-zero assertion. -/
theorem repeated_triangle (ω : Form 2 E) (a b : E) :
    orientedIntegral ω (project 2 (simplex (affine ![a,b,a]))) = 0 :=
  affine_integral_repeated ω ![a,b,a] 0 2 (by decide) rfl

/-- The degree-zero normalization has value one rather than an empty-face value. -/
theorem degree_zero :
    orientedIntegral (fun _ => parameterVolume 0)
      (project 0 (simplex (identitySimplex 0))) = 1 := by
  simpa using orientedIntegral_identity 0

end Tests
/-- The genuine integral does not depend on how a map is extended outside its closed simplex.
This is an equality of integral values, not an extra relation in the chain quotient. -/
theorem integral_eqOn {n : ℕ} (ω : Form n E) (S T : Simplex n E)
    (hST : EqOn S.val T.val (standardSimplex n)) :
    SmoothChains.integral ω (simplex S) = SmoothChains.integral ω (simplex T) := by
  rw [integral_simplex, integral_simplex]
  apply integral_congr_ae
  have hc : Convex ℝ (standardSimplex n) :=
    (MultivariateRiemann.piSimplex_convex n).linear_preimage
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap
  have hn : ∀ᵐ u : Param n ∂volume, u ∉ frontier (standardSimplex n) := by
    rw [ae_iff]
    simpa using hc.addHaar_frontier volume
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (standardSimplex_isCompact n).measurableSet] with u hfront hu
  have hi : u ∈ interior (standardSimplex n) := by
    by_contra h
    exact hfront ⟨subset_closure hu, h⟩
  have he : S.val =ᶠ[nhds u] T.val :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hi)
      (fun v hv ↦ hST (interior_subset hv))
  have hd := he.fderiv_eq (𝕜 := ℝ)
  simp only [simplexCoefficient, pullback_apply, Simplex.toSmooth]
  rw [hST hu, hd]

/-- Both closed-source representatives have the same literal Riemann value in every order. -/
theorem source_eqOn {n : ℕ} (ω : Form n E) (S T : Simplex n E)
    (hST : EqOn S.val T.val (standardSimplex n))
    (hω : ContinuousOn ω (S.val '' standardSimplex n)) (σ : Equiv.Perm (Fin n)) :
    MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω T.toSmooth ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (orientedIntegral ω (project n (simplex S))) := by
  have him : S.val '' standardSimplex n = T.val '' standardSimplex n := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hST hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hST hx⟩
  have ht := SmoothChains.integral_source ω T (him ▸ hω) σ
  rw [← integral_eqOn ω S T hST] at ht
  simpa only [orientedIntegral_project] using ht

/-- Boundary integral values also depend only on the closed source restriction. -/
theorem boundaryIntegral_eqOn {n : ℕ} (ω : Form n E) (S T : Simplex (n+1) E)
    (hST : EqOn S.val T.val (standardSimplex (n+1))) :
    orientedIntegral ω (orientedBoundary n (project (n+1) (simplex S))) =
      orientedIntegral ω (orientedBoundary n (project (n+1) (simplex T))) := by
  simp only [orientedBoundary_project, orientedIntegral_project, boundary_simplex,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_eqOn
  intro u hu
  exact hST (relabel_mem i.succAbove hu)

end Rudin.Support.SmoothChainIntegration
