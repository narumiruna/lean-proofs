module

public import Math.Rudin.Support.SmoothChainIntegration

/-! # Exercise 10.20: integration by parts for actual differential forms

The scalar and form are C¹ on an open set containing the full chain images.
The parameter maps are C² on neighborhoods of their closed simplexes. The
boundary is the actual signed restriction boundary, with integer multiplicity.
-/

@[expose] public section
noncomputable section

namespace Rudin.Chapter10.Exercise20

open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support.SimplexStokes
open Rudin.Support

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exterior product of the genuine differential `df` with an n-form.
The alternation has the usual n+1 signed terms, without a factorial factor. -/
def differentialWedge {n : ℕ} (f : E → ℝ) (ω : Form n E) : Form (n+1) E :=
  fun x ↦ ContinuousAlternatingMap.alternatizeUncurryFin
    ((fderiv ℝ f x).smulRight (ω x))

theorem differentialWedge_apply {n : ℕ} (f : E → ℝ) (ω : Form n E)
    (x : E) (v : Fin (n+1) → E) :
    differentialWedge f ω x v = ∑ i : Fin (n+1),
      (-1 : ℝ)^i.val * (fderiv ℝ f x (v i) * ω x (fun j ↦ v (i.succAbove j))) := by
  simp only [differentialWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

/-- Product rule for the actual exterior derivative. -/
theorem exterior_product {n : ℕ} {f : E → ℝ} {ω : Form n E} {x : E}
    (hf : DifferentiableAt ℝ f x) (hω : DifferentiableAt ℝ ω x) :
    extDeriv (fun y ↦ f y • ω y) x =
      f x • extDeriv ω x + differentialWedge f ω x := by
  simp only [extDeriv, fderiv_fun_smul hf hω,
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul, differentialWedge]

theorem continuous_terms {n : ℕ} {f : E → ℝ} {ω : Form n E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hω : ContDiffOn ℝ 1 ω U) :
    ContinuousOn (fun x ↦ f x • extDeriv ω x) U ∧
    ContinuousOn (differentialWedge f ω) U ∧ ContinuousOn (fun x ↦ f x • ω x) U := by
  have hc := hf.continuousOn.smul (extDeriv_continuousOn hU hω)
  refine ⟨hc, ?_, hf.continuousOn.smul hω.continuousOn⟩
  apply ((extDeriv_continuousOn hU (hf.smul hω)).sub hc).congr
  intro x hx
  change differentialWedge f ω x = extDeriv (fun y ↦ f y • ω y) x - f x • extDeriv ω x
  rw [exterior_product
    (((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
    (((hω x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))]
  abel

/-- Integrability and the literal repeated Riemann witnesses, in every order. -/
def SourceDefined {n : ℕ} (η : Form n E) (S : SmoothChains.Simplex n E) : Prop :=
  IntegrableOn (simplexCoefficient η S.toSmooth) (standardSimplex n) ∧
    ∀ σ : Equiv.Perm (Fin n), MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient η S.toSmooth ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (SmoothChains.integral η (SmoothChains.simplex S))

theorem sourceDefined_of_continuous {n : ℕ} {η : Form n E} {S : SmoothChains.Simplex n E}
    (hη : ContinuousOn η (S.val '' standardSimplex n)) : SourceDefined η S :=
  ⟨SmoothChains.integral_integrable η S hη, SmoothChains.integral_source η S hη⟩

/-- These explicit hypotheses certify every term, including every boundary face. -/
theorem validity_conditions {n : ℕ} {f : E → ℝ} {ω : Form n E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hω : ContDiffOn ℝ 1 ω U)
    (S : SmoothChains.InDomain (n+1) U) :
    SourceDefined (fun x ↦ f x • extDeriv ω x) S.val ∧
    SourceDefined (differentialWedge f ω) S.val ∧
    ∀ i : Fin (n+2), SourceDefined (fun x ↦ f x • ω x) (S.val.face i) := by
  have hs : S.val.val '' standardSimplex (n+1) ⊆ U := by
    rintro y ⟨x, hx, rfl⟩; exact S.property hx
  obtain ⟨hfd, hdw, hfw⟩ := continuous_terms hU hf hω
  refine ⟨sourceDefined_of_continuous (hfd.mono hs),
    sourceDefined_of_continuous (hdw.mono hs), fun i ↦ ?_⟩
  apply sourceDefined_of_continuous (hfw.mono ?_)
  rintro y ⟨x, hx, rfl⟩
  exact (S.face i).property hx

private theorem integral_add_domain {n : ℕ} {η θ : Form n E} {U : Set E}
    (hη : ContinuousOn η U) (hθ : ContinuousOn θ U) (c : SmoothChains.DomainChain n U) :
    SmoothChains.integral (fun x ↦ η x + θ x) (SmoothChains.forgetDomain n U c) =
      SmoothChains.integral η (SmoothChains.forgetDomain n U c) + SmoothChains.integral θ (SmoothChains.forgetDomain n U c) := by
  have h : (SmoothChains.integral (fun x ↦ η x + θ x)).comp (SmoothChains.forgetDomain n U) =
      (SmoothChains.integral η).comp (SmoothChains.forgetDomain n U) +
        (SmoothChains.integral θ).comp (SmoothChains.forgetDomain n U) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply,
      SmoothChains.forgetDomain, FreeAbelianGroup.map_of_apply,
      SmoothChains.integral, FreeAbelianGroup.lift_apply_of]
    change simplexIntegral (fun x ↦ η x + θ x) S.val.toSmooth =
      simplexIntegral η S.val.toSmooth + simplexIntegral θ S.val.toSmooth
    have hs : S.val.val '' standardSimplex n ⊆ U := by
      rintro y ⟨x, hx, rfl⟩; exact S.property hx
    change (∫ u in standardSimplex n, simplexCoefficient η S.val.toSmooth u +
      simplexCoefficient θ S.val.toSmooth u) = _
    exact integral_add (simplexCoefficient_integrable η _ (hη.mono hs))
      (simplexCoefficient_integrable θ _ (hθ.mono hs))
  exact DFunLike.congr_fun h c

private theorem integral_congr_domain {n : ℕ} {η θ : Form n E} {U : Set E}
    (he : EqOn η θ U) (c : SmoothChains.DomainChain n U) :
    SmoothChains.integral η (SmoothChains.forgetDomain n U c) = SmoothChains.integral θ (SmoothChains.forgetDomain n U c) := by
  have h : (SmoothChains.integral η).comp (SmoothChains.forgetDomain n U) =
      (SmoothChains.integral θ).comp (SmoothChains.forgetDomain n U) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp only [AddMonoidHom.comp_apply, SmoothChains.forgetDomain,
      FreeAbelianGroup.map_of_apply, SmoothChains.integral, FreeAbelianGroup.lift_apply_of]
    apply setIntegral_congr_fun (standardSimplex_isCompact n).measurableSet
    intro u hu
    simp only [simplexCoefficient, pullback_apply]
    simpa only [SmoothChains.Simplex.toSmooth] using
      congrArg (fun A : E [⋀^Fin n]→L[ℝ] ℝ ↦
        A (fun i ↦ fderiv ℝ S.val.val u (EuclideanSpace.single i 1))) (he (S.property hu))
  exact DFunLike.congr_fun h c

/-- The source formula for arbitrary finite integer chains, including zero chains. -/
theorem form_identity {n : ℕ} {f : E → ℝ} {ω : Form n E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hω : ContDiffOn ℝ 1 ω U)
    (c : SmoothChains.DomainChain (n+1) U) :
    SmoothChains.integral (fun x ↦ f x • extDeriv ω x) (SmoothChains.forgetDomain (n+1) U c) =
      SmoothChains.integral (fun x ↦ f x • ω x)
        (SmoothChains.boundary n (SmoothChains.forgetDomain (n+1) U c)) -
      SmoothChains.integral (differentialWedge f ω) (SmoothChains.forgetDomain (n+1) U c) := by
  have he : EqOn (extDeriv (fun x ↦ f x • ω x))
      (fun x ↦ f x • extDeriv ω x + differentialWedge f ω x) U := by
    intro x hx
    exact exterior_product
      (((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
      (((hω x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
  have hi := integral_congr_domain he c
  obtain ⟨hfd, hdw, _⟩ := continuous_terms hU hf hω
  rw [integral_add_domain hfd hdw] at hi
  have hs := domainChain_stokes (fun x ↦ f x • ω x) hU (hf.smul hω) c
  linarith

/-- In degree zero the exterior product is the usual scalar `g df`. -/
theorem differentialWedge_zero (f g : ℝ → ℝ) (x v : ℝ) :
    differentialWedge f (Rudin.Support.PathIntegration.zeroForm g) x (fun _ ↦ v) =
      fderiv ℝ f x v * g x := by
  simp [differentialWedge_apply, Rudin.Support.PathIntegration.zeroForm]

/-- On an affine real segment the simplex integral is the oriented interval integral. -/
theorem segment_integral (η : Form 1 ℝ) (a b : ℝ)
    (hη : ContinuousOn η ((SmoothChains.affine ![a,b]).val '' standardSimplex 1)) :
    SmoothChains.integral η (SmoothChains.simplex (SmoothChains.affine ![a,b])) =
      ∫ x in a..b, η x (fun _ ↦ 1) := by
  rw [SmoothChains.integral_eq_pathIntegral η _ hη, SmoothChains.affine_path]
  unfold PathIntegration.pathIntegral PathIntegration.coefficient
  simp only [PathIntegration.fromAlternating_apply,
    fun t ↦ (PathIntegration.segment_hasDerivAt a b t).deriv]
  have he : (fun t ↦ η (OrientedChains.Parametric.segment a b t) (fun _ ↦ b-a)) =
      fun t ↦ (b-a) * η ((b-a)*t+a) (fun _ ↦ 1) := by
    funext t
    have hp : OrientedChains.Parametric.segment a b t = (b-a)*t+a := by
      simp only [OrientedChains.Parametric.segment, smul_eq_mul]
      ring
    rw [hp]
    simpa only [smul_eq_mul, mul_one, Fin.prod_univ_one,
      ContinuousAlternatingMap.coe_toAlternatingMap] using
      (η ((b-a)*t+a)).toAlternatingMap.map_smul_univ
        (fun _ : Fin 1 ↦ b-a) (fun _ ↦ 1)
  rw [he, intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using
    intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := 1) (fun x ↦ η x (fun _ ↦ 1)) (b-a) a

private theorem zeroForm_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (PathIntegration.zeroForm g) := by
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℝ ℝ (Fin 0)).contDiff.comp hg

/-- The actual zero-dimensional signed boundary evaluates at the two endpoints. -/
theorem segment_boundary (f g : ℝ → ℝ) (a b : ℝ) :
    SmoothChains.integral (fun x ↦ f x • PathIntegration.zeroForm g x)
      (SmoothChains.boundary 0 (SmoothChains.simplex (SmoothChains.affine ![a,b]))) =
      f b * g b - f a * g a := by
  rw [SmoothChains.boundary_simplex]
  simp only [map_sum, map_zsmul, SmoothChains.affine_face,
    SmoothChains.integral_zero, SmoothChains.affine_formula]
  simp [PathIntegration.zeroForm, sub_eq_add_neg]

/-- The formula also holds on the proved oriented quotient, for any admissible representative. -/
theorem oriented_form_identity {n : ℕ} {f : E → ℝ} {ω : Form n E} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hω : ContDiffOn ℝ 1 ω U)
    (c : SmoothChains.Oriented (n+1) E)
    (hc : ∃ d : SmoothChains.DomainChain (n+1) U,
      SmoothChains.project (n+1) (SmoothChains.forgetDomain (n+1) U d) = c) :
    SmoothChainIntegration.orientedIntegral (fun x ↦ f x • extDeriv ω x) c =
      SmoothChainIntegration.orientedIntegral (fun x ↦ f x • ω x)
        (SmoothChains.orientedBoundary n c) -
      SmoothChainIntegration.orientedIntegral (differentialWedge f ω) c := by
  rcases hc with ⟨d, rfl⟩
  simpa only [SmoothChains.orientedBoundary_project,
    SmoothChainIntegration.orientedIntegral_project] using form_identity hU hf hω d

/-- Degree zero of `form_identity` gives ordinary integration by parts on any real segment. -/
theorem one_variable_identity {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (a b : ℝ) :
    (∫ x in a..b, f x * deriv g x) =
      f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  let S : SmoothChains.InDomain 1 (Set.univ : Set ℝ) :=
    ⟨SmoothChains.affine ![a,b], fun _ _ ↦ Set.mem_univ _⟩
  have h := form_identity isOpen_univ hf.contDiffOn (zeroForm_contDiff hg).contDiffOn
    (FreeAbelianGroup.of S)
  simp only [SmoothChains.forgetDomain, FreeAbelianGroup.map_of_apply] at h
  change SmoothChains.integral (fun x ↦ f x • extDeriv (PathIntegration.zeroForm g) x)
      (SmoothChains.simplex (SmoothChains.affine ![a,b])) =
    SmoothChains.integral (fun x ↦ f x • PathIntegration.zeroForm g x)
      (SmoothChains.boundary 0 (SmoothChains.simplex (SmoothChains.affine ![a,b]))) -
    SmoothChains.integral (differentialWedge f (PathIntegration.zeroForm g))
      (SmoothChains.simplex (SmoothChains.affine ![a,b])) at h
  obtain ⟨hfd, hdw, _⟩ := continuous_terms isOpen_univ hf.contDiffOn
    (zeroForm_contDiff hg).contDiffOn
  rw [segment_integral _ a b (hfd.mono (subset_univ _)), segment_boundary,
    segment_integral _ a b (hdw.mono (subset_univ _))] at h
  have hA (x : ℝ) : (f x • extDeriv (PathIntegration.zeroForm g) x) (fun _ ↦ 1) =
      f x * deriv g x := by
    change f x * PathIntegration.fromAlternating (extDeriv (PathIntegration.zeroForm g)) x 1 = _
    rw [PathIntegration.exterior_potential, fderiv_apply_one_eq_deriv]
  have hB (x : ℝ) : differentialWedge f (PathIntegration.zeroForm g) x (fun _ ↦ 1) =
      deriv f x * g x := by
    rw [differentialWedge_zero, fderiv_apply_one_eq_deriv]
  simpa only [hA, hB] using h

/-- Both ordinary terms have literal Riemann integrals, including a singleton interval. -/
theorem one_variable_case {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun x ↦ f x * deriv g x) volume a b ∧
    IntervalIntegrable (fun x ↦ deriv f x * g x) volume a b ∧
    StieltjesPrototype.HasDarbouxRSIntegral (fun x ↦ f x * deriv g x) id a b
      (f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x) ∧
    StieltjesPrototype.HasDarbouxRSIntegral (fun x ↦ deriv f x * g x) id a b
      (∫ x in a..b, deriv f x * g x) := by
  have hfg : Continuous (fun x ↦ f x * deriv g x) :=
    hf.continuous.mul (hg.continuous_deriv (by norm_num))
  have hgf : Continuous (fun x ↦ deriv f x * g x) :=
    (hf.continuous_deriv (by norm_num)).mul hg.continuous
  refine ⟨hfg.intervalIntegrable a b, hgf.intervalIntegrable a b, ?_, ?_⟩
  · have hs := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hfg.continuousOn
    have hs' : StieltjesPrototype.HasDarbouxRSIntegral (fun x ↦ f x * deriv g x) id a b
        (∫ x in a..b, f x * deriv g x) := by
      simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
        ← Real.volume_eq_stieltjes_id, Pi.mul_apply] using hs
    rwa [one_variable_identity hf hg a b] at hs'
  · have hs := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hgf.continuousOn
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id, Pi.mul_apply] using hs

end Rudin.Chapter10.Exercise20
