module

public import Math.Rudin.Support.SimplexStokes
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.LinearAlgebra.Determinant
public import Math.Rudin.Support.SmoothChainIntegration
public import Math.Rudin.Chapter10.Exercise18
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support.MultivariateRiemann

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Parameter := EuclideanSpace ℝ (Fin 2)

def punctured : Set Space := {x | x ≠ 0}
def offAxis : Set Space := {x | 0 < x 0 ^ 2 + x 1 ^ 2}

/-- The coordinate form `dxᵢ ∧ dxⱼ`. -/
def coordinateTwo (i j : Fin 3) : Space [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := v 0 i * v 1 j - v 0 j * v 1 i
  map_update_add' v k a b := by
    fin_cases k <;> simp [Function.update_apply, PiLp.add_apply] <;> ring
  map_update_smul' v k a b := by
    fin_cases k <;> simp [Function.update_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v k l h hkl := by
    fin_cases k <;> fin_cases l <;> simp_all <;> ring
  cont := by fun_prop

@[simp] theorem coordinateTwo_apply (i j : Fin 3) (v : Fin 2 → Space) :
    coordinateTwo i j v = v 0 i * v 1 j - v 0 j * v 1 i := rfl

/-- This ambient expression represents the source form only on `punctured`. -/
def zeta : Form 2 Space := fun x =>
  (x 0 / ‖x‖ ^ 3) • coordinateTwo 1 2 +
  (x 1 / ‖x‖ ^ 3) • coordinateTwo 2 0 +
  (x 2 / ‖x‖ ^ 3) • coordinateTwo 0 1

@[simp] theorem zeta_apply (x : Space) (v : Fin 2 → Space) :
    zeta x v = (x 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      x 1 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) / ‖x‖ ^ 3 := by
  simp [zeta, div_mul_eq_mul_div, ← add_div]

/-- The source radius is the Euclidean norm, not the coordinate sup norm. -/
theorem radius_formula (x : Space) :
    ‖x‖ = Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

def sigma (p : Parameter) : Space := WithLp.toLp 2
  ![Real.sin (p 0) * Real.cos (p 1), Real.sin (p 0) * Real.sin (p 1), Real.cos (p 0)]

theorem sigma_norm (p : Parameter) : ‖sigma p‖ = 1 := by
  rw [radius_formula]
  have hu := Real.sin_sq_add_cos_sq (p 0)
  have hv := Real.sin_sq_add_cos_sq (p 1)
  have h : (sigma p) 0 ^ 2 + (sigma p) 1 ^ 2 + (sigma p) 2 ^ 2 = 1 := by
    dsimp [sigma]
    nlinarith [sq_nonneg (Real.sin (p 0))]
  rw [h, Real.sqrt_one]

theorem sigma_ne_zero (p : Parameter) : sigma p ≠ 0 := by
  intro h
  have := sigma_norm p
  simp [h] at this

/-- The permitted printed data can have identically zero image. -/
theorem origin_obstruction :
    ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) ∧
    ContDiff ℝ 2 (fun _ : ℝ => (0 : Space)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < (1 : ℝ)) ∧
    ¬ MapsTo (fun _ : Parameter => (1 : ℝ) • (0 : Space))
      {p | ∀ i, p i ∈ Icc (0 : ℝ) 1} punctured := by
  refine ⟨contDiff_const, contDiff_const, by intros; norm_num, ?_⟩
  intro h
  have h0 := h (show (0 : Parameter) ∈ {p | ∀ i, p i ∈ Icc (0 : ℝ) 1} by simp)
  simpa [punctured] using h0

/-- Cancellation for the general, nonseparable radial curtain. -/
theorem radial_curtain_algebra (h dh : Space) (r a b : ℝ) :
    zeta (r • h) ![a • h + r • dh, b • h] = 0 := by
  rw [zeta_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul]
  have hnum : r * h 0 * ((a * h 1 + r * dh 1) * (b * h 2) -
      (a * h 2 + r * dh 2) * (b * h 1)) +
    r * h 1 * ((a * h 2 + r * dh 2) * (b * h 0) -
      (a * h 0 + r * dh 0) * (b * h 2)) +
    r * h 2 * ((a * h 0 + r * dh 0) * (b * h 1) -
      (a * h 1 + r * dh 1) * (b * h 0)) = 0 := by ring
  rw [hnum, zero_div]

theorem norm_hasFDerivAt {x : Space} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Space => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1 <;> try { funext y; exact (Real.sqrt_sq (norm_nonneg y)).symm }
  ext y
  simp only [smul_apply, smul_eq_mul]
  field_simp
  <;> simp [smul_eq_mul, mul_comm]

theorem radial_coefficient_hasFDerivAt {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun y : Space => y i / ‖y‖ ^ 3)
      ((‖x‖ ^ 3)⁻¹ • EuclideanSpace.proj i -
        (3 * x i / ‖x‖ ^ 5) • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hi := (hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt x
    ((norm_hasFDerivAt hx).pow 3)
  convert ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.mul hi) using 1
  · funext y; exact div_eq_mul_inv _ _
  · ext y
    simp only [smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      EuclideanSpace.coe_proj, smul_eq_mul]
    norm_num
    field_simp
    <;> ring

theorem zeta_smooth : ContDiffOn ℝ 1 zeta punctured := by
  intro x hx
  have hn : ‖x‖ ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr hx)
  have hc (i : Fin 3) : ContDiffAt ℝ 1 (fun y : Space => y i / ‖y‖ ^ 3) x :=
    (EuclideanSpace.proj i).contDiff.contDiffAt.div ((contDiffAt_norm ℝ hx).pow 3) hn
  exact (((hc 0).smul contDiffAt_const).add ((hc 1).smul contDiffAt_const) |>.add
    ((hc 2).smul contDiffAt_const)).contDiffWithinAt

theorem punctured_open : IsOpen punctured := isOpen_ne

theorem zeta_closed {x : Space} (hx : x ∈ punctured) : extDeriv zeta x = 0 := by
  have hd : DifferentiableAt ℝ zeta x :=
    (zeta_smooth.differentiableOn one_ne_zero x hx).differentiableAt
      (punctured_open.mem_nhds hx)
  have he : extDeriv zeta x (EuclideanSpace.basisFun (Fin 3) ℝ) = 0 := by
    rw [show (EuclideanSpace.basisFun (Fin 3) ℝ : Fin 3 → Space) =
      (EuclideanSpace.single · 1) by funext i; exact EuclideanSpace.basisFun_apply _ _ _]
    rw [extDeriv_apply hd, Fin.sum_univ_three]
    simp only [EuclideanSpace.basisFun_apply, Fin.val_zero, Fin.val_one,
      Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, neg_neg]
    have h0 : (fun y : Space => zeta y ((0 : Fin 3).removeNth
        (EuclideanSpace.single · 1))) = (fun y => y 0 / ‖y‖ ^ 3) := by
      funext y
      norm_num [zeta_apply, Fin.removeNth, Fin.tail, Fin.succAbove]
    have h1 : (fun y : Space => zeta y ((1 : Fin 3).removeNth
        (EuclideanSpace.single · 1))) = (fun y => -(y 1 / ‖y‖ ^ 3)) := by
      funext y
      norm_num [zeta_apply, Fin.removeNth, Fin.tail, Fin.succAbove, neg_div]
    have h2 : (fun y : Space => zeta y ((2 : Fin 3).removeNth
        (EuclideanSpace.single · 1))) = (fun y => y 2 / ‖y‖ ^ 3) := by
      funext y
      norm_num [zeta_apply, Fin.removeNth, Fin.tail, Fin.succAbove]
    rw [h0, h1, h2, (radial_coefficient_hasFDerivAt hx 0).fderiv,
      fderiv_fun_neg, (radial_coefficient_hasFDerivAt hx 1).fderiv,
      (radial_coefficient_hasFDerivAt hx 2).fderiv]
    simp only [sub_apply, add_apply, smul_apply, neg_apply, smul_eq_mul]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hs : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    field_simp
    nlinarith
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [AlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (extDeriv zeta x).toAlternatingMap]
  change (extDeriv zeta x (EuclideanSpace.basisFun (Fin 3) ℝ)) • _ = _
  rw [he, zero_smul]
  rfl

def curtain (ρ : Parameter → ℝ) (h : ℝ → Space) (p : Parameter) : Space :=
  ρ p • h (p 0)

def unitSquare : Set Parameter := {p | ∀ i, p i ∈ Icc (0 : ℝ) 1}

theorem curtain_nonzero {ρ : Parameter → ℝ} {h : ℝ → Space} {p : Parameter}
    (hρ : 0 < ρ p) (hh : h (p 0) ≠ 0) : curtain ρ h p ≠ 0 :=
  smul_ne_zero (ne_of_gt hρ) hh

/-- Both partials are genuine derivatives. The radius may depend on both parameters. -/
theorem curtain_derivatives {ρ : Parameter → ℝ} {h : ℝ → Space} {p : Parameter}
    (hρ : DifferentiableAt ℝ ρ p) (hh : DifferentiableAt ℝ h (p 0)) :
    fderiv ℝ (curtain ρ h) p (EuclideanSpace.single 0 1) =
      fderiv ℝ ρ p (EuclideanSpace.single 0 1) • h (p 0) + ρ p • deriv h (p 0) ∧
    fderiv ℝ (curtain ρ h) p (EuclideanSpace.single 1 1) =
      fderiv ℝ ρ p (EuclideanSpace.single 1 1) • h (p 0) := by
  have hp := (EuclideanSpace.proj 0 : Parameter →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hd := hρ.hasFDerivAt.smul (hh.hasFDerivAt.comp p hp)
  change HasFDerivAt (curtain ρ h) _ p at hd
  rw [hd.fderiv]
  constructor <;> simp [ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, add_comm]

/-- The actual pullback vanishes. No singular value is used in this statement. -/
theorem curtain_pullback {ρ : Parameter → ℝ} {h : ℝ → Space} {p : Parameter}
    (hρ : DifferentiableAt ℝ ρ p) (hh : DifferentiableAt ℝ h (p 0))
    (hpos : 0 < ρ p) (hn : h (p 0) ≠ 0) :
    curtain ρ h p ∈ punctured ∧
    pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1) = 0 := by
  refine ⟨curtain_nonzero hpos hn, ?_⟩
  have hd := curtain_derivatives hρ hh
  rw [pullback_apply]
  have hv : (fun i : Fin 2 => fderiv ℝ (curtain ρ h) p (EuclideanSpace.single i 1)) =
      ![fderiv ℝ ρ p (EuclideanSpace.single 0 1) • h (p 0) + ρ p • deriv h (p 0),
        fderiv ℝ ρ p (EuclideanSpace.single 1 1) • h (p 0)] := by
    funext i; fin_cases i
    · exact hd.1
    · exact hd.2
  rw [hv]
  exact radial_curtain_algebra _ _ _ _ _

theorem unitSquare_coordinates : unitSquare =
    (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc 0 1 := by
  ext p
  simp [unitSquare, Pi.le_def, forall_and]

theorem unitSquare_compact : IsCompact unitSquare := by
  rw [unitSquare_coordinates]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

/-- Direct proof from the surface integrand, with integrability and source integrals. -/
theorem corrected_general_curtain {ρ : Parameter → ℝ} {h : ℝ → Space}
    (hρ : ∀ p ∈ unitSquare, DifferentiableAt ℝ ρ p)
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ h s)
    (hpos : ∀ p ∈ unitSquare, 0 < ρ p)
    (hn : ∀ s ∈ Icc (0 : ℝ) 1, h s ≠ 0) :
    MapsTo (curtain ρ h) unitSquare punctured ∧
    IntegrableOn (fun p => pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1))
      unitSquare ∧
    (∫ p in unitSquare, pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1)) = 0 ∧
    (∀ σ : Equiv.Perm (Fin 2), HasSourceIntegral 2 0 1
      ((fun p => pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1)) ∘
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation σ) 0) := by
  have hz (p) (hp : p ∈ unitSquare) :=
    curtain_pullback (hρ p hp) (hh (p 0) (hp 0)) (hpos p hp) (hn (p 0) (hp 0))
  have hc : ContinuousOn
      (fun p => pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1)) unitSquare :=
    continuousOn_const.congr (fun p hp => (hz p hp).2)
  have hi : (∫ p in unitSquare,
      pullback zeta (curtain ρ h) p (EuclideanSpace.single · 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun p hp => (hz p hp).2
  refine ⟨fun p hp => (hz p hp).1, hc.integrableOn_compact unitSquare_compact, hi, ?_⟩
  intro σ
  have hs := euclidean_box_source (a := (0 : Fin 2 → ℝ)) (b := 1)
    (by intro i; norm_num) (unitSquare_coordinates ▸ hc) σ
  rw [← unitSquare_coordinates, hi] at hs
  convert hs using 1 <;> { funext i; rfl }

def sigmaU (p : Parameter) : Space := WithLp.toLp 2
  ![Real.cos (p 0) * Real.cos (p 1), Real.cos (p 0) * Real.sin (p 1), -Real.sin (p 0)]
def sigmaV (p : Parameter) : Space := WithLp.toLp 2
  ![-Real.sin (p 0) * Real.sin (p 1), Real.sin (p 0) * Real.cos (p 1), 0]

theorem sigma_smooth : ContDiff ℝ 2 sigma := by
  apply contDiff_euclidean.mpr
  intro i; fin_cases i <;> dsimp [sigma] <;> fun_prop

theorem sigma_hasFDerivAt (p : Parameter) : HasFDerivAt sigma
    ((EuclideanSpace.proj 0 : Parameter →L[ℝ] ℝ).smulRight (sigmaU p) +
      (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).smulRight (sigmaV p)) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  have h0 := (EuclideanSpace.proj 0 : Parameter →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h1 := (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hc0 := h0.cos
  have hs0 := h0.sin
  have hc1 := h1.cos
  have hs1 := h1.sin
  fin_cases i
  · convert (hs0.mul hc1).hasFDerivWithinAt using 1
    · funext q; rfl
    · ext q
      simp [sigmaU, sigmaV, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply]
      ring
  · convert (hs0.mul hs1).hasFDerivWithinAt using 1
    · funext q; rfl
    · ext q
      simp [sigmaU, sigmaV, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply]
      ring
  · convert hc0.hasFDerivWithinAt using 1
    · funext q; rfl
    · ext q
      simp [sigmaU, sigmaV, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply]
      ring

def cross (a b : Space) : Space := WithLp.toLp 2
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def normal (S : Parameter → Space) (p : Parameter) : Space :=
  cross (fderiv ℝ S p (EuclideanSpace.single 0 1))
    (fderiv ℝ S p (EuclideanSpace.single 1 1))

def area (S : Parameter → Space) (E : Set Parameter) : ℝ := ∫ p in E, ‖normal S p‖
def surfaceIntegral (S : Parameter → Space) (E : Set Parameter) : ℝ :=
  ∫ p in E, pullback zeta S p (EuclideanSpace.single · 1)

theorem zeta_cross (x a b : Space) :
    zeta x ![a,b] = inner ℝ x (cross a b) / ‖x‖ ^ 3 := by
  simp [zeta_apply, cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, mul_comm]

theorem sigma_cross (p : Parameter) : cross (sigmaU p) (sigmaV p) =
    Real.sin (p 0) • sigma p := by
  ext i
  have hv := Real.sin_sq_add_cos_sq (p 1)
  fin_cases i <;> simp [cross, sigmaU, sigmaV, sigma, PiLp.smul_apply, smul_eq_mul]
  all_goals try ring
  linear_combination Real.cos (p 0) * Real.sin (p 0) * hv

theorem sigma_normal (p : Parameter) : normal sigma p = Real.sin (p 0) • sigma p := by
  rw [normal, (sigma_hasFDerivAt p).fderiv]
  simpa [ContinuousLinearMap.smulRight_apply] using sigma_cross p

theorem sigma_area_density {p : Parameter} (hu : p 0 ∈ Icc (0 : ℝ) Real.pi) :
    ‖normal sigma p‖ = Real.sin (p 0) := by
  rw [sigma_normal, norm_smul, sigma_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2)]

theorem sigma_pullback (p : Parameter) :
    pullback zeta sigma p (EuclideanSpace.single · 1) = Real.sin (p 0) := by
  rw [pullback_apply]
  have hv : (fun i : Fin 2 => fderiv ℝ sigma p (EuclideanSpace.single i 1)) =
      ![sigmaU p, sigmaV p] := by
    rw [(sigma_hasFDerivAt p).fderiv]
    funext i; fin_cases i <;> simp [ContinuousLinearMap.smulRight_apply]
  rw [hv, zeta_cross, sigma_cross, inner_smul_right,
    real_inner_self_eq_norm_sq, sigma_norm]
  simp

/-- The area is the norm of the actual cross product, not a definition by flux. -/
theorem sphere_area {E : Set Parameter} (hE : IsCompact E)
    (hD : ∀ p ∈ E, p 0 ∈ Icc (0 : ℝ) Real.pi) :
    IntegrableOn (fun p => pullback zeta sigma p (EuclideanSpace.single · 1)) E ∧
    IntegrableOn (fun p => ‖normal sigma p‖) E ∧
    surfaceIntegral sigma E = (∫ p in E, Real.sin (p 0)) ∧
    surfaceIntegral sigma E = area sigma E := by
  have hs : Continuous (fun p : Parameter => Real.sin (p 0)) := by fun_prop
  have hi : IntegrableOn (fun p : Parameter => Real.sin (p 0)) E :=
    hs.continuousOn.integrableOn_compact hE
  have ha : EqOn (fun p => ‖normal sigma p‖) (fun p => Real.sin (p 0)) E :=
    fun p hp => sigma_area_density (hD p hp)
  refine ⟨by simpa only [sigma_pullback] using hi,
    (hs.continuousOn.congr ha).integrableOn_compact hE, ?_, ?_⟩
  · simp only [surfaceIntegral, sigma_pullback]
  · exact (show surfaceIntegral sigma E = ∫ p in E, Real.sin (p 0) by
      simp only [surfaceIntegral, sigma_pullback]).trans
        (setIntegral_congr_fun hE.measurableSet (fun p hp => (ha hp).symm))

def axisRadiusSq (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

def coordinateOne (i : Fin 3) : Space [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ Space ℝ 0 (EuclideanSpace.proj i)

def eta : Form 1 Space := fun x =>
  (x 0 / axisRadiusSq x) • coordinateOne 1 -
    (x 1 / axisRadiusSq x) • coordinateOne 0

def lambda : Form 1 Space := fun x => -(x 2 / ‖x‖) • eta x

@[simp] theorem coordinateOne_apply (i : Fin 3) (v : Fin 1 → Space) :
    coordinateOne i v = v 0 i := rfl

theorem offAxis_nonzero {x : Space} (hx : x ∈ offAxis) : x ≠ 0 := by
  intro h; simp [offAxis, h] at hx

theorem axisRadiusSq_hasFDerivAt (x : Space) : HasFDerivAt axisRadiusSq
    ((2 * x 0) • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) +
      (2 * x 1) • (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)) x := by
  convert ((EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2 |>.add
    (((EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2) using 1
  · rfl
  · simp

theorem lambda_smooth : ContDiffOn ℝ 1 lambda offAxis := by
  intro x hx
  have ha : ContDiffAt ℝ 1 axisRadiusSq x := by unfold axisRadiusSq; fun_prop
  have han : axisRadiusSq x ≠ 0 := ne_of_gt hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (offAxis_nonzero hx)
  have hnorm := contDiffAt_norm (n := 1) ℝ (offAxis_nonzero hx)
  have hc (i : Fin 3) : ContDiffAt ℝ 1 (fun y : Space => y i / axisRadiusSq y) x :=
    (EuclideanSpace.proj i).contDiff.contDiffAt.div ha han
  have he : ContDiffAt ℝ 1 eta x :=
    ((hc 0).smul (contDiffAt_const (c := coordinateOne 1))).sub
      ((hc 1).smul (contDiffAt_const (c := coordinateOne 0)))
  exact (((EuclideanSpace.proj 2 : Space →L[ℝ] ℝ).contDiff.contDiffAt.div hnorm hn).neg.smul
    he).contDiffWithinAt

theorem lambda_apply (x : Space) (v : Fin 1 → Space) :
    lambda x v = (x 2 * (x 1 * v 0 0 - x 0 * v 0 1)) / (‖x‖ * axisRadiusSq x) := by
  simp [lambda, eta, div_eq_mul_inv]
  ring

def lambdaNumeratorD (x v : Space) : Space →L[ℝ] ℝ :=
  (x 1 * v 0 - x 0 * v 1) • EuclideanSpace.proj 2 +
    x 2 • (v 0 • EuclideanSpace.proj 1 - v 1 • EuclideanSpace.proj 0)

def lambdaDenominatorD (x : Space) : Space →L[ℝ] ℝ :=
  (axisRadiusSq x / ‖x‖) • innerSL ℝ x +
    ‖x‖ • ((2 * x 0) • EuclideanSpace.proj 0 + (2 * x 1) • EuclideanSpace.proj 1)

theorem lambda_eval_hasFDerivAt {x : Space} (hx : x ∈ offAxis) (v : Fin 1 → Space) :
    HasFDerivAt (fun y => lambda y v)
      (((‖x‖ * axisRadiusSq x)⁻¹) • lambdaNumeratorD x (v 0) -
        ((x 2 * (x 1 * v 0 0 - x 0 * v 0 1)) / (‖x‖ * axisRadiusSq x) ^ 2) •
          lambdaDenominatorD x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (offAxis_nonzero hx)
  have ha : axisRadiusSq x ≠ 0 := ne_of_gt hx
  have hp (i : Fin 3) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hnum : HasFDerivAt (fun y : Space => y 2 * (y 1 * v 0 0 - y 0 * v 0 1))
      (lambdaNumeratorD x (v 0)) x := by
    convert (hp 2).mul (((hp 1).mul_const (v 0 0)).sub ((hp 0).mul_const (v 0 1))) using 1
    · rfl
    · ext w
      simp [lambdaNumeratorD]
      ring
  have hden : HasFDerivAt (fun y : Space => ‖y‖ * axisRadiusSq y)
      (lambdaDenominatorD x) x := by
    convert (norm_hasFDerivAt (offAxis_nonzero hx)).mul (axisRadiusSq_hasFDerivAt x) using 1
    ext w
    simp [lambdaDenominatorD, div_eq_mul_inv]
    ring
  have hi := (hasDerivAt_inv (mul_ne_zero hn ha)).comp_hasFDerivAt x hden
  convert hnum.mul hi using 1
  · funext y
    rw [lambda_apply, div_eq_mul_inv]
    rfl
  · ext w
    simp [div_eq_mul_inv]
    ring

theorem offAxis_open : IsOpen offAxis := by
  apply isOpen_lt continuous_const
  fun_prop

set_option maxHeartbeats 800000 in
theorem lambda_exterior {x : Space} (hx : x ∈ offAxis) : extDeriv lambda x = zeta x := by
  have hd : DifferentiableAt ℝ lambda x :=
    (lambda_smooth.differentiableOn one_ne_zero x hx).differentiableAt
      (offAxis_open.mem_nhds hx)
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (offAxis_nonzero hx)
  have ha : axisRadiusSq x ≠ 0 := ne_of_gt hx
  have hs : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro v hv
  change extDeriv lambda x _ = zeta x _
  rw [extDeriv_apply hd, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [(lambda_eval_hasFDerivAt hx _).fderiv, (lambda_eval_hasFDerivAt hx _).fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, neg_neg]
  simp [lambdaNumeratorD, lambdaDenominatorD, Fin.removeNth, Fin.tail,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three]
  generalize h0 : v 0 = i
  generalize h1 : v 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [h0, h1, zeta_apply, axisRadiusSq] at * <;>
    field_simp <;> first | nlinarith | (rw [hs]; ring)

theorem zeta_det (x : Space) (v : Fin 2 → Space) :
    zeta x v = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
      (Fin.cons x v) / ‖x‖ ^ 3 := by
  rw [zeta_apply, Module.Basis.det_apply, Matrix.det_fin_three]
  have hv2 : (Fin.cons x v : Fin 3 → Space) 2 = v 1 := by
    exact Fin.cons_succ (α := fun _ : Fin 3 => Space) x v 1
  simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, hv2]
  ring

/-- Orthogonal transport includes the determinant sign; reflections are allowed. -/
theorem zeta_orthogonal_pullback (Q : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    pullback zeta Q x = LinearMap.det Q.toLinearEquiv.toLinearMap • zeta x := by
  ext v
  have hd : fderiv ℝ (Q : Space → Space) x =
      Q.toContinuousLinearEquiv.toContinuousLinearMap := Q.toContinuousLinearEquiv.fderiv
  rw [pullback_apply, hd]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  rw [zeta_det, zeta_det, Q.norm_map]
  have hm := Module.Basis.det_comp (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    Q.toLinearEquiv.toLinearMap (Fin.cons x v)
  convert congrArg (fun t => t / ‖x‖ ^ 3) hm using 1
  · congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · ring

theorem orthogonal_det_ne_zero (Q : Space ≃ₗᵢ[ℝ] Space) :
    LinearMap.det Q.toLinearEquiv.toLinearMap ≠ 0 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  exact (Q.toLinearEquiv.isUnit_det _ _).ne_zero

/-- A concrete orthogonal reflection carries any nonzero direction to the z-axis. -/
def axisTransport (v : Space) : Space ≃ₗᵢ[ℝ] Space :=
  Submodule.reflection (ℝ ∙ (v - ‖v‖ • EuclideanSpace.single 2 1))ᗮ

theorem axisTransport_direction (v : Space) :
    axisTransport v v = ‖v‖ • EuclideanSpace.single 2 1 := by
  apply Submodule.reflection_sub
  simp [norm_smul]

theorem offAxis_iff_not_axis (x : Space) :
    x ∈ offAxis ↔ ¬ ∃ t : ℝ, t • (EuclideanSpace.single 2 1 : Space) = x := by
  constructor
  · intro hx ⟨t, ht⟩
    rw [← ht] at hx
    simpa [offAxis, PiLp.smul_apply] using hx
  · intro hx
    by_contra hn
    have hz : x 0 = 0 ∧ x 1 = 0 := by
      simp only [offAxis, mem_setOf_eq, not_lt] at hn
      constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    apply hx
    refine ⟨x 2, ?_⟩
    ext i; fin_cases i <;> simp [hz.1, hz.2, PiLp.smul_apply]

theorem transport_domain {v : Space} (hv : v ≠ 0) (x : Space) :
    axisTransport v x ∈ offAxis ↔ x ∉ (ℝ ∙ v : Submodule ℝ Space) := by
  rw [offAxis_iff_not_axis, Submodule.mem_span_singleton]
  apply not_congr
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / ‖v‖, (axisTransport v).injective ?_⟩
    rw [map_smul, axisTransport_direction, smul_smul,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv), ht]
  · rintro ⟨t, rfl⟩
    refine ⟨t * ‖v‖, ?_⟩
    rw [map_smul, axisTransport_direction, smul_smul]

/-- Primitive on the complement of a line, by actual orthogonal transport. -/
def linePrimitive (v : Space) : Form 1 Space :=
  (LinearMap.det (axisTransport v).toLinearEquiv.toLinearMap)⁻¹ •
    pullback lambda (axisTransport v)

theorem line_exact {v : Space} (hv : v ≠ 0) :
    ContDiffOn ℝ 1 (linePrimitive v) (↑(ℝ ∙ v : Submodule ℝ Space))ᶜ ∧
    ∀ x ∉ (ℝ ∙ v : Submodule ℝ Space), extDeriv (linePrimitive v) x = zeta x := by
  have hLam (x : Space) (hx : x ∉ (ℝ ∙ v : Submodule ℝ Space)) :
      ContDiffAt ℝ 1 lambda (axisTransport v x) :=
    (lambda_smooth _ ((transport_domain hv x).mpr hx)).contDiffAt
      (offAxis_open.mem_nhds ((transport_domain hv x).mpr hx))
  have hQ : ContDiff ℝ 2 (axisTransport v) :=
    (axisTransport v).toContinuousLinearEquiv.contDiff
  constructor
  · intro x hx
    exact (contDiffAt_const.smul
      (Rudin.Support.SimplexStokes.pullback_contDiffAt (hLam x hx) hQ.contDiffAt)).contDiffWithinAt
  · intro x hx
    rw [linePrimitive, extDeriv_smul, exterior_pullback lambda (axisTransport v) x
      ((hLam x hx).differentiableAt one_ne_zero) hQ.contDiffAt]
    have hpb : pullback (extDeriv lambda) (axisTransport v) x =
        pullback zeta (axisTransport v) x := by
      ext w
      simp only [pullback_apply, lambda_exterior ((transport_domain hv x).mpr hx)]
    rw [hpb, zeta_orthogonal_pullback, smul_smul,
      inv_mul_cancel₀ (orthogonal_det_ne_zero _), one_smul]

theorem lambda_radial (x w : Space) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    lambda (r • x) (fun _ => a • x + r • w) = lambda x (fun _ => w) := by
  rw [lambda_apply, lambda_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  simp only [axisRadiusSq, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  have hrn := ne_of_gt hr
  field_simp
  <;> ring

def radialSurface (f : Parameter → ℝ) (p : Parameter) : Space := f p • sigma p

theorem radialSurface_nonzero {f : Parameter → ℝ} {p : Parameter} (hf : 0 < f p) :
    radialSurface f p ≠ 0 := smul_ne_zero (ne_of_gt hf) (sigma_ne_zero p)

theorem lambda_radial_pullback {f : Parameter → ℝ} {p : Parameter}
    (hf : DifferentiableAt ℝ f p) (hpos : 0 < f p) :
    pullback lambda (radialSurface f) p = pullback lambda sigma p := by
  have hd := hf.hasFDerivAt.smul (sigma_hasFDerivAt p)
  change HasFDerivAt (radialSurface f) _ p at hd
  ext v
  rw [pullback_apply, pullback_apply, hd.fderiv]
  have hv : (fun i : Fin 1 =>
      (f p • ((EuclideanSpace.proj 0 : Parameter →L[ℝ] ℝ).smulRight (sigmaU p) +
        (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).smulRight (sigmaV p)) +
        (fderiv ℝ f p).smulRight (sigma p)) (v i)) =
      (fun _ => (fderiv ℝ f p) (v 0) • sigma p +
        f p • fderiv ℝ sigma p (v 0)) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [(sigma_hasFDerivAt p).fderiv]
    simp [ContinuousLinearMap.smulRight_apply, add_comm]
  rw [hv]
  have hright : (fun i : Fin 1 => fderiv ℝ sigma p (v i)) =
      (fun _ => fderiv ℝ sigma p (v 0)) := by
    funext i; congr 2; exact Subsingleton.elim _ _
  rw [hright]
  exact lambda_radial _ _ hpos _

theorem sigma_offAxis {p : Parameter} (hu : p 0 ∈ Ioo (0 : ℝ) Real.pi) :
    sigma p ∈ offAxis := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hv := Real.sin_sq_add_cos_sq (p 1)
  change 0 < (sigma p) 0 ^ 2 + (sigma p) 1 ^ 2
  have he : (sigma p) 0 ^ 2 + (sigma p) 1 ^ 2 = Real.sin (p 0) ^ 2 := by
    dsimp [sigma]
    linear_combination Real.sin (p 0) ^ 2 * hv
  rw [he]
  exact sq_pos_of_pos hs

theorem smul_offAxis {x : Space} (hx : x ∈ offAxis) {r : ℝ} (hr : 0 < r) :
    r • x ∈ offAxis := by
  change 0 < (r • x) 0 ^ 2 + (r • x) 1 ^ 2
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow]
  rw [← mul_add]
  exact mul_pos (sq_pos_of_pos hr) hx

/-- The alternative proof starts from the explicit primitive, without any curtain lemma. -/
theorem radial_pullback_from_exactness {f : Parameter → ℝ} {p : Parameter}
    (hf : ContDiffAt ℝ 2 f p) (hpos : 0 < f p)
    (hu : p 0 ∈ Ioo (0 : ℝ) Real.pi) :
    pullback zeta (radialSurface f) p = pullback zeta sigma p := by
  have hS : ContDiffAt ℝ 2 (radialSurface f) p := hf.smul sigma_smooth.contDiffAt
  have ha := sigma_offAxis hu
  have hb : radialSurface f p ∈ offAxis := smul_offAxis ha hpos
  have hLa := (lambda_smooth _ ha).contDiffAt (offAxis_open.mem_nhds ha)
  have hLb := (lambda_smooth _ hb).contDiffAt (offAxis_open.mem_nhds hb)
  have heq : pullback lambda (radialSurface f) =ᶠ[nhds p] pullback lambda sigma := by
    have hfn := hf.eventually (by norm_num)
    have hpn := hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    filter_upwards [hfn, hpn] with q hq hqp
    exact lambda_radial_pullback (hq.differentiableAt (by norm_num)) hqp
  have he := heq.extDeriv_eq
  rw [exterior_pullback lambda (radialSurface f) p
      (hLb.differentiableAt one_ne_zero) hS,
    exterior_pullback lambda sigma p (hLa.differentiableAt one_ne_zero)
      sigma_smooth.contDiffAt] at he
  simpa only [pullback, lambda_exterior ha, lambda_exterior hb] using he

def sphereDomain : Set Parameter :=
  {p | p 0 ∈ Icc (0 : ℝ) Real.pi ∧ p 1 ∈ Icc (0 : ℝ) (2 * Real.pi)}

/-- Move each latitude strictly toward the equator, without moving its longitude. -/
def poleApproach (p : Parameter) (t : ℝ) : Parameter := WithLp.toLp 2
  ![(1 - t) * p 0 + t * (Real.pi / 2), p 1]

theorem poleApproach_inside {p : Parameter} (hp : p ∈ sphereDomain) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    poleApproach p t ∈ sphereDomain ∧
    poleApproach p t 0 ∈ Ioo (0 : ℝ) Real.pi := by
  have hπ := Real.pi_pos
  have hu := hp.1
  have htπ := mul_pos ht.1 hπ
  have hu' : (1 - t) * p 0 + t * (Real.pi / 2) ∈ Ioo (0 : ℝ) Real.pi := by
    constructor
    · nlinarith [htπ, mul_nonneg (le_of_lt (sub_pos.mpr ht.2)) hu.1]
    · nlinarith [htπ, mul_nonneg (le_of_lt (sub_pos.mpr ht.2)) (sub_nonneg.mpr hu.2)]
  exact ⟨⟨⟨hu'.1.le, hu'.2.le⟩, hp.2⟩, hu'⟩

theorem poleApproach_limit (p : Parameter) :
    Filter.Tendsto (poleApproach p) (nhdsWithin 0 (Ioi 0)) (nhds p) := by
  have hc : Continuous (poleApproach p) := by
    unfold poleApproach
    fun_prop
  have h0 : poleApproach p 0 = p := by
    ext i; fin_cases i <;> simp [poleApproach]
  simpa only [h0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Actual one-sided limits justify the alternative exactness proof at both poles. -/
theorem radial_exactness_pole_limit {f : Parameter → ℝ}
    (hf : ∀ q ∈ sphereDomain, ContDiffAt ℝ 2 f q)
    (hpos : ∀ q ∈ sphereDomain, 0 < f q) {p : Parameter} (hp : p ∈ sphereDomain) :
    Filter.Tendsto
      (fun t => pullback zeta (radialSurface f) (poleApproach p t) (EuclideanSpace.single · 1))
      (nhdsWithin 0 (Ioi 0))
      (nhds (pullback zeta (radialSurface f) p (EuclideanSpace.single · 1))) ∧
    pullback zeta (radialSurface f) p (EuclideanSpace.single · 1) = Real.sin (p 0) := by
  have hS : ContDiffAt ℝ 2 (radialSurface f) p := (hf p hp).smul sigma_smooth.contDiffAt
  have hn := radialSurface_nonzero (hpos p hp)
  have hZ : ContDiffAt ℝ 1 zeta (radialSurface f p) :=
    (zeta_smooth _ hn).contDiffAt (punctured_open.mem_nhds hn)
  have hpb := (Rudin.Support.SimplexStokes.pullback_contDiffAt hZ hS).continuousAt
  have hc : ContinuousAt
      (fun q => pullback zeta (radialSurface f) q (EuclideanSpace.single · 1)) p :=
    hpb.eval continuousAt_const
  have hl := hc.tendsto.comp (poleApproach_limit p)
  refine ⟨hl, ?_⟩
  have hs : ContinuousAt (fun q : Parameter => Real.sin (q 0)) p :=
    Real.continuous_sin.continuousAt.comp (EuclideanSpace.proj 0).continuous.continuousAt
  have hr := hs.tendsto.comp (poleApproach_limit p)
  have heq : (fun t => pullback zeta (radialSurface f) (poleApproach p t)
      (EuclideanSpace.single · 1)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun t => Real.sin (poleApproach p t 0)) := by
    have ht1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, ht1] with t ht0 ht1
    have ht := poleApproach_inside hp ⟨ht0, ht1⟩
    rw [radial_pullback_from_exactness (hf _ ht.1) (hpos _ ht.1) ht.2, sigma_pullback]
  exact tendsto_nhds_unique hl (hr.congr' heq.symm)

/-- Alternative derivation of the surface equality, including polar boundary points. -/
theorem radial_area_from_exactness {f : Parameter → ℝ}
    (hf : ∀ q ∈ sphereDomain, ContDiffAt ℝ 2 f q)
    (hpos : ∀ q ∈ sphereDomain, 0 < f q) {E : Set Parameter}
    (hE : IsCompact E) (hED : E ⊆ sphereDomain) :
    IntegrableOn (fun p => pullback zeta (radialSurface f) p (EuclideanSpace.single · 1)) E ∧
    surfaceIntegral (radialSurface f) E = surfaceIntegral sigma E ∧
    surfaceIntegral (radialSurface f) E = area sigma E := by
  have he (p) (hp : p ∈ E) := (radial_exactness_pole_limit hf hpos (hED hp)).2
  have hs : ContinuousOn (fun p : Parameter => Real.sin (p 0)) E := by fun_prop
  have hI : surfaceIntegral (radialSurface f) E = surfaceIntegral sigma E := by
    apply setIntegral_congr_fun hE.measurableSet
    intro p hp
    exact (he p hp).trans (sigma_pullback p).symm
  exact ⟨(hs.congr he).integrableOn_compact hE, hI,
    hI.trans (sphere_area hE (fun p hp => (hED hp).1)).2.2.2⟩

/-- The printed separable curtain is a specialization, with its correction explicit. -/
theorem corrected_radial_surface {g : ℝ → ℝ} {h : ℝ → Space}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 g t)
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 h s)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < g t)
    (hn : ∀ s ∈ Icc (0 : ℝ) 1, h s ≠ 0) :
    MapsTo (curtain (fun p => g (p 1)) h) unitSquare punctured ∧
    IntegrableOn (fun p => pullback zeta (curtain (fun p => g (p 1)) h) p
      (EuclideanSpace.single · 1)) unitSquare ∧
    (∫ p in unitSquare, pullback zeta (curtain (fun p => g (p 1)) h) p
      (EuclideanSpace.single · 1)) = 0 ∧
    (∀ σ : Equiv.Perm (Fin 2), HasSourceIntegral 2 0 1
      ((fun p => pullback zeta (curtain (fun p => g (p 1)) h) p
        (EuclideanSpace.single · 1)) ∘ (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘
          coordinatePermutation σ) 0) := by
  apply corrected_general_curtain
  · intro p hp
    exact ((hg (p 1) (hp 1)).differentiableAt (by norm_num)).comp p
      (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).differentiableAt
  · intro s hs
    exact (hh s hs).differentiableAt (by norm_num)
  · exact fun p hp => hpos (p 1) (hp 1)
  · exact hn

/-- Literal Riemann witnesses for spherical coordinate rectangles, including poles. -/
theorem sphere_rectangle_source {a b : Fin 2 → ℝ} (hab : a ≤ b)
    (σ : Equiv.Perm (Fin 2)) :
    HasSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      ((fun p => pullback zeta sigma p (EuclideanSpace.single · 1)) ∘
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation σ)
      (surfaceIntegral sigma ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b)) := by
  apply euclidean_box_source hab
  simp only [sigma_pullback]
  fun_prop

theorem sphere_simplex_source (σ : Equiv.Perm (Fin 2)) :
    HasSourceIntegral 2 0 1
      (simplexZeroExtension ((fun p => pullback zeta sigma p (EuclideanSpace.single · 1)) ∘
        (EuclideanSpace.equiv (Fin 2) ℝ).symm) ∘ coordinatePermutation σ)
      (surfaceIntegral sigma (standardSimplex 2)) := by
  exact (euclidean_simplex_source (f := fun p => pullback zeta sigma p
    (EuclideanSpace.single · 1)) (by simp only [sigma_pullback]; fun_prop) σ).2.1

/-- The limiting exactness proof also supplies the source integrals on every source rectangle. -/
theorem radial_rectangle_source {f : Parameter → ℝ}
    (hf : ∀ q ∈ sphereDomain, ContDiffAt ℝ 2 f q)
    (hpos : ∀ q ∈ sphereDomain, 0 < f q) {a b : Fin 2 → ℝ} (hab : a ≤ b)
    (hD : (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b ⊆ sphereDomain)
    (σ : Equiv.Perm (Fin 2)) :
    HasSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      ((fun p => pullback zeta (radialSurface f) p (EuclideanSpace.single · 1)) ∘
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation σ)
      (surfaceIntegral (radialSurface f) ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b)) := by
  apply euclidean_box_source hab
  have hs : ContinuousOn (fun p : Parameter => Real.sin (p 0))
      ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b) := by fun_prop
  exact hs.congr (fun p hp => (radial_exactness_pole_limit hf hpos (hD hp)).2)

theorem radial_interpolation_positive {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * r := by
  by_cases h : t = 1
  · simpa [h] using hr
  · have ht' : t < 1 := lt_of_le_of_ne ht.2 h
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht') (mul_nonneg ht.1 hr.le)

def radialHomotopy (f : Parameter → ℝ) (q : Space) : Space :=
  let p : Parameter := WithLp.toLp 2 ![q 1,q 2]
  (1 - q 0 + q 0 * f p) • sigma p

/-- Positivity and the unit vector supply all origin avoidance needed in the homotopy. -/
theorem radialHomotopy_nonzero {f : Parameter → ℝ} {q : Space}
    (hf : 0 < f (WithLp.toLp 2 ![q 1,q 2])) (ht : q 0 ∈ Icc (0 : ℝ) 1) :
    radialHomotopy f q ≠ 0 :=
  smul_ne_zero (ne_of_gt (radial_interpolation_positive hf ht)) (sigma_ne_zero _)

theorem radialHomotopy_ends (f : Parameter → ℝ) (p : Parameter) :
    radialHomotopy f (WithLp.toLp 2 ![0,p 0,p 1]) = sigma p ∧
    radialHomotopy f (WithLp.toLp 2 ![1,p 0,p 1]) = radialSurface f p := by
  have he : (WithLp.toLp 2 ![p 0,p 1] : Parameter) = p := by
    ext i; fin_cases i <;> rfl
  simp [radialHomotopy, radialSurface, he]

/-- Both polar edges have zero cross-product area but do not belong to lambda's domain. -/
theorem pole_models (v : ℝ) :
    sigma (WithLp.toLp 2 ![0,v]) = EuclideanSpace.single 2 1 ∧
    sigma (WithLp.toLp 2 ![Real.pi,v]) = -(EuclideanSpace.single 2 1 : Space) ∧
    normal sigma (WithLp.toLp 2 ![0,v]) = 0 ∧
    normal sigma (WithLp.toLp 2 ![Real.pi,v]) = 0 ∧
    sigma (WithLp.toLp 2 ![0,v]) ∉ offAxis ∧
    sigma (WithLp.toLp 2 ![Real.pi,v]) ∉ offAxis := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [sigma]
  · ext i; fin_cases i <;> simp [sigma]
  · simp [sigma_normal]
  · simp [sigma_normal]
  · simp [offAxis, sigma]
  · simp [offAxis, sigma]

/-- A nonlinear curtain with a nonseparable radius tests the actual derivatives. -/
theorem nonlinear_curtain_model (p : Parameter) :
    let r := fun q : Parameter => 2 + q 0 ^ 2 + q 1 ^ 2
    let h := fun s : ℝ => (WithLp.toLp 2 ![1,s,s^2] : Space)
    curtain r h p ∈ punctured ∧
      pullback zeta (curtain r h) p (EuclideanSpace.single · 1) = 0 := by
  dsimp
  apply curtain_pullback
  · fun_prop
  · apply differentiableAt_euclidean.mpr
    intro i; fin_cases i <;> dsimp <;> fun_prop
  · positivity
  · intro h
    have he := congrArg (fun x : Space => x 0) h
    norm_num at he

end Rudin.Chapter10.Exercise22

noncomputable section
namespace Rudin.Chapter10.Exercise22.Subdivision
open Set MeasureTheory Matrix
open Rudin.Support.SimplexIntegration
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def unitSquare : Set Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc 0 1

def lower : Plane →L[ℝ] Plane :=
  (Matrix.toEuclideanLin !![1,1;0,1]).toContinuousLinearMap

def upper : Plane →L[ℝ] Plane :=
  (Matrix.toEuclideanLin !![0,1;1,1]).toContinuousLinearMap

def lowerRegion : Set Plane := {x | 0 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 ≤ 1}
def upperRegion : Set Plane := {x | 0 ≤ x 0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ 1}

@[simp] theorem lower_zero (x : Plane) : lower x 0 = x 0 + x 1 := by
  change ( !![1,1;0,1] *ᵥ (fun i => x i)) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] theorem lower_one (x : Plane) : lower x 1 = x 1 := by
  change ( !![1,1;0,1] *ᵥ (fun i => x i)) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] theorem upper_zero (x : Plane) : upper x 0 = x 1 := by
  change ( !![0,1;1,1] *ᵥ (fun i => x i)) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
@[simp] theorem upper_one (x : Plane) : upper x 1 = x 0 + x 1 := by
  change ( !![0,1;1,1] *ᵥ (fun i => x i)) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lower_det : lower.det = 1 := by
  norm_num [lower, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin, Matrix.det_fin_two_of]
theorem upper_det : upper.det = -1 := by
  norm_num [upper, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin, Matrix.det_fin_two_of]

theorem lower_injective : Function.Injective lower := by
  intro x y h
  have h0 := congrArg (fun x : Plane => x 0) h
  have h1 := congrArg (fun x : Plane => x 1) h
  simp only [lower_zero, lower_one] at h0 h1
  ext i; fin_cases i <;> dsimp <;> linarith

theorem upper_injective : Function.Injective upper := by
  intro x y h
  have h0 := congrArg (fun x : Plane => x 0) h
  have h1 := congrArg (fun x : Plane => x 1) h
  simp only [upper_zero, upper_one] at h0 h1
  ext i; fin_cases i <;> dsimp <;> linarith

theorem mem_simplex (x : Plane) :
    x ∈ standardSimplex 2 ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  simp [standardSimplex, Fin.forall_fin_two, Fin.sum_univ_two, and_assoc]

theorem lower_image : lower '' standardSimplex 2 = lowerRegion := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases (mem_simplex u).mp hu with ⟨h0,h1,hs⟩
    simp only [lowerRegion, mem_ofPred_eq, lower_zero, lower_one]
    exact ⟨h1, by linarith, hs⟩
  · rintro ⟨h0,h1,hs⟩
    let u : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0-x 1,x 1]
    refine ⟨u, ?_, ?_⟩
    · rw [mem_simplex]
      change 0 ≤ x 0-x 1 ∧ 0 ≤ x 1 ∧ x 0-x 1+x 1 ≤ 1
      constructor
      · exact sub_nonneg.mpr h1
      exact ⟨h0, by linarith⟩
    · ext i; fin_cases i <;> simp [u]

theorem upper_image : upper '' standardSimplex 2 = upperRegion := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases (mem_simplex u).mp hu with ⟨h0,h1,hs⟩
    simp only [upperRegion, mem_ofPred_eq, upper_zero, upper_one]
    exact ⟨h1, by linarith, hs⟩
  · rintro ⟨h0,h1,hs⟩
    let u : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 1-x 0,x 0]
    refine ⟨u, ?_, ?_⟩
    · rw [mem_simplex]
      change 0 ≤ x 1-x 0 ∧ 0 ≤ x 0 ∧ x 1-x 0+x 0 ≤ 1
      constructor
      · exact sub_nonneg.mpr h1
      exact ⟨h0, by linarith⟩
    · ext i; fin_cases i <;> simp [u]

theorem regions_union : lowerRegion ∪ upperRegion = unitSquare := by
  ext x
  have hx : x ∈ unitSquare ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 ≤ 1 ∧ x 1 ≤ 1 := by
    simp [unitSquare, mem_Icc, Pi.le_def, Fin.forall_fin_two, and_assoc]
  rw [hx]
  change (0 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 ≤ 1) ∨
    (0 ≤ x 0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ 1) ↔ _
  constructor
  · rintro (⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩)
    · exact ⟨h0.trans h1,h0,h2,h1.trans h2⟩
    · exact ⟨h0,h0.trans h1,h1.trans h2,h2⟩
  · rintro ⟨h0,h1,h2,h3⟩
    rcases le_total (x 0) (x 1) with h | h
    · exact Or.inr ⟨h0,h,h3⟩
    · exact Or.inl ⟨h1,h,h2⟩

theorem lower_compact : IsCompact lowerRegion := by
  rw [← lower_image]
  exact (standardSimplex_isCompact 2).image lower.continuous

theorem upper_compact : IsCompact upperRegion := by
  rw [← upper_image]
  exact (standardSimplex_isCompact 2).image upper.continuous

theorem regions_aedisjoint : AEDisjoint volume lowerRegion upperRegion := by
  let L : Plane →ₗ[ℝ] ℝ :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) - EuclideanSpace.proj 1).toLinearMap
  have hL : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hm : (EuclideanSpace.single 0 1 : Plane) ∈ LinearMap.ker L := by
      rw [h]; trivial
    have hz := LinearMap.mem_ker.mp hm
    norm_num [L] at hz
  have hz := Measure.addHaar_submodule volume (LinearMap.ker L) hL
  apply measure_mono_null _ hz
  intro x hx
  change x 0 - x 1 = 0
  exact sub_eq_zero.mpr (le_antisymm hx.2.2.1 hx.1.2.1)

theorem lower_integral (f : Plane → ℝ) :
    (∫ x in lowerRegion, f x) = ∫ u in standardSimplex 2, f (lower u) := by
  rw [← lower_image, integral_image_eq_integral_abs_det_fderiv_smul volume
    (standardSimplex_isCompact 2).measurableSet
    (fun u _ => lower.hasFDerivAt.hasFDerivWithinAt) lower_injective.injOn]
  simp [lower_det]

theorem upper_integral (f : Plane → ℝ) :
    (∫ x in upperRegion, f x) = ∫ u in standardSimplex 2, f (upper u) := by
  rw [← upper_image, integral_image_eq_integral_abs_det_fderiv_smul volume
    (standardSimplex_isCompact 2).measurableSet
    (fun u _ => upper.hasFDerivAt.hasFDerivWithinAt) upper_injective.injOn]
  simp [upper_det]

/-- The source square is the sum of its two genuine triangle integrals.
The upper chart has determinant -1; the square chain also has coefficient -1. -/
theorem square_integral {f : Plane → ℝ} (hf : ContinuousOn f unitSquare) :
    (∫ u in standardSimplex 2, f (lower u)) +
      (∫ u in standardSimplex 2, f (upper u)) = ∫ x in unitSquare, f x := by
  have hl : lowerRegion ⊆ unitSquare := by
    rw [← regions_union]; exact subset_union_left
  have hu : upperRegion ⊆ unitSquare := by
    rw [← regions_union]; exact subset_union_right
  have hfi : IntegrableOn f lowerRegion := (hf.mono hl).integrableOn_compact lower_compact
  have hfj : IntegrableOn f upperRegion := (hf.mono hu).integrableOn_compact upper_compact
  rw [← lower_integral, ← upper_integral, ← regions_union]
  exact (setIntegral_union₀ regions_aedisjoint upper_compact.measurableSet.nullMeasurableSet
    hfi hfj).symm

end Rudin.Chapter10.Exercise22.Subdivision

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration
open Rudin.Support



def unitCube : Set Space := {q | ∀ i, q i ∈ Icc (0 : ℝ) 1}
def cubeAxis (i : Fin 3) : Space := EuclideanSpace.single i 1

def cubeTetra (p : Fin 6) : SmoothChains.Simplex 3 Space :=
  SmoothChains.affine (fun i => (EuclideanSpace.equiv (Fin 3) ℝ).symm (Exercise18.vertices p i))

/-- The actual smooth affine map agrees with the barycentric realization of E18. -/
theorem cubeTetra_realize (p : Fin 6) (u : Space) (hu : u ∈ standardSimplex 3) :
    (cubeTetra p).val u = (EuclideanSpace.equiv (Fin 3) ℝ).symm
      (Exercise18.tetrahedron p ⟨SmoothChains.weights u,
        (SmoothChains.mem_simplex_iff_weights u).mp hu, SmoothChains.sum_weights u⟩) := by
  ext j
  simp [cubeTetra, SmoothChains.affine, Exercise18.tetrahedron,
    OrientedChains.realize, map_sum, PiLp.smul_apply]

/-- Coverage includes all boundary ties, using the actual six E18 tetrahedra. -/
theorem cubeTetra_mem (p : Fin 6) : MapsTo (cubeTetra p).val (standardSimplex 3) unitCube := by
  intro u hu
  rw [cubeTetra_realize p u hu]
  exact (Exercise18.cube_coverage _).mp ⟨p, _, rfl⟩

theorem cube_eq_six : SmoothChains.cube (cubeAxis 0) (cubeAxis 1) (cubeAxis 2) =
    SmoothChains.simplex (cubeTetra 0) - SmoothChains.simplex (cubeTetra 1) - SmoothChains.simplex (cubeTetra 2) +
      SmoothChains.simplex (cubeTetra 3) + SmoothChains.simplex (cubeTetra 4) - SmoothChains.simplex (cubeTetra 5) := by
  have hv (p : Fin 6) : (fun i => (EuclideanSpace.equiv (Fin 3) ℝ).symm
      (Exercise18.vertices p i)) =
      ![0, cubeAxis (Exercise18.order p 0),
        cubeAxis (Exercise18.order p 0) + cubeAxis (Exercise18.order p 1),
        cubeAxis 0 + cubeAxis 1 + cubeAxis 2] := by
    ext i j
    fin_cases i <;> simp [Exercise18.vertices, Exercise18.e, cubeAxis, Pi.single_apply]
  simp only [cubeTetra, hv, SmoothChains.cube]
  norm_num [Exercise18.order]
  simp only [add_comm (cubeAxis 1) (cubeAxis 0), add_comm (cubeAxis 2) (cubeAxis 0),
    add_comm (cubeAxis 2) (cubeAxis 1)]

/-- The source cube as a chain whose six full images lie in the local domain. -/
def cubeInDomain {V : Set Space} (hV : unitCube ⊆ V) : SmoothChains.DomainChain 3 V :=
  let T := fun p => FreeAbelianGroup.of
    (⟨cubeTetra p, fun _ hu => hV (cubeTetra_mem p hu)⟩ : SmoothChains.InDomain 3 V)
  T 0 - T 1 - T 2 + T 3 + T 4 - T 5

theorem forget_cubeInDomain {V : Set Space} (hV : unitCube ⊆ V) :
    SmoothChains.forgetDomain 3 V (cubeInDomain hV) = SmoothChains.cube (cubeAxis 0) (cubeAxis 1) (cubeAxis 2) := by
  rw [cube_eq_six]
  simp [cubeInDomain, SmoothChains.forgetDomain, FreeAbelianGroup.map_of, SmoothChains.simplex]

/-- Stokes on the six actual local C² postcompositions, with no volume comparison. -/
theorem local_cube_closed (H : Space → Space) {V : Set Space}
    (hV : IsOpen V) (hCV : unitCube ⊆ V) (hH : ContDiffOn ℝ 2 H V)
    (himage : MapsTo H unitCube punctured) :
    SmoothChains.integral (pullback zeta H)
      (SmoothChains.boundary 2 (SmoothChains.cube (cubeAxis 0) (cubeAxis 1) (cubeAxis 2))) = 0 := by
  have hT (p : Fin 6) : SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex
      ((cubeTetra p).mapOn H V hV hH (fun _ hu => hCV (cubeTetra_mem p hu))))) = 0 := by
    let T := (cubeTetra p).mapOn H V hV hH (fun _ hu => hCV (cubeTetra_mem p hu))
    have him : T.val '' standardSimplex 3 ⊆ punctured := by
      rintro _ ⟨u, hu, rfl⟩
      exact himage (cubeTetra_mem p hu)
    rw [← SimplexStokes.smoothChains_stokes zeta T punctured_open zeta_smooth him,
      SmoothChains.integral_simplex, simplexIntegral]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    change extDeriv zeta (T.val u) _ = 0
    rw [zeta_closed (him (mem_image_of_mem _ hu))]
    rfl
  have hs : SmoothChains.integral zeta (SmoothChains.boundary 2
      (SmoothChains.mapOnChain 3 H V hV hH (cubeInDomain hCV))) = 0 := by
    simp only [cubeInDomain, map_add, map_sub]
    change (_ - _ - _ + _ + _ - _ : ℝ) = 0
    change SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) -
      SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) -
      SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) +
      SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) +
      SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) -
      SmoothChains.integral zeta (SmoothChains.boundary 2 (SmoothChains.simplex _)) = 0
    rw [hT, hT, hT, hT, hT, hT]
    ring
  rw [SmoothChains.boundary_mapOnChain] at hs
  have hn := SmoothChainIntegration.orientedIntegral_mapOnChain zeta H V hV hH
    (SmoothChains.domainBoundary 2 V (cubeInDomain hCV))
  change SmoothChains.integral zeta
    (SmoothChains.mapOnChain 2 H V hV hH (SmoothChains.domainBoundary 2 V (cubeInDomain hCV))) =
    SmoothChains.integral (pullback zeta H)
      (SmoothChains.forgetDomain 2 V (SmoothChains.domainBoundary 2 V (cubeInDomain hCV))) at hn
  rw [SmoothChains.forgetDomain_boundary, forget_cubeInDomain] at hn
  exact hn.symm.trans hs

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support

def squareAxis (i : Fin 2) : Parameter := EuclideanSpace.single i 1

def parameterSquare : SmoothChains.Chain 2 Parameter :=
  SmoothChains.square 0 (squareAxis 0) (squareAxis 0 + squareAxis 1) (squareAxis 1)

def cubeFace (r : ℝ) (i : Fin 3) (p : Parameter) : Space :=
  WithLp.toLp 2 (Fin.insertNth i r (WithLp.ofLp p))

theorem cubeFace_smooth (r : ℝ) (i : Fin 3) : ContDiff ℝ 2 (cubeFace r i) := by
  apply contDiff_euclidean.mpr
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa [cubeFace] using (contDiff_const : ContDiff ℝ 2 (fun _ : Parameter => r))
  · simpa [cubeFace] using (EuclideanSpace.proj k : Parameter →L[ℝ] ℝ).contDiff

theorem cubeFace_mem {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin 3) :
    MapsTo (cubeFace r i) unitSquare unitCube := by
  intro p hp j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa [cubeFace] using hr
  · simpa [cubeFace] using hp k

theorem cubeFace_affine (r : ℝ) (i : Fin 3) (v : Fin 3 → Parameter) :
    (SmoothChains.affine v).map (cubeFace r i) (cubeFace_smooth r i) =
      SmoothChains.affine (cubeFace r i ∘ v) := by
  apply Subtype.ext
  funext u
  ext j
  change cubeFace r i ((SmoothChains.affine v).val u) j = _
  simp only [SmoothChains.affine, Function.comp_def, map_sum]
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · have hw := SmoothChains.sum_weights u
    change (∑ x : Fin 3, SmoothChains.weights u x) = 1 at hw
    simp only [Fin.sum_univ_three] at hw
    simp [cubeFace, Fin.sum_univ_three, PiLp.smul_apply]
    linear_combination -r * hw
  · simp [cubeFace]

theorem map_parameterSquare (r : ℝ) (i : Fin 3) :
    SmoothChains.map 2 (cubeFace r i) (cubeFace_smooth r i) parameterSquare =
      SmoothChains.square (cubeFace r i 0) (cubeFace r i (squareAxis 0))
        (cubeFace r i (squareAxis 0 + squareAxis 1)) (cubeFace r i (squareAxis 1)) := by
  simp only [parameterSquare, SmoothChains.square, map_sub, SmoothChains.map_simplex,
    cubeFace_affine]
  rfl

/-- The six square restrictions are the twelve full-map boundary triangles. -/
theorem cube_boundary_faces :
    SmoothChains.boundary 2 (SmoothChains.cube (cubeAxis 0) (cubeAxis 1) (cubeAxis 2)) =
      (SmoothChains.map 2 (cubeFace 1 0) (cubeFace_smooth 1 0) parameterSquare -
       SmoothChains.map 2 (cubeFace 0 0) (cubeFace_smooth 0 0) parameterSquare) -
      (SmoothChains.map 2 (cubeFace 1 1) (cubeFace_smooth 1 1) parameterSquare -
       SmoothChains.map 2 (cubeFace 0 1) (cubeFace_smooth 0 1) parameterSquare) +
      (SmoothChains.map 2 (cubeFace 1 2) (cubeFace_smooth 1 2) parameterSquare -
       SmoothChains.map 2 (cubeFace 0 2) (cubeFace_smooth 0 2) parameterSquare) := by
  rw [SmoothChains.boundary_cube]
  simp only [map_parameterSquare]
  congr 3 <;> congr 1 <;> ext j <;> fin_cases j <;>
    norm_num [cubeFace, cubeAxis, squareAxis, Fin.insertNth, Fin.succAboveCases,
      Fin.cons, Fin.cases, Fin.induction, Pi.single_apply] <;> norm_num [Fin.induction.go]

theorem local_cube_closed_at (H : Space → Space)
    (hH : ∀ q ∈ unitCube, ContDiffAt ℝ 2 H q)
    (himage : MapsTo H unitCube punctured) :
    SmoothChains.integral (pullback zeta H)
      (SmoothChains.boundary 2 (SmoothChains.cube (cubeAxis 0) (cubeAxis 1) (cubeAxis 2))) = 0 := by
  let V := {q | ContDiffAt ℝ 2 H q}
  have hV : IsOpen V := isOpen_iff_mem_nhds.mpr
    (fun q (hq : ContDiffAt ℝ 2 H q) => hq.eventually (by norm_num))
  exact local_cube_closed H hV hH
    (fun q (hq : ContDiffAt ℝ 2 H q) => hq.contDiffWithinAt) himage

/-- The time-first curtain is the same general curtain with its coordinates exchanged. -/
def timeCurtain (ρ : Parameter → ℝ) (h : ℝ → Space) (p : Parameter) : Space :=
  ρ p • h (p 1)

theorem timeCurtain_pullback {ρ : Parameter → ℝ} {h : ℝ → Space} {p : Parameter}
    (hρ : DifferentiableAt ℝ ρ p) (hh : DifferentiableAt ℝ h (p 1))
    (hpos : 0 < ρ p) (hn : h (p 1) ≠ 0) :
    timeCurtain ρ h p ∈ punctured ∧
    pullback zeta (timeCurtain ρ h) p (EuclideanSpace.single · 1) = 0 := by
  refine ⟨smul_ne_zero (ne_of_gt hpos) hn, ?_⟩
  have hd := hρ.hasFDerivAt.smul (hh.hasFDerivAt.comp p
    (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).hasFDerivAt)
  change HasFDerivAt (timeCurtain ρ h) _ p at hd
  rw [pullback_apply]
  have hv : (fun i : Fin 2 =>
      fderiv ℝ (timeCurtain ρ h) p (EuclideanSpace.single i 1)) =
      ![fderiv ℝ ρ p (EuclideanSpace.single 0 1) • h (p 1),
        fderiv ℝ ρ p (EuclideanSpace.single 1 1) • h (p 1) + ρ p • deriv h (p 1)] := by
    rw [hd.fderiv]
    funext i; fin_cases i <;> simp [ContinuousLinearMap.smulRight_apply, add_comm]
  rw [hv, zeta_apply]
  have hz := radial_curtain_algebra (h (p 1)) (deriv h (p 1)) (ρ p)
    (fderiv ℝ ρ p (EuclideanSpace.single 1 1))
    (fderiv ℝ ρ p (EuclideanSpace.single 0 1))
  rw [zeta_apply] at hz
  simp only [timeCurtain, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul] at *
  convert congrArg Neg.neg hz using 1 <;> ring

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support

def tailParameter (q : Space) : Parameter := WithLp.toLp 2 ![q 1, q 2]

theorem tailParameter_smooth : ContDiff ℝ 2 tailParameter := by
  apply contDiff_euclidean.mpr
  intro i; fin_cases i <;> dsimp [tailParameter] <;> fun_prop

theorem tailParameter_mem {q : Space} (hq : q ∈ unitCube) : tailParameter q ∈ unitSquare := by
  intro i; fin_cases i
  · exact hq 1
  · exact hq 2

/-- The same radial homotopy for an arbitrary nonvanishing parameterized surface. -/
def surfaceHomotopy (S : Parameter → Space) (f : Parameter → ℝ) (q : Space) : Space :=
  (1 - q 0 + q 0 * f (tailParameter q)) • S (tailParameter q)

theorem surfaceHomotopy_smoothAt {S : Parameter → Space} {f : Parameter → ℝ} {q : Space}
    (hS : ContDiffAt ℝ 2 S (tailParameter q))
    (hf : ContDiffAt ℝ 2 f (tailParameter q)) :
    ContDiffAt ℝ 2 (surfaceHomotopy S f) q := by
  exact ((contDiffAt_const.sub (EuclideanSpace.proj 0).contDiff.contDiffAt).add
    ((EuclideanSpace.proj 0).contDiff.contDiffAt.mul
      (hf.comp q tailParameter_smooth.contDiffAt))).smul
        (hS.comp q tailParameter_smooth.contDiffAt)

theorem surfaceHomotopy_nonzero {S : Parameter → Space} {f : Parameter → ℝ} {q : Space}
    (hf : 0 < f (tailParameter q)) (hS : S (tailParameter q) ≠ 0)
    (ht : q 0 ∈ Icc (0 : ℝ) 1) : surfaceHomotopy S f q ∈ punctured :=
  smul_ne_zero (ne_of_gt (radial_interpolation_positive hf ht)) hS

/-- No alternative exactness identity is used to identify the literal homotopy. -/
theorem surfaceHomotopy_sigma (f : Parameter → ℝ) :
    surfaceHomotopy sigma f = radialHomotopy f := rfl

def sideParameter (r : ℝ) (i : Fin 2) (s : ℝ) : Parameter :=
  WithLp.toLp 2 (Fin.insertNth i r (fun _ : Fin 1 => s))

theorem sideParameter_smooth (r : ℝ) (i : Fin 2) : ContDiff ℝ 2 (sideParameter r i) := by
  apply contDiff_euclidean.mpr
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa [sideParameter] using (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => r))
  · simpa [sideParameter] using! (contDiff_id : ContDiff ℝ 2 (fun s : ℝ => s))

theorem sideParameter_mem {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (i : Fin 2) : sideParameter r i s ∈ unitSquare := by
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simpa [sideParameter] using hr
  · simpa [sideParameter] using hs

theorem homotopy_side_formula (S : Parameter → Space) (f : Parameter → ℝ)
    (r : ℝ) (i : Fin 2) :
    surfaceHomotopy S f ∘ cubeFace r i.succ =
      timeCurtain (fun p => 1 - p 0 + p 0 * f (sideParameter r i (p 1)))
        (S ∘ sideParameter r i) := by
  funext p
  have ht : tailParameter (cubeFace r i.succ p) = sideParameter r i (p 1) := by
    ext j; fin_cases i <;> fin_cases j <;>
      norm_num [tailParameter, cubeFace, sideParameter, Fin.insertNth, Fin.succAboveCases,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go]
  have h0 : cubeFace r i.succ p 0 = p 0 := by
    fin_cases i <;>
      norm_num [cubeFace, Fin.insertNth, Fin.succAboveCases]
  simp only [Function.comp_def, surfaceHomotopy, ht, h0, timeCurtain]

/-- Each of the four side faces is a nonseparable radial curtain, with zero actual coefficient. -/
theorem homotopy_side_zero {S : Parameter → Space} {f : Parameter → ℝ}
    (hS : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 S p)
    (hf : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 f p)
    (hpos : ∀ p ∈ unitSquare, 0 < f p)
    (hn : ∀ p ∈ unitSquare, S p ≠ 0)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin 2) {p : Parameter}
    (hp : p ∈ unitSquare) :
    (surfaceHomotopy S f ∘ cubeFace r i.succ) p ∈ punctured ∧
    pullback zeta (surfaceHomotopy S f ∘ cubeFace r i.succ) p
      (EuclideanSpace.single · 1) = 0 := by
  rw [homotopy_side_formula]
  have hm := sideParameter_mem hr (hp 1) i
  have hs : ContDiffAt ℝ 2 (sideParameter r i) (p 1) := (sideParameter_smooth r i).contDiffAt
  apply timeCurtain_pullback
  · apply ContDiffAt.differentiableAt (n := 2) _ (by norm_num)
    exact (contDiffAt_const.sub (EuclideanSpace.proj 0).contDiff.contDiffAt).add
      ((EuclideanSpace.proj 0).contDiff.contDiffAt.mul
        ((hf _ hm).comp p (hs.comp p
          (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).contDiff.contDiffAt)))
  · exact ((hS _ hm).comp (p 1) hs).differentiableAt (by norm_num)
  · exact radial_interpolation_positive (hpos _ hm) (hp 0)
  · exact hn _ hm

theorem homotopy_end_formula (S : Parameter → Space) (f : Parameter → ℝ) :
    surfaceHomotopy S f ∘ cubeFace 0 0 = S ∧
    surfaceHomotopy S f ∘ cubeFace 1 0 = (fun p => f p • S p) := by
  have ht (r : ℝ) (p : Parameter) : tailParameter (cubeFace r 0 p) = p := by
    ext j; fin_cases j <;> rfl
  constructor <;> funext p <;>
    simp only [Function.comp_apply, surfaceHomotopy, ht] <;>
    simp [cubeFace]

/-- Continuity and integrability follow from local C² and actual image avoidance. -/
theorem surface_coefficient_continuous {S : Parameter → Space} {E : Set Parameter}
    (hS : ∀ p ∈ E, ContDiffAt ℝ 2 S p) (hn : MapsTo S E punctured) :
    ContinuousOn (fun p => pullback zeta S p (EuclideanSpace.single · 1)) E := by
  intro p hp
  have hZ := (zeta_smooth _ (hn hp)).contDiffAt (punctured_open.mem_nhds (hn hp))
  exact ((SimplexStokes.pullback_contDiffAt hZ (hS p hp)).continuousAt.eval
    continuousAt_const).continuousWithinAt

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support.MultivariateRiemann Rudin.Support

def rectangle (a b : Fin 2 → ℝ) : Set Parameter :=
  (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' Icc a b

def rectangleLinear (a b : Fin 2 → ℝ) : Parameter →L[ℝ] Parameter :=
  ∑ i, (b i - a i) • (EuclideanSpace.proj i : Parameter →L[ℝ] ℝ).smulRight (squareAxis i)

def rectangleChart (a b : Fin 2 → ℝ) (p : Parameter) : Parameter :=
  WithLp.toLp 2 a + rectangleLinear a b p

@[simp] theorem rectangleLinear_apply (a b : Fin 2 → ℝ) (p : Parameter) (i : Fin 2) :
    rectangleLinear a b p i = (b i - a i) * p i := by
  fin_cases i <;> simp [rectangleLinear, Fin.sum_univ_two, squareAxis,
    ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, mul_comm]

@[simp] theorem rectangleChart_apply (a b : Fin 2 → ℝ) (p : Parameter) (i : Fin 2) :
    rectangleChart a b p i = a i + (b i - a i) * p i := by
  simp [rectangleChart]

theorem rectangleChart_smooth (a b : Fin 2 → ℝ) : ContDiff ℝ 2 (rectangleChart a b) :=
  contDiff_const.add (rectangleLinear a b).contDiff

theorem rectangleChart_hasFDerivAt (a b : Fin 2 → ℝ) (p : Parameter) :
    HasFDerivAt (rectangleChart a b) (rectangleLinear a b) p :=
  (rectangleLinear a b).hasFDerivAt.const_add _

theorem rectangleLinear_det (a b : Fin 2 → ℝ) :
    LinearMap.det (rectangleLinear a b).toLinearMap = (b 0 - a 0) * (b 1 - a 1) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_apply]

theorem rectangle_compact (a b : Fin 2 → ℝ) : IsCompact (rectangle a b) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

theorem rectangle_mem {a b : Fin 2 → ℝ} {p : Parameter} :
    p ∈ rectangle a b ↔ ∀ i, p i ∈ Icc (a i) (b i) := by
  simp [rectangle, Pi.le_def, forall_and]

theorem rectangleChart_mem {a b : Fin 2 → ℝ} (hab : a ≤ b) :
    MapsTo (rectangleChart a b) unitSquare (rectangle a b) := by
  intro p hp
  rw [rectangle_mem]
  intro i
  rw [rectangleChart_apply]
  have h := hp i
  have habi := hab i
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr habi) h.1,
    mul_nonneg (sub_nonneg.mpr habi) (sub_nonneg.mpr h.2)]

theorem rectangleChart_image {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) :
    rectangleChart a b '' unitSquare = rectangle a b := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact rectangleChart_mem (fun i => (hab i).le) hu
  intro p hp
  let u : Parameter := WithLp.toLp 2 (fun i => (p i - a i) / (b i - a i))
  have hd (i) : 0 < b i - a i := sub_pos.mpr (hab i)
  have hpi := rectangle_mem.mp hp
  refine ⟨u, ?_, ?_⟩
  · intro i
    change (p i - a i) / (b i - a i) ∈ Icc (0 : ℝ) 1
    exact ⟨div_nonneg (sub_nonneg.mpr (hpi i).1) (hd i).le,
      (div_le_one (hd i)).mpr (by linarith [(hpi i).2])⟩
  · ext i
    simp [u, mul_div_cancel₀ _ (ne_of_gt (hd i))]

theorem rectangleChart_injective {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) :
    Function.Injective (rectangleChart a b) := by
  intro p q he
  ext i
  have h := congrArg (fun z : Parameter => z i) he
  simp only [rectangleChart_apply] at h
  exact (mul_left_cancel₀ (ne_of_gt (sub_pos.mpr (hab i)))) (add_left_cancel h)

/-- The rectangle substitution is an analytic determinant comparison, not a definition. -/
theorem rectangle_integral_substitution {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    (g : Parameter → ℝ) :
    (∫ p in rectangle a b, g p) =
      (b 0 - a 0) * (b 1 - a 1) * ∫ p in unitSquare, g (rectangleChart a b p) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    unitSquare_compact.measurableSet
    (fun p _ => (rectangleChart_hasFDerivAt a b p).hasFDerivWithinAt)
    (rectangleChart_injective hab).injOn g
  rw [rectangleChart_image hab] at h
  simpa only [rectangleLinear_det, abs_of_pos (mul_pos (sub_pos.mpr (hab 0))
    (sub_pos.mpr (hab 1))), smul_eq_mul, integral_const_mul] using h

/-- Naturality plus the true Jacobian compares the two literal surface integrals. -/
theorem rectangle_surface_substitution {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i)
    {S : Parameter → Space} (hS : ∀ p ∈ rectangle a b, DifferentiableAt ℝ S p) :
    surfaceIntegral (S ∘ rectangleChart a b) unitSquare = surfaceIntegral S (rectangle a b) := by
  rw [surfaceIntegral, surfaceIntegral, rectangle_integral_substitution hab,
    ← integral_const_mul]
  apply setIntegral_congr_fun unitSquare_compact.measurableSet
  intro p hp
  dsimp only
  rw [pullback_comp zeta S (rectangleChart a b) p
    (hS _ (rectangleChart_mem (fun i => (hab i).le) hp))
    (rectangleChart_hasFDerivAt a b p).differentiableAt]
  rw [pullback_apply, (rectangleChart_hasFDerivAt a b p).fderiv]
  exact (SmoothChainIntegration.alternating_linear (pullback zeta S (rectangleChart a b p))
    (rectangleLinear a b)).trans (by rw [rectangleLinear_det])

theorem rectangle_degenerate {a b : Fin 2 → ℝ} (hab : a ≤ b)
    (hdeg : ¬ ∀ i, a i < b i) : volume (rectangle a b) = 0 := by
  push_neg at hdeg
  obtain ⟨i, hi⟩ := hdeg
  have he := le_antisymm (hab i) hi
  rw [rectangle, euclidean_box_volume]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [he]

/-- The prescribed homotopy with only its source rectangle rescaled to the unit cube. -/
def rectangleHomotopy (f : Parameter → ℝ) (a b : Fin 2 → ℝ) (q : Space) : Space :=
  let p := rectangleChart a b (tailParameter q)
  radialHomotopy f (WithLp.toLp 2 ![q 0, p 0, p 1])

theorem rectangleHomotopy_formula (f : Parameter → ℝ) (a b : Fin 2 → ℝ) :
    rectangleHomotopy f a b =
      surfaceHomotopy (sigma ∘ rectangleChart a b) (f ∘ rectangleChart a b) := by
  funext q
  have hp : (WithLp.toLp 2 ![(rectangleChart a b (tailParameter q)) 0,
      (rectangleChart a b (tailParameter q)) 1] : Parameter) =
      rectangleChart a b (tailParameter q) := by
    ext i; fin_cases i <;> rfl
  change (1 - q 0 + q 0 * f (WithLp.toLp 2
    ![(rectangleChart a b (tailParameter q)) 0, (rectangleChart a b (tailParameter q)) 1])) •
    sigma (WithLp.toLp 2 ![(rectangleChart a b (tailParameter q)) 0,
      (rectangleChart a b (tailParameter q)) 1]) = _
  rw [hp]
  rfl

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support

/-- The actual lower and upper triangles in the frozen square chain. -/
def parameterTriangle (upper : Bool) : SmoothChains.Simplex 2 Parameter :=
  SmoothChains.affine (if upper then ![0, squareAxis 1, squareAxis 0 + squareAxis 1]
    else ![0, squareAxis 0, squareAxis 0 + squareAxis 1])

def triangleLinear (upper : Bool) : Parameter →L[ℝ] Parameter :=
  (EuclideanSpace.proj 0 : Parameter →L[ℝ] ℝ).smulRight
      (if upper then squareAxis 1 else squareAxis 0) +
    (EuclideanSpace.proj 1 : Parameter →L[ℝ] ℝ).smulRight (squareAxis 0 + squareAxis 1)

theorem parameterTriangle_linear (upper : Bool) :
    (parameterTriangle upper).val = triangleLinear upper := by
  funext p
  rw [parameterTriangle, SmoothChains.affine_formula]
  cases upper <;> simp [Fin.sum_univ_two, triangleLinear, ContinuousLinearMap.smulRight_apply]

theorem triangleLinear_det (upper : Bool) :
    LinearMap.det (triangleLinear upper).toLinearMap = if upper then -1 else 1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  cases upper <;> simp [triangleLinear, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply, squareAxis]

/-- Actual pullback coefficients have the correct determinant signs. -/
theorem parameterTriangle_coefficient (ω : Form 2 Parameter) (upper : Bool) (p : Parameter) :
    simplexCoefficient ω (parameterTriangle upper).toSmooth p =
      (if upper then -1 else 1) * ω (triangleLinear upper p) (EuclideanSpace.single · 1) := by
  change pullback ω (parameterTriangle upper).val p (EuclideanSpace.single · 1) = _
  rw [parameterTriangle_linear, pullback_apply, (triangleLinear upper).fderiv,
    SmoothChainIntegration.alternating_linear, triangleLinear_det]

/-- The negative upper coefficient cancels the negative upper chain multiplicity. -/
theorem square_integral_coefficients (ω : Form 2 Parameter) :
    SmoothChains.integral ω parameterSquare =
      (∫ p in standardSimplex 2, ω (triangleLinear false p) (EuclideanSpace.single · 1)) +
      (∫ p in standardSimplex 2, ω (triangleLinear true p) (EuclideanSpace.single · 1)) := by
  change SmoothChains.integral ω (SmoothChains.simplex (parameterTriangle false) -
    SmoothChains.simplex (parameterTriangle true)) = _
  simp only [map_sub, SmoothChains.integral_simplex, simplexIntegral, parameterTriangle_coefficient,
    Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul, integral_neg, sub_neg_eq_add]

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support

theorem triangleLinear_lower : triangleLinear false = Subdivision.lower := by
  ext p i; fin_cases i <;>
    simp [triangleLinear, squareAxis, ContinuousLinearMap.smulRight_apply]

theorem triangleLinear_upper : triangleLinear true = Subdivision.upper := by
  ext p i; fin_cases i <;>
    simp [triangleLinear, squareAxis, ContinuousLinearMap.smulRight_apply]

/-- Analytic two-cell comparison: actual affine triangle coefficients sum to the cell integral. -/
theorem square_form_integral (ω : Form 2 Parameter)
    (hω : ContinuousOn (fun p => ω p (EuclideanSpace.single · 1)) unitSquare) :
    SmoothChains.integral ω parameterSquare =
      ∫ p in unitSquare, ω p (EuclideanSpace.single · 1) := by
  rw [square_integral_coefficients, triangleLinear_lower, triangleLinear_upper]
  have hu : unitSquare = Subdivision.unitSquare := unitSquare_coordinates
  rw [hu] at hω ⊢
  exact Subdivision.square_integral hω

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration Rudin.Support.MultivariateRiemann Rudin.Support

/-- Each boundary pair of actual triangle coefficients equals its analytic square integral. -/
theorem cube_face_integral (H : Space → Space)
    (hH : ∀ q ∈ unitCube, ContDiffAt ℝ 2 H q) (hn : MapsTo H unitCube punctured)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin 3) :
    SmoothChains.integral (pullback zeta H)
      (SmoothChains.map 2 (cubeFace r i) (cubeFace_smooth r i) parameterSquare) =
        surfaceIntegral (H ∘ cubeFace r i) unitSquare := by
  have hC (p) (hp : p ∈ unitSquare) : ContDiffAt ℝ 2 (H ∘ cubeFace r i) p :=
    (hH _ (cubeFace_mem hr i hp)).comp p (cubeFace_smooth r i).contDiffAt
  have hnc : MapsTo (H ∘ cubeFace r i) unitSquare punctured :=
    fun p hp => hn (cubeFace_mem hr i hp)
  have he (p) (hp : p ∈ unitSquare) :
      pullback (pullback zeta H) (cubeFace r i) p = pullback zeta (H ∘ cubeFace r i) p :=
    (pullback_comp zeta H (cubeFace r i) p
      ((hH _ (cubeFace_mem hr i hp)).differentiableAt (by norm_num))
      ((cubeFace_smooth r i).differentiable (by norm_num) p)).symm
  rw [SmoothChains.integral_map, square_form_integral]
  · apply setIntegral_congr_fun unitSquare_compact.measurableSet
    intro p hp
    exact congrArg (fun A => A (EuclideanSpace.single · 1)) (he p hp)
  · exact (surface_coefficient_continuous hC hnc).congr
      (fun p hp => congrArg (fun A => A (EuclideanSpace.single · 1)) (he p hp))

/-- Radial invariance on the unit square, derived by six-tetrahedron Stokes and the four curtains. -/
theorem radial_unit_from_stokes {S : Parameter → Space} {f : Parameter → ℝ}
    (hS : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 S p)
    (hf : ∀ p ∈ unitSquare, ContDiffAt ℝ 2 f p)
    (hpos : ∀ p ∈ unitSquare, 0 < f p) (hn : ∀ p ∈ unitSquare, S p ≠ 0)
    (H : Space → Space) (hdef : H = surfaceHomotopy S f) :
    surfaceIntegral (fun p => f p • S p) unitSquare = surfaceIntegral S unitSquare := by
  subst H
  let H := surfaceHomotopy S f
  have hH (q) (hq : q ∈ unitCube) : ContDiffAt ℝ 2 H q :=
    surfaceHomotopy_smoothAt (hS _ (tailParameter_mem hq)) (hf _ (tailParameter_mem hq))
  have him : MapsTo H unitCube punctured := fun q hq =>
    surfaceHomotopy_nonzero (hpos _ (tailParameter_mem hq)) (hn _ (tailParameter_mem hq)) (hq 0)
  have hs := local_cube_closed_at H hH him
  rw [cube_boundary_faces] at hs
  simp only [map_add, map_sub] at hs
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  rw [cube_face_integral H hH him h1 0, cube_face_integral H hH him h0 0,
    cube_face_integral H hH him h1 1, cube_face_integral H hH him h0 1,
    cube_face_integral H hH him h1 2, cube_face_integral H hH him h0 2] at hs
  have hside (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
      surfaceIntegral (H ∘ cubeFace r i.succ) unitSquare = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro p hp
    exact (homotopy_side_zero hS hf hpos hn hr i hp).2
  have hs11 : surfaceIntegral (H ∘ cubeFace 1 1) unitSquare = 0 := hside 1 h1 0
  have hs01 : surfaceIntegral (H ∘ cubeFace 0 1) unitSquare = 0 := hside 0 h0 0
  have hs12 : surfaceIntegral (H ∘ cubeFace 1 2) unitSquare = 0 := hside 1 h1 1
  have hs02 : surfaceIntegral (H ∘ cubeFace 0 2) unitSquare = 0 := hside 0 h0 1
  rw [hs11, hs01, hs12, hs02] at hs
  have hend := homotopy_end_formula S f
  change H ∘ cubeFace 0 0 = S ∧ H ∘ cubeFace 1 0 = _ at hend
  rw [hend.1, hend.2] at hs
  linarith

/-- The prescribed part (d), including degenerate rectangles and local C² source regularity. -/
theorem radial_area_from_stokes {f : Parameter → ℝ}
    (hf : ∀ q ∈ sphereDomain, ContDiffAt ℝ 2 f q)
    (hpos : ∀ q ∈ sphereDomain, 0 < f q) {a b : Fin 2 → ℝ} (hab : a ≤ b)
    (hD : rectangle a b ⊆ sphereDomain) :
    IntegrableOn (fun p => pullback zeta (radialSurface f) p (EuclideanSpace.single · 1))
      (rectangle a b) ∧
    surfaceIntegral (radialSurface f) (rectangle a b) = surfaceIntegral sigma (rectangle a b) ∧
    surfaceIntegral (radialSurface f) (rectangle a b) = area sigma (rectangle a b) := by
  have hR (p) (hp : p ∈ rectangle a b) : ContDiffAt ℝ 2 (radialSurface f) p :=
    (hf p (hD hp)).smul sigma_smooth.contDiffAt
  have hn : MapsTo (radialSurface f) (rectangle a b) punctured :=
    fun p hp => radialSurface_nonzero (hpos p (hD hp))
  have hi := (surface_coefficient_continuous hR hn).integrableOn_compact
    (μ := volume) (rectangle_compact a b)
  have he : surfaceIntegral (radialSurface f) (rectangle a b) =
      surfaceIntegral sigma (rectangle a b) := by
    by_cases hlt : ∀ i, a i < b i
    · have hSm (p) (hp : p ∈ unitSquare) :
          ContDiffAt ℝ 2 (sigma ∘ rectangleChart a b) p :=
        sigma_smooth.contDiffAt.comp p (rectangleChart_smooth a b).contDiffAt
      have hfm (p) (hp : p ∈ unitSquare) : ContDiffAt ℝ 2 (f ∘ rectangleChart a b) p :=
        (hf _ (hD (rectangleChart_mem hab hp))).comp p (rectangleChart_smooth a b).contDiffAt
      have hs := radial_unit_from_stokes hSm hfm
        (fun p hp => hpos _ (hD (rectangleChart_mem hab hp)))
        (fun p _ => sigma_ne_zero (rectangleChart a b p))
        (rectangleHomotopy f a b) (rectangleHomotopy_formula f a b)
      change surfaceIntegral (radialSurface f ∘ rectangleChart a b) unitSquare =
        surfaceIntegral (sigma ∘ rectangleChart a b) unitSquare at hs
      rw [rectangle_surface_substitution hlt (fun p hp => (hR p hp).differentiableAt (by norm_num)),
        rectangle_surface_substitution hlt (fun p _ => sigma_smooth.differentiable (by norm_num) p)] at hs
      exact hs
    · have hv := rectangle_degenerate hab hlt
      simp [surfaceIntegral, Measure.restrict_eq_zero.mpr hv]
  exact ⟨hi, he, he.trans (sphere_area (rectangle_compact a b) (fun p hp => (hD hp).1)).2.2.2⟩

/-- Source Darboux witnesses for part (d), without the independent primitive proof of part (f). -/
theorem radial_stokes_rectangle_source {f : Parameter → ℝ}
    (hf : ∀ q ∈ sphereDomain, ContDiffAt ℝ 2 f q)
    (hpos : ∀ q ∈ sphereDomain, 0 < f q) {a b : Fin 2 → ℝ} (hab : a ≤ b)
    (hD : rectangle a b ⊆ sphereDomain) (τ : Equiv.Perm (Fin 2)) :
    HasSourceIntegral 2 (a ∘ τ) (b ∘ τ)
      ((fun p => pullback zeta (radialSurface f) p (EuclideanSpace.single · 1)) ∘
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ∘ coordinatePermutation τ)
      (surfaceIntegral sigma (rectangle a b)) := by
  rw [← (radial_area_from_stokes hf hpos hab hD).2.1]
  apply euclidean_box_source hab
  apply surface_coefficient_continuous
  · exact fun p hp => (hf p (hD hp)).smul sigma_smooth.contDiffAt
  · exact fun p hp => radialSurface_nonzero (hpos p (hD hp))

end Rudin.Chapter10.Exercise22

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Rudin.Chapter10.Exercise22
open Set MeasureTheory
open Rudin.Support.SimplexIntegration

/-- A family of smooth, positive, genuinely nonseparable radial functions. -/
def nonseparableRadius (c : ℝ) (p : Parameter) : ℝ := 2 + c * p 0 * p 1

theorem nonseparableRadius_smooth (c : ℝ) : ContDiff ℝ 2 (nonseparableRadius c) := by
  unfold nonseparableRadius
  fun_prop

theorem nonseparableRadius_positive {c : ℝ} (hc : 0 ≤ c) {p : Parameter}
    (hp : p ∈ sphereDomain) : 0 < nonseparableRadius c p := by
  dsimp [nonseparableRadius]
  have h := mul_nonneg (mul_nonneg hc hp.1.1) hp.2.1
  linarith

/-- The radius cannot be written as a product of one-variable functions, even on the unit square. -/
theorem nonseparableRadius_not_product {c : ℝ} (hc : 0 < c) :
    ¬ ∃ g h : ℝ → ℝ, ∀ p ∈ unitSquare, nonseparableRadius c p = g (p 0) * h (p 1) := by
  rintro ⟨g, h, he⟩
  have hp (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
      (WithLp.toLp 2 ![u,v] : Parameter) ∈ unitSquare := by
    intro i; fin_cases i <;> assumption
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h00 := he _ (hp 0 0 h0 h0)
  have h01 := he _ (hp 0 1 h0 h1)
  have h10 := he _ (hp 1 0 h1 h0)
  have h11 := he _ (hp 1 1 h1 h1)
  simp [nonseparableRadius] at h00 h01 h10 h11
  have hx : (g 0 * h 0) * (g 1 * h 1) = (g 0 * h 1) * (g 1 * h 0) := by ring
  rw [← h00, ← h01, ← h10, ← h11] at hx
  nlinarith

theorem sphereDomain_rectangle : sphereDomain = rectangle ![0,0] ![Real.pi, 2 * Real.pi] := by
  ext p
  simp [rectangle_mem, sphereDomain, Fin.forall_fin_two]

/-- Every positive family parameter gives a nontrivial model of the prescribed Stokes proof. -/
theorem nonseparable_radial_stokes_models {c : ℝ} (hc : 0 < c) :
    surfaceIntegral (radialSurface (nonseparableRadius c)) sphereDomain =
      surfaceIntegral sigma sphereDomain ∧
    surfaceIntegral (radialSurface (nonseparableRadius c)) sphereDomain = area sigma sphereDomain ∧
    ¬ ∃ g h : ℝ → ℝ, ∀ p ∈ unitSquare,
      nonseparableRadius c p = g (p 0) * h (p 1) := by
  have hab : (![0,0] : Fin 2 → ℝ) ≤ ![Real.pi, 2 * Real.pi] := by
    intro i; fin_cases i <;> simp [Real.pi_pos.le]
  have hs := radial_area_from_stokes
    (fun p _ => (nonseparableRadius_smooth c).contDiffAt)
    (fun p hp => nonseparableRadius_positive hc.le hp) hab
    (by rw [← sphereDomain_rectangle])
  rw [← sphereDomain_rectangle] at hs
  exact ⟨hs.2.1, hs.2.2, nonseparableRadius_not_product hc⟩

/-- The literal interior homotopy is nonconstant; no zero-map model can pass this check. -/
theorem nonseparable_homotopy_model (c : ℝ) :
    radialHomotopy (nonseparableRadius c) (WithLp.toLp 2 ![1/2,1,1]) =
      (3/2 + c/2) • sigma (WithLp.toLp 2 ![1,1]) := by
  simp [radialHomotopy, nonseparableRadius]
  congr 1
  ring

end Rudin.Chapter10.Exercise22
