module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Math.Rudin.Support.MultivariateRiemann

/-! # Exercise 10.8: an affine parallelogram -/
@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise08
open Set MeasureTheory

/-- The parallelogram based at `(1,1)` with edge vectors `(2,1)` and `(1,3)`. -/
def parallelogram : Set (ℝ × ℝ) :=
  {p | ∃ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1,
    p = (1,1) + u • (2,1) + v • (1,3)}

def square : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

def transform (p : ℝ × ℝ) : ℝ × ℝ := (1 + 2*p.1 + p.2, 1 + p.1 + 3*p.2)

theorem vertices : transform (0,0) = (1,1) ∧ transform (1,0) = (3,2) ∧
    transform (0,1) = (2,4) ∧ transform (1,1) = (4,5) := by
  norm_num [transform]

theorem image_square : transform '' square = parallelogram := by
  ext p
  constructor
  · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩, rfl⟩
    exact ⟨u, hu, v, hv, by ext <;> simp [transform] <;> ring⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨(u,v), ⟨hu,hv⟩, by ext <;> simp [transform] <;> ring⟩

/-- The linear part of the affine map. -/
def linearPart : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) !![2,1;1,3]).toContinuousLinearMap

theorem affine_formula (p : ℝ × ℝ) : transform p = (1,1) + linearPart p := by
  simp [transform, linearPart, Matrix.toLin_finTwoProd_toContinuousLinearMap, add_assoc]

theorem hasFDerivAt_transform (p : ℝ × ℝ) : HasFDerivAt transform linearPart p := by
  simpa only [← affine_formula] using linearPart.hasFDerivAt.const_add (1,1)

theorem jacobian : linearPart.det = 5 := by
  norm_num [linearPart, LinearMap.det_toLin, Matrix.det_fin_two_of]

theorem injective : Function.Injective transform := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [transform] at h₁ h₂
  ext <;> linarith

theorem integrand_transform (p : ℝ × ℝ) :
    Real.exp ((transform p).1 - (transform p).2) = Real.exp (p.1 - 2*p.2) := by
  congr 1
  simp [transform]
  ring

/-- The substitution theorem is applied to the actual image of the square. -/
theorem transformed_integral :
    (∫ p in parallelogram, Real.exp (p.1-p.2)) =
      ∫ p in square, 5 * Real.exp (p.1-2*p.2) := by
  rw [← image_square]
  unfold square
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_Icc.prod measurableSet_Icc)
    (fun p _ => (hasFDerivAt_transform p).hasFDerivWithinAt) injective.injOn]
  simp [jacobian, smul_eq_mul, integrand_transform]

/-- Compactness supplies integrability independently of the substitution. -/
theorem integrable_integrand :
    IntegrableOn (fun p : ℝ × ℝ => Real.exp (p.1-p.2)) parallelogram := by
  have hc : Continuous transform := continuous_iff_continuousAt.mpr
    (fun p => (hasFDerivAt_transform p).continuousAt)
  have hk : IsCompact parallelogram := by
    rw [← image_square]
    exact (isCompact_Icc.prod isCompact_Icc).image hc
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.exp (p.1-p.2))).continuousOn.integrableOn_compact hk

theorem square_integral_value :
    (∫ p in square, 5 * Real.exp (p.1-2*p.2)) =
      5 / 2 * (Real.exp 1 - 1) * (1 - Real.exp (-2)) := by
  have he : (fun p : ℝ × ℝ => Real.exp (p.1-2*p.2)) =
      (fun p => Real.exp p.1 * Real.exp (-2*p.2)) := by
    funext p
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_const_mul, he]
  unfold square
  rw [Measure.volume_eq_prod, setIntegral_prod_mul Real.exp (fun y : ℝ => Real.exp (-2*y))]
  simp_rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rw [integral_exp, intervalIntegral.integral_comp_mul_left _ (by norm_num : (-2:ℝ) ≠ 0)]
  simp [integral_exp]
  ring

theorem integral_value :
    (∫ p in parallelogram, Real.exp (p.1-p.2)) =
      5 / 2 * (Real.exp 1 - 1) * (1 - Real.exp (-2)) := by
  rw [transformed_integral, square_integral_value]

open Rudin.Support.MultivariateRiemann

/-- The transformed square integral has the literal repeated Darboux value. -/
theorem transformed_source :
    HasSourceIntegral 2 0 1 (fun u => 5 * Real.exp (u 0 - 2*u 1))
      (5 / 2 * (Real.exp 1 - 1) * (1 - Real.exp (-2))) := by
  have h := source_of_continuous (n := 2) (a := 0) (b := 1)
    (by intro i; norm_num : (0 : Fin 2 → ℝ) ≤ 1)
    (by fun_prop : Continuous (fun u : Fin 2 → ℝ => 5 * Real.exp (u 0 - 2*u 1)))
  have he : (fun u : Fin 2 → ℝ => 5 * Real.exp (u 0 - 2*u 1)) =
      (fun u => 5 * Real.exp (u 0) * Real.exp (-2*u 1)) := by
    funext u
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hv : iterated 2 0 1 (fun u => 5 * Real.exp (u 0 - 2*u 1)) =
      5 / 2 * (Real.exp 1 - 1) * (1 - Real.exp (-2)) := by
    rw [he]
    change (∫ v in (0:ℝ)..1, ∫ u in (0:ℝ)..1,
      5 * Real.exp u * Real.exp (-2*v)) = _
    simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_exp]
    rw [intervalIntegral.integral_comp_mul_left _ (by norm_num : (-2:ℝ) ≠ 0)]
    simp [integral_exp]
    ring
  rwa [hv] at h

end Rudin.Chapter10.Exercise08
