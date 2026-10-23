module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

/-! # The exponential map of the real Euclidean plane

The complex plane supplies the Euclidean norm. Real and imaginary coordinates
are stated explicitly; derivatives below are real Fréchet derivatives.
-/

@[expose] public section

open Set Filter
open scoped Topology Matrix

namespace Rudin.Chapter09

noncomputable def exercise17F (z : ℂ) : ℂ := Complex.exp z
noncomputable def exercise17G (z : ℂ) : ℂ := Complex.log z

/-- The literal two real coordinate functions in the source. -/
theorem exercise17_coordinates (z : ℂ) :
    (exercise17F z).re = Real.exp z.re * Real.cos z.im ∧
    (exercise17F z).im = Real.exp z.re * Real.sin z.im :=
  ⟨Complex.exp_re z, Complex.exp_im z⟩

/-- Complex norm is the source Euclidean norm, not the product maximum norm. -/
theorem exercise17_euclidean_norm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq_apply, pow_two] using Complex.sq_norm z

theorem exercise17_range : range exercise17F = {0}ᶜ := by
  ext z
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩; exact Complex.exp_ne_zero w
  · intro hz; exact ⟨Complex.log z, Complex.exp_log hz⟩

noncomputable def exercise17D (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) (exercise17F z)

theorem exercise17_hasFDerivAt (z : ℂ) :
    HasFDerivAt exercise17F (exercise17D z) z := by
  have h := (Complex.hasDerivAt_exp z).hasFDerivAt.restrictScalars ℝ
  have he : exercise17D z =
      (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp z)).restrictScalars ℝ := by
    ext w
    simp [exercise17D, exercise17F, mul_comm]
  rw [he]
  exact h

noncomputable def exercise17Jacobian (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(exercise17F z).re, -(exercise17F z).im;
     (exercise17F z).im, (exercise17F z).re]

/-- This matrix acts on the actual real Fréchet derivative's coordinates. -/
theorem exercise17_matrix_action (z w : ℂ) :
    exercise17Jacobian z *ᵥ ![w.re, w.im] =
      ![(exercise17D z w).re, (exercise17D z w).im] := by
  ext i
  fin_cases i <;> simp [exercise17Jacobian, exercise17D, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem exercise17_jacobian (z : ℂ) :
    (exercise17Jacobian z).det = Real.exp (2 * z.re) := by
  rw [exercise17Jacobian, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hn := exercise17_euclidean_norm (exercise17F z)
  rw [exercise17F, Complex.norm_exp] at hn
  change (Complex.exp z).re * (Complex.exp z).re -
    -(Complex.exp z).im * (Complex.exp z).im = _
  rw [show 2 * z.re = z.re + z.re by ring, Real.exp_add]
  nlinarith

theorem exercise17_jacobian_ne_zero (z : ℂ) : (exercise17Jacobian z).det ≠ 0 := by
  rw [exercise17_jacobian]; exact (Real.exp_pos _).ne'

theorem exercise17_locally_injective (z : ℂ) :
    ∃ s ∈ 𝓝 z, InjOn exercise17F s := by
  have h := (Complex.hasStrictDerivAt_exp z).eventually_left_inverse (Complex.exp_ne_zero z)
  refine ⟨{w | (Complex.hasStrictDerivAt_exp z).localInverse Complex.exp
    (Complex.exp z) z (Complex.exp_ne_zero z) (Complex.exp w) = w}, h, ?_⟩
  intro u hu v hv huv
  change Complex.exp u = Complex.exp v at huv
  rw [← hu, ← hv, huv]

theorem exercise17_not_injective : ¬Function.Injective exercise17F := by
  intro h
  have he : exercise17F 0 = exercise17F (2 * Real.pi * Complex.I) := by
    simp [exercise17F, Complex.exp_two_pi_mul_I]
  have hz := congrArg Complex.im (h he)
  norm_num [Complex.mul_im] at hz

noncomputable def exercise17A : ℂ := (Real.pi / 3 : ℝ) * Complex.I
noncomputable def exercise17B : ℂ := exercise17F exercise17A

theorem exercise17_b_value : exercise17B = (1 / 2 : ℝ) +
    (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [exercise17B, exercise17A, exercise17F,
    Complex.exp_re, Complex.exp_im, Real.cos_pi_div_three, Real.sin_pi_div_three]

theorem exercise17_a_strip : exercise17A.im ∈ Ioo (-Real.pi) Real.pi := by
  simp only [exercise17A, Complex.mul_I_im, Complex.ofReal_re, mem_Ioo]
  constructor <;> linarith [Real.pi_pos]

theorem exercise17_inverse_value : exercise17G exercise17B = exercise17A :=
  Complex.log_exp exercise17_a_strip.1 exercise17_a_strip.2.le

/-- The explicit branch is log of the norm plus the principal angle. -/
theorem exercise17_inverse_formula (z : ℂ) :
    exercise17G z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I := rfl

theorem exercise17_inverse_branch :
    ∃ (u v : Set ℂ), IsOpen u ∧ IsOpen v ∧ exercise17A ∈ u ∧ exercise17B ∈ v ∧
      MapsTo exercise17F u v ∧ MapsTo exercise17G v u ∧
      (∀ z ∈ u, exercise17G (exercise17F z) = z) ∧
      (∀ z ∈ v, exercise17F (exercise17G z) = z) ∧ ContinuousOn exercise17G v := by
  let e := Complex.expOpenPartialHomeomorph
  refine ⟨e.source, e.target, e.open_source, e.open_target, exercise17_a_strip,
    e.map_source exercise17_a_strip, e.map_source', e.map_target',
    e.left_inv', e.right_inv', e.continuousOn_invFun⟩

/-- The complete image of each horizontal coordinate line is an open ray. -/
theorem exercise17_horizontal_image (c : ℝ) :
    range (fun x : ℝ ↦ exercise17F ((x : ℂ) + c * Complex.I)) =
      {w | ∃ r : ℝ, 0 < r ∧ w = (r : ℂ) * Complex.exp (c * Complex.I)} := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Real.exp x, Real.exp_pos x, by simp [exercise17F, Complex.exp_add]⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨Real.log r, ?_⟩
    simp [exercise17F, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

/-- The complete image of each vertical coordinate line is a circle. -/
theorem exercise17_vertical_image (c : ℝ) :
    range (fun y : ℝ ↦ exercise17F ((c : ℂ) + y * Complex.I)) =
      {w | ‖w‖ = Real.exp c} := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    simp [exercise17F, Complex.norm_exp]
  · intro hw
    change ‖w‖ = Real.exp c at hw
    have hn : w ≠ 0 := by
      intro hz
      simp only [hz, norm_zero] at hw
      exact (Real.exp_ne_zero c) hw.symm
    refine ⟨Complex.arg w, ?_⟩
    have he : (c : ℂ) + (Complex.arg w : ℂ) * Complex.I = Complex.log w := by
      rw [Complex.log, hw, Real.log_exp]
    change exercise17F ((c : ℂ) + (Complex.arg w : ℂ) * Complex.I) = w
    rw [he, exercise17F, Complex.exp_log hn]

noncomputable def exercise17ForwardMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, -(Real.sqrt 3 / 2); Real.sqrt 3 / 2, 1 / 2]
noncomputable def exercise17InverseMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, Real.sqrt 3 / 2; -(Real.sqrt 3 / 2), 1 / 2]

theorem exercise17_forward_matrix : exercise17Jacobian exercise17A =
    exercise17ForwardMatrix := by
  rw [exercise17Jacobian, ← exercise17B, exercise17_b_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exercise17ForwardMatrix, Complex.add_re, Complex.add_im]

theorem exercise17_b_inverse : exercise17B⁻¹ =
    (1 / 2 : ℝ) - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  rw [exercise17_b_value]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · ring

noncomputable def exercise17InverseD : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) exercise17B⁻¹

theorem exercise17_inverse_hasFDerivAt :
    HasFDerivAt exercise17G exercise17InverseD exercise17B := by
  have hb : exercise17B ∈ Complex.slitPlane :=
    Complex.expOpenPartialHomeomorph.map_source exercise17_a_strip
  have he : exercise17InverseD =
      (ContinuousLinearMap.toSpanSingleton ℂ exercise17B⁻¹).restrictScalars ℝ := by
    ext w
    simp [exercise17InverseD, mul_comm]
  rw [he]
  exact (Complex.hasDerivAt_log hb).hasFDerivAt.restrictScalars ℝ

theorem exercise17_inverse_matrix_action (w : ℂ) :
    exercise17InverseMatrix *ᵥ ![w.re, w.im] =
      ![(exercise17InverseD w).re, (exercise17InverseD w).im] := by
  ext i
  fin_cases i <;> simp [exercise17InverseMatrix, exercise17InverseD, exercise17_b_inverse,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

/-- Both products are the identity, explicitly verifying the inverse formula. -/
theorem exercise17_inverse_identity :
    exercise17InverseMatrix * exercise17ForwardMatrix = 1 ∧
      exercise17ForwardMatrix * exercise17InverseMatrix = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [exercise17ForwardMatrix, exercise17InverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] <;> nlinarith

theorem exercise17_inverse_eq_matrix_inv :
    exercise17InverseMatrix = exercise17ForwardMatrix⁻¹ :=
  Matrix.inv_eq_left_inv exercise17_inverse_identity.1 |>.symm

end Rudin.Chapter09
