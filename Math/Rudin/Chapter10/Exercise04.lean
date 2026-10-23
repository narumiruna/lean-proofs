module

public import Math.Rudin.Chapter10.Exercise03
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section
noncomputable section
namespace Rudin.Chapter10
open Set Real
open scoped Topology ContDiff

abbrev Plane := Fin 2 → ℝ

def exercise04_F (x : Plane) : Plane :=
  ![exp (x 0) * cos (x 1) - 1, exp (x 0) * sin (x 1)]
def exercise04_G1 (x : Plane) : Plane := ![exp (x 0) * cos (x 1) - 1, x 1]
def exercise04_G2 (x : Plane) : Plane := ![x 0, (1 + x 0) * tan (x 1)]
def exercise04_H2 (x : Plane) : Plane := ![x 0, exp (x 0) * sin (x 1)]
/-- The positive square-root branch is forced near zero. -/
def exercise04_H1 (x : Plane) : Plane := ![sqrt (exp (2 * x 0) - (x 1)^2) - 1, x 1]

/-- The common source strip; the intermediate G1 image has the same second coordinate. -/
def exercise04_U : Set Plane := {x | x 1 ∈ Ioo (-(π/2)) (π/2)}
/-- The open domain of the square-root factor. -/
def exercise04_V : Set Plane := {x | 0 < exp (2 * x 0) - (x 1)^2}

theorem exercise04_domains : IsOpen exercise04_U ∧ (0 : Plane) ∈ exercise04_U ∧
    IsOpen exercise04_V ∧ (0 : Plane) ∈ exercise04_V := by
  refine ⟨isOpen_Ioo.preimage (continuous_apply 1), ?_, ?_, ?_⟩
  · simp [exercise04_U, Real.pi_pos]
  · exact isOpen_lt continuous_const (by fun_prop)
  · norm_num [exercise04_V]

theorem exercise04_primitive_maps : PrimitiveOn exercise04_U exercise04_G1 ∧
    PrimitiveOn exercise04_U exercise04_G2 ∧ PrimitiveOn exercise04_U exercise04_H2 ∧
    PrimitiveOn exercise04_V exercise04_H1 := by
  obtain ⟨hU, _, hV, _⟩ := exercise04_domains
  refine ⟨⟨hU, 0, ?_⟩, ⟨hU, 1, ?_⟩, ⟨hU, 1, ?_⟩, ⟨hV, 0, ?_⟩⟩ <;>
    intro x hx j hj <;> fin_cases j <;>
    simp_all [exercise04_G1, exercise04_G2, exercise04_H2, exercise04_H1]

theorem exercise04_smooth : ContDiff ℝ ∞ exercise04_F ∧ ContDiff ℝ ∞ exercise04_G1 ∧
    ContDiff ℝ ∞ exercise04_H2 ∧ ContDiffOn ℝ ∞ exercise04_G2 exercise04_U ∧
    ContDiffOn ℝ ∞ exercise04_H1 exercise04_V := by
  have hf : ContDiff ℝ ∞ exercise04_F := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [exercise04_F] <;> fun_prop
  have hg : ContDiff ℝ ∞ exercise04_G1 := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [exercise04_G1] <;> fun_prop
  have hh : ContDiff ℝ ∞ exercise04_H2 := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [exercise04_H2] <;> fun_prop
  refine ⟨hf, hg, hh, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro j
    fin_cases j
    · exact contDiffAt_pi.mp contDiffAt_id 0
    · change ContDiffAt ℝ ∞ (fun y : Plane => (1 + y 0) * tan (y 1)) x
      apply ContDiffAt.mul (by fun_prop)
      have ht : ContDiffAt ℝ ∞ Real.tan (x 1) :=
        Real.contDiffAt_tan.mpr (cos_pos_of_mem_Ioo hx).ne'
      exact ContDiffAt.comp x (f := fun y : Plane => y 1) (g := Real.tan) ht (by fun_prop)
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro j
    fin_cases j
    · change ContDiffAt ℝ ∞ (fun y : Plane => sqrt (exp (2*y 0) - (y 1)^2) - 1) x
      apply ContDiffAt.sub _ contDiffAt_const
      exact (show ContDiffAt ℝ ∞ (fun y : Plane => exp (2*y 0) - (y 1)^2) x by
        fun_prop).sqrt (ne_of_gt hx)
    · exact contDiffAt_pi.mp contDiffAt_id 1

theorem exercise04_first_factorization : MapsTo exercise04_G1 exercise04_U exercise04_U ∧
    EqOn exercise04_F (exercise04_G2 ∘ exercise04_G1) exercise04_U := by
  refine ⟨fun x hx => hx, ?_⟩
  intro x hx
  have hc := (cos_pos_of_mem_Ioo hx).ne'
  ext j
  fin_cases j
  · rfl
  · simp [exercise04_F, exercise04_G1, exercise04_G2, Real.tan_eq_sin_div_cos]
    field_simp

theorem exercise04_radical (x : Plane) :
    exp (2*x 0) - (exp (x 0) * sin (x 1))^2 = (exp (x 0) * cos (x 1))^2 := by
  have he : exp (2*x 0) = exp (x 0)^2 := by rw [two_mul, exp_add, pow_two]
  rw [he]
  nlinarith [sin_sq_add_cos_sq (x 1)]

theorem exercise04_alternative_factor : MapsTo exercise04_H2 exercise04_U exercise04_V ∧
    EqOn exercise04_F (exercise04_H1 ∘ exercise04_H2) exercise04_U := by
  have hp (x : Plane) (hx : x ∈ exercise04_U) : 0 < exp (x 0) * cos (x 1) :=
    mul_pos (exp_pos _) (cos_pos_of_mem_Ioo hx)
  constructor
  · intro x hx
    change 0 < exp (2*x 0) - (exp (x 0)*sin (x 1))^2
    rw [exercise04_radical]
    exact sq_pos_of_pos (hp x hx)
  · intro x hx
    ext j
    fin_cases j
    · change exp (x 0)*cos (x 1)-1 = sqrt (exp (2*x 0) - (exp (x 0)*sin (x 1))^2)-1
      rw [exercise04_radical, Real.sqrt_sq (hp x hx).le]
    · rfl

/-- Actual Frechet derivatives, rather than values of a total derivative at a
point where differentiability has not been established. -/
theorem exercise04_derivatives :
    HasFDerivAt exercise04_F (ContinuousLinearMap.id ℝ Plane) 0 ∧
    HasFDerivAt exercise04_G1 (ContinuousLinearMap.id ℝ Plane) 0 ∧
    HasFDerivAt exercise04_G2 (ContinuousLinearMap.id ℝ Plane) 0 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Plane)
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Plane)
  have he := (Real.hasDerivAt_exp 0).comp_hasFDerivAt (0 : Plane) h0
  have hc := (Real.hasDerivAt_cos 0).comp_hasFDerivAt (0 : Plane) h1
  have hs := (Real.hasDerivAt_sin 0).comp_hasFDerivAt (0 : Plane) h1
  have ht := (Real.hasDerivAt_tan (x := 0) (by simp)).comp_hasFDerivAt (0 : Plane) h1
  have hfirst : HasFDerivAt (𝕜 := ℝ) (fun x : Plane => exp (x 0)*cos (x 1)-1)
      (ContinuousLinearMap.proj 0) 0 := by
    convert (he.mul hc).sub_const 1 using 1 <;> simp
  have hsecond : HasFDerivAt (𝕜 := ℝ) (fun x : Plane => exp (x 0)*sin (x 1))
      (ContinuousLinearMap.proj 1) 0 := by
    convert he.mul hs using 1 <;> first | rfl | simp
  have htan : HasFDerivAt (𝕜 := ℝ) (fun x : Plane => (1+x 0)*tan (x 1))
      (ContinuousLinearMap.proj 1) 0 := by
    convert (h0.const_add 1).mul ht using 1 <;> first | rfl | simp
  refine ⟨?_, ?_, ?_⟩ <;> apply hasFDerivAt_pi'' <;> intro j <;> fin_cases j
  · simpa [exercise04_F] using hfirst
  · simpa [exercise04_F] using hsecond
  · simpa [exercise04_G1] using hfirst
  · simpa [exercise04_G1] using h1
  · simpa [exercise04_G2] using h0
  · simpa [exercise04_G2] using htan

/-- The three Jacobians are the determinants of the actual Frechet derivatives. -/
theorem exercise04_jacobians :
    LinearMap.det (fderiv ℝ exercise04_G1 0).toLinearMap = 1 ∧
    LinearMap.det (fderiv ℝ exercise04_G2 0).toLinearMap = 1 ∧
    LinearMap.det (fderiv ℝ exercise04_F 0).toLinearMap = 1 := by
  obtain ⟨hf,hg,hh⟩ := exercise04_derivatives
  rw [hf.fderiv, hg.fderiv, hh.fderiv]
  simp

end Rudin.Chapter10
