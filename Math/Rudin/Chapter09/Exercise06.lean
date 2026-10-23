module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

/-!
# R09E06: partial derivatives without continuity

Source: Rudin, Exercise 9.6, book page 239 (PDF page 248), and the
partial-derivative definition in Section 9.16, book page 215.
The domain has the actual Euclidean norm. Real division at zero makes the
quotient formula equal to zero at the origin, as required by the source.
The derivative theorems assert `HasDerivAt`, not merely a value of the total
`deriv` operator. The coordinate-line theorem uses the source's parametrization
`p + t eⱼ`. Discontinuity follows by restriction to the diagonal.
-/

@[expose] public section

namespace Rudin.Chapter09

open Filter Topology

/-- A point of the Euclidean plane with coordinates `x` and `y`. -/
def exercise06Point (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x, y]

/-- Rudin's function, with the prescribed value at the origin. -/
noncomputable def exercise06Function (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 * p 1 / ((p 0) ^ 2 + (p 1) ^ 2)

@[simp] theorem exercise06Point_zero : exercise06Point 0 0 = 0 := by
  ext i
  fin_cases i <;> rfl

/-- The definition has exactly the stated value at zero. -/
@[simp] theorem exercise06Function_zero : exercise06Function 0 = 0 := by
  simp [exercise06Function]

/-- The first partial derivative exists everywhere, including the origin. -/
theorem exercise06_partial_one (x y : ℝ) :
    HasDerivAt (fun t => exercise06Function (exercise06Point t y))
      (y * (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) x := by
  change HasDerivAt (fun t => t * y / (t ^ 2 + y ^ 2)) _ x
  by_cases hy : y = 0
  · subst y
    simpa using hasDerivAt_const x (0 : ℝ)
  · have hd : x ^ 2 + y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg x, sq_pos_of_ne_zero hy]
    convert ((hasDerivAt_id x).mul_const y).div
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2)) hd using 1
    · ext t
      simp only [Pi.div_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq]
      ring

/-- The second partial derivative exists everywhere, including the origin. -/
theorem exercise06_partial_two (x y : ℝ) :
    HasDerivAt (fun t => exercise06Function (exercise06Point x t))
      (x * (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2) y := by
  change HasDerivAt (fun t => x * t / (x ^ 2 + t ^ 2)) _ y
  by_cases hx : x = 0
  · subst x
    simpa using hasDerivAt_const y (0 : ℝ)
  · have hd : x ^ 2 + y ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg y, sq_pos_of_ne_zero hx]
    convert ((hasDerivAt_id y).const_mul x).div
      (((hasDerivAt_id y).pow 2).const_add (x ^ 2)) hd using 1
    · ext t
      simp only [Pi.div_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.pow_apply, id_eq]
      ring

/-- Both coordinate partials exist at every Euclidean point, in the source's form. -/
theorem exercise06_partials (p : EuclideanSpace ℝ (Fin 2)) (j : Fin 2) :
    ∃ d : ℝ, HasDerivAt
      (fun t : ℝ => exercise06Function (p + t • EuclideanSpace.single j 1)) d 0 := by
  fin_cases j
  · have h := (exercise06_partial_one (p 0) (p 1)).comp_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (p 0)) (by simp)
    refine ⟨p 1 * ((p 1) ^ 2 - (p 0) ^ 2) / ((p 0) ^ 2 + (p 1) ^ 2) ^ 2, ?_⟩
    convert h using 1
    · funext t
      congr 1
      ext i
      fin_cases i <;> simp [exercise06Point]
    · simp
  · have h := (exercise06_partial_two (p 0) (p 1)).comp_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (p 1)) (by simp)
    refine ⟨p 0 * ((p 0) ^ 2 - (p 1) ^ 2) / ((p 0) ^ 2 + (p 1) ^ 2) ^ 2, ?_⟩
    convert h using 1
    · funext t
      congr 1
      ext i
      fin_cases i <;> simp [exercise06Point]
    · simp

/-- On the punctured diagonal the function is constantly `1/2`. -/
theorem exercise06_diagonal (t : ℝ) (ht : t ≠ 0) :
    exercise06Function (exercise06Point t t) = 1 / 2 := by
  change t * t / (t ^ 2 + t ^ 2) = 1 / 2
  have hd : t ^ 2 + t ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero ht]
  field_simp
  ring

/-- Despite both partial derivatives, the function is not continuous at the origin. -/
theorem exercise06_discontinuity : ¬ ContinuousAt exercise06Function 0 := by
  intro h
  have hp : Continuous (fun t : ℝ => exercise06Point t t) := by
    unfold exercise06Point
    fun_prop
  have hc : ContinuousAt (fun t : ℝ => exercise06Function (exercise06Point t t)) 0 :=
    h.comp_of_eq hp.continuousAt exercise06Point_zero
  have hzero : Tendsto (fun t : ℝ => exercise06Function (exercise06Point t t))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => exercise06Function (exercise06Point t t))
      =ᶠ[𝓝[≠] 0] (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact exercise06_diagonal t ht
  have hhalf : Tendsto (fun t : ℝ => exercise06Function (exercise06Point t t))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds.congr' heq.symm
  have he : (0 : ℝ) = 1 / 2 := tendsto_nhds_unique hzero hhalf
  norm_num at he

end Rudin.Chapter09
