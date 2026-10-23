module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# R09E05: representation and norm of a real linear functional

Source: Rudin, Exercise 9.5, book page 239 (PDF page 248).
The representing vector is constructed from the values on the coordinate
vectors. The domain is `EuclideanSpace ℝ (Fin n)`, with no assumption `0 < n`.
The codomain `ℝ` is the usual identification of real Euclidean one-space.
Continuity follows from finite dimension; it is not an extra hypothesis.
The operator norm is also identified with the supremum over the closed unit
ball from Section 9.6(c). The norm proof uses the inner-product functional's
norm theorem, whose proof uses Schwarz's inequality and evaluation at the
representing vector (and treats the zero vector separately).
-/

@[expose] public section

namespace Rudin.Chapter09

/-- The explicit coordinate construction: `y i = A eᵢ`. -/
noncomputable def exercise05Vector {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => A (EuclideanSpace.single i 1))

/-- The constructed vector represents the functional by the Euclidean dot product. -/
theorem exercise05_representing_vector {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    A x = inner ℝ x (exercise05Vector A) := by
  calc
    A x = ∑ i, x i * A (EuclideanSpace.single i 1) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
      simp [map_sum, EuclideanSpace.basisFun_apply]
    _ = inner ℝ x (exercise05Vector A) := by
      simp [PiLp.inner_apply, exercise05Vector, mul_comm]

/-- No other vector represents the same functional. -/
theorem exercise05_uniqueness {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin n))
    (hy : ∀ x, A x = inner ℝ x y) : y = exercise05Vector A := by
  ext i
  simpa [exercise05Vector, EuclideanSpace.inner_single_left] using
    (hy (EuclideanSpace.single i 1)).symm

/-- Existence and uniqueness, including dimension zero. -/
theorem exercise05_existsUnique {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) :
    ∃! y : EuclideanSpace ℝ (Fin n), ∀ x, A x = inner ℝ x y :=
  ⟨exercise05Vector A, exercise05_representing_vector A, exercise05_uniqueness A⟩

/-- The operator norm equals the Euclidean norm of the representing vector. -/
theorem exercise05_norm {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) :
    ‖A.toContinuousLinearMap‖ = ‖exercise05Vector A‖ := by
  have hA : A.toContinuousLinearMap = innerSL ℝ (exercise05Vector A) := by
    ext x
    simpa [real_inner_comm] using exercise05_representing_vector A x
  rw [hA, innerSL_apply_norm]

/-- The norm in the preceding theorem is Rudin's closed-unit-ball supremum. -/
theorem exercise05_source_norm {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) :
    sSup ((fun x => ‖A x‖) '' Metric.closedBall 0 1) = ‖exercise05Vector A‖ := by
  rw [← exercise05_norm A]
  exact A.toContinuousLinearMap.sSup_unitClosedBall_eq_norm

end Rudin.Chapter09
