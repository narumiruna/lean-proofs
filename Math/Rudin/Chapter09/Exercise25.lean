module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # A right inverse on the range gives a projection

The source map `S` is defined on the range of `A`. The dimension identity
below follows from the complementary kernel and range of the actual projection.
-/

@[expose] public section

namespace Rudin.Chapter09
open LinearMap Module

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A linear right inverse on the range exists, including the zero map. -/
theorem exercise25_right_inverse (A : E →ₗ[ℝ] F) :
    ∃ S : LinearMap.range A →ₗ[ℝ] E, Function.LeftInverse A.rangeRestrict S := by
  obtain ⟨S, hS⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  exact ⟨S, LinearMap.congr_fun hS⟩

/-- The source `SA` uses the restriction of `A` to its actual range. -/
def exercise25Projection (A : E →ₗ[ℝ] F) (S : LinearMap.range A →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  S.comp A.rangeRestrict

theorem exercise25_projection (A : E →ₗ[ℝ] F) (S : LinearMap.range A →ₗ[ℝ] E)
    (hS : Function.LeftInverse A.rangeRestrict S) :
    (exercise25Projection A S).comp (exercise25Projection A S) = exercise25Projection A S := by
  ext x
  change S (A.rangeRestrict (S (A.rangeRestrict x))) = S (A.rangeRestrict x)
  rw [hS]

theorem exercise25_kernel (A : E →ₗ[ℝ] F) (S : LinearMap.range A →ₗ[ℝ] E)
    (hS : Function.LeftInverse A.rangeRestrict S) :
    LinearMap.ker (exercise25Projection A S) = LinearMap.ker A := by
  ext x
  change S (A.rangeRestrict x) = 0 ↔ A x = 0
  constructor
  · intro h
    have hr : A.rangeRestrict x = 0 := by
      rw [← hS (A.rangeRestrict x), h, map_zero]
    exact congrArg Subtype.val hr
  · intro h
    have hr : A.rangeRestrict x = 0 := Subtype.ext h
    simp only [hr, map_zero]

theorem exercise25_range (A : E →ₗ[ℝ] F) (S : LinearMap.range A →ₗ[ℝ] E) :
    LinearMap.range (exercise25Projection A S) = LinearMap.range S := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨A.rangeRestrict x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := z.property
    refine ⟨x, congrArg S (show A.rangeRestrict x = z from Subtype.ext hx)⟩

/-- Use the projection in part (a), not an independent rank-nullity assumption. -/
theorem exercise25_dimension [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] F)
    (S : LinearMap.range A →ₗ[ℝ] E) (hS : Function.LeftInverse A.rangeRestrict S) :
    finrank ℝ (LinearMap.ker A) + finrank ℝ (LinearMap.range A) = finrank ℝ E := by
  have hp : IsIdempotentElem (exercise25Projection A S) := exercise25_projection A S hS
  have hd := Submodule.finrank_add_eq_of_isCompl hp.isCompl.symm
  rw [exercise25_kernel A S hS, exercise25_range A S,
    LinearMap.finrank_range_of_inj hS.injective] at hd
  exact hd

/-- Rudin's Euclidean spaces have the required dimension, also when `n = 0`. -/
theorem exercise25_b {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    finrank ℝ (LinearMap.ker A) + finrank ℝ (LinearMap.range A) = n := by
  obtain ⟨S, hS⟩ := exercise25_right_inverse A
  simpa using exercise25_dimension A S hS

end Rudin.Chapter09
