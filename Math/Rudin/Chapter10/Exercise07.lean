module

public import Math.Rudin.Support.SimplexIntegration
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
noncomputable section
namespace Rudin.Chapter10
open Set
open Rudin.Support.SimplexIntegration

/-- The vertices in the source Cartesian coordinates. -/
def exercise07_vertices (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  insert 0 (range fun i => EuclideanSpace.single i 1)

theorem exercise07_convex (n : ℕ) : Convex ℝ (standardSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

/-- Minimality includes dimension zero, where the sole vertex is zero. -/
theorem exercise07_minimal {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) (h0 : 0 ∈ C)
    (he : ∀ i, EuclideanSpace.single i 1 ∈ C) : standardSimplex n ⊆ C := by
  intro x hx
  let w : Option (Fin n) → ℝ := Option.elim' (1 - ∑ i, x i) (fun i => x i)
  let v : Option (Fin n) → EuclideanSpace ℝ (Fin n) :=
    Option.elim' 0 (fun i => EuclideanSpace.single i 1)
  have hw : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hx.2
    | some i => exact hx.1 i
  have hs : ∑ i, w i = 1 := by simp [w, Fintype.sum_option]
  have hv : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))), v i ∈ C := by
    intro i _
    cases i with
    | none => exact h0
    | some i => exact he i
  have h := hC.sum_mem hw hs hv
  have heq : ∑ i, w i • v i = x := by
    ext j
    simp [w, v, Fintype.sum_option, EuclideanSpace.single, Pi.single_apply,
      Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

/-- Equality with the actual convex hull, not a replacement definition of the simplex. -/
theorem exercise07_a (n : ℕ) :
    standardSimplex n = convexHull ℝ (exercise07_vertices n) := by
  apply Subset.antisymm
  · apply exercise07_minimal (convex_convexHull _ _)
    · exact subset_convexHull ℝ _ (mem_insert _ _)
    · intro i
      exact subset_convexHull ℝ _ (mem_insert_of_mem _ (mem_range_self i))
  · apply convexHull_min _ (exercise07_convex n)
    rintro x (rfl | ⟨i, rfl⟩)
    · simp [standardSimplex]
    · constructor
      · intro j
        simp [EuclideanSpace.single]
        split_ifs <;> norm_num
      · simp [EuclideanSpace.single]

/-- Affine images preserve convexity without openness or nonemptiness assumptions. -/
theorem exercise07_b {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (T : E →ᵃ[ℝ] F) {C : Set E}
    (hC : Convex ℝ C) : Convex ℝ (T '' C) := hC.affine_image T

end Rudin.Chapter10
