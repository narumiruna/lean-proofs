module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Exercise 10.30: the actual Euclidean normal

The displayed matrix has columns α, β, and their cross product. No rank or
nondegeneracy assumption is needed for either identity.
-/

@[expose] public section

namespace Rudin.Chapter10

open Matrix
open scoped Matrix

abbrev Exercise30Space := EuclideanSpace ℝ (Fin 3)
abbrev Exercise30Parameter := EuclideanSpace ℝ (Fin 2)

noncomputable def exercise30Normal (α β : Exercise30Space) : Exercise30Space :=
  WithLp.toLp 2 ((fun i ↦ α i) ⨯₃ (fun i ↦ β i))

/-- Formula (134), as a genuine linear map. -/
noncomputable def exercise30Map (α β : Exercise30Space) :
    Exercise30Parameter →ₗ[ℝ] Exercise30Space where
  toFun u := u 0 • α + u 1 • β
  map_add' u v := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' c u := by simp [smul_add, mul_smul]

/-- The matrix printed in the exercise, with the three vectors as columns. -/
noncomputable def exercise30Matrix (α β : Exercise30Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.transpose ![(fun i ↦ α i), (fun i ↦ β i), (fun i ↦ exercise30Normal α β i)]

theorem exercise30_normal_coordinates (α β : Exercise30Space) :
    (fun i ↦ exercise30Normal α β i) =
      ![α 1 * β 2 - α 2 * β 1, α 2 * β 0 - α 0 * β 2, α 0 * β 1 - α 1 * β 0] := rfl

theorem exercise30_basis (α β : Exercise30Space) :
    exercise30Map α β (EuclideanSpace.single 0 1) = α ∧
      exercise30Map α β (EuclideanSpace.single 1 1) = β := by
  simp [exercise30Map]

set_option backward.isDefEq.respectTransparency false in
theorem exercise30_determinant (α β : Exercise30Space) :
    Matrix.det (exercise30Matrix α β) = ‖exercise30Normal α β‖ ^ 2 := by
  rw [exercise30Matrix, Matrix.det_transpose, ← triple_product_eq_det,
    triple_product_permutation, triple_product_permutation,
    EuclideanSpace.real_norm_sq_eq]
  change (∑ i, exercise30Normal α β i * exercise30Normal α β i) = _
  simp only [pow_two]

theorem exercise30_normal_perpendicular (α β : Exercise30Space) :
    inner ℝ (exercise30Normal α β) α = 0 ∧
      inner ℝ (exercise30Normal α β) β = 0 := by
  constructor <;> simp [EuclideanSpace.inner_eq_star_dotProduct, exercise30Normal]

/-- Equation (137), with the source map and its actual two basis images. -/
theorem exercise30_orthogonality (α β : Exercise30Space) :
    inner ℝ (exercise30Normal α β)
        (exercise30Map α β (EuclideanSpace.single 0 1)) = 0 ∧
      inner ℝ (exercise30Normal α β)
        (exercise30Map α β (EuclideanSpace.single 1 1)) = 0 := by
  rw [(exercise30_basis α β).1, (exercise30_basis α β).2]
  exact exercise30_normal_perpendicular α β

end Rudin.Chapter10
