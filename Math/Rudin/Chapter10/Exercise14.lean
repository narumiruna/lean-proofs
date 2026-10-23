module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Basic.Real.Basic

/-! # Chapter 10, Exercise 14
The coordinate differentials are covectors. Their wedge is `ιMulti` in the
exterior algebra of the dual space. Reordering its factors has the same scalar
as the determinant of the corresponding permutation matrix.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise14

open ExteriorAlgebra

/-- The coordinate differential `dxᵢ`. -/
def dx {n : ℕ} (i : Fin n) : Module.Dual ℝ (Fin n → ℝ) :=
  LinearMap.proj i

/-- The actual wedge of a tuple of coordinate differentials. -/
def coordinateWedge {n k : ℕ} (j : Fin k → Fin n) :
    ExteriorAlgebra ℝ (Module.Dual ℝ (Fin n → ℝ)) :=
  ιMulti ℝ k (fun i => dx (j i))

/-- The determinant definition of the sign of a permutation. -/
def determinantSign {k : ℕ} (σ : Equiv.Perm (Fin k)) : ℝ :=
  Matrix.det ((1 : Matrix (Fin k) (Fin k) ℝ).submatrix σ id)

theorem determinantSign_eq {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    determinantSign σ = (σ.sign : ℤ) := by
  simp [determinantSign, Matrix.det_permute]

/-- Reordering coordinate differentials gives exactly the determinant sign.
For an increasing tuple `j`, this is equations (45)--(46). The result also
holds when indices repeat: then the alternating wedge vanishes. -/
theorem permutation_sign {n k : ℕ} (j : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    coordinateWedge (j ∘ σ) = determinantSign σ • coordinateWedge j := by
  have h := (ιMulti ℝ k (M := Module.Dual ℝ (Fin n → ℝ))).map_perm
    (fun i => dx (j i)) σ
  simpa only [coordinateWedge, determinantSign_eq, Units.smul_def,
    Int.cast_smul_eq_zsmul, Function.comp_def] using h

/-- An interchange changes the wedge sign, as in the source sorting procedure. -/
theorem interchange {n k : ℕ} (j : Fin k → Fin n) {a b : Fin k} (hab : a ≠ b) :
    coordinateWedge (j ∘ Equiv.swap a b) = -coordinateWedge j := by
  exact (ιMulti ℝ k).map_swap (fun i => dx (j i)) hab

end Rudin.Chapter10.Exercise14
