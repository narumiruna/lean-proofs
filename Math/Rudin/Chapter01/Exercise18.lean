module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R01E18: a nonzero orthogonal vector

Source: Rudin, book page 23 (PDF page 32).
The construction uses the first two coordinates, with a separate branch
when both are zero. In dimension one it is possible exactly when `x = 0`.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- An explicit vector orthogonal to `x`, using two coordinates. -/
noncomputable def exercise18_vector {k : ℕ} (hk : 2 ≤ k)
    (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  if x i = 0 ∧ x j = 0 then EuclideanSpace.single i 1
  else x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1

/-- The constructed vector is nonzero and orthogonal to `x`. -/
theorem exercise18_vector_spec {k : ℕ} (hk : 2 ≤ k)
    (x : EuclideanSpace ℝ (Fin k)) :
    exercise18_vector hk x ≠ 0 ∧ inner ℝ x (exercise18_vector hk x) = 0 := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  change (if x i = 0 ∧ x j = 0 then EuclideanSpace.single i 1
    else x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1) ≠ 0 ∧
    inner ℝ x (if x i = 0 ∧ x j = 0 then EuclideanSpace.single i 1
    else x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1) = 0
  by_cases h : x i = 0 ∧ x j = 0
  · simp only [h]
    constructor
    · intro hz
      have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v i) hz
      simp [i] at this
    · simpa [EuclideanSpace.inner_single_right, i] using h.1
  · simp only [h]
    constructor
    · intro hz
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v i) hz
      have hj := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v j) hz
      simp [hij, Ne.symm hij] at hi hj
      exact h ⟨hj, hi⟩
    · simp [inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]

/-- Every vector in dimension at least two has a nonzero orthogonal vector. -/
theorem exercise18 {k : ℕ} (hk : 2 ≤ k) (x : EuclideanSpace ℝ (Fin k)) :
    ∃ y : EuclideanSpace ℝ (Fin k), y ≠ 0 ∧ inner ℝ x y = 0 :=
  ⟨exercise18_vector hk x, exercise18_vector_spec hk x⟩

/-- In dimension one, only the zero vector has a nonzero orthogonal vector. -/
theorem exercise18_dimension_one (x : EuclideanSpace ℝ (Fin 1)) :
    (∃ y : EuclideanSpace ℝ (Fin 1), y ≠ 0 ∧ inner ℝ x y = 0) ↔ x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hy0 : y 0 ≠ 0 := by
      intro h
      apply hy
      ext i
      fin_cases i
      exact h
    have hprod : x 0 * y 0 = 0 := by
      simpa [PiLp.inner_apply, mul_comm] using hxy
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hprod).resolve_right hy0
    ext i
    fin_cases i
    exact hx0
  · rintro rfl
    refine ⟨EuclideanSpace.single 0 1, ?_, by simp⟩
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp at this

end Rudin.Chapter01
