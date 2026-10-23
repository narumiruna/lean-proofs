module

public import Math.Rudin.Chapter07.Exercise25

/-! # Chapter 7, Exercise 26

Source: PDF page 180, book page 171. The Euler polygons and residuals of
Exercise 25 were constructed for normed real vector spaces. Here they are
specialized to Euclidean space, with the Euclidean norm and vector-valued
Ascoli selection, not a general ODE existence theorem.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Rudin.Chapter07

/-- The exact vector Euler construction converges along a subsequence to a solution.
The conclusion includes both one-sided endpoint derivatives. -/
theorem exercise26_vector_existence {k : ℕ}
    (Φ : ℝ → EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (c : EuclideanSpace ℝ (Fin k))
    (hc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin k) => Φ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ))
    (hb : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖Φ t z‖ ≤ M) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin k), ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformlyOn (fun n => Euler.polygon Φ c (σ n + 1)) f atTop (Icc (0 : ℝ) 1) ∧
      ContinuousOn f (Icc (0 : ℝ) 1) ∧ f 0 = c ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f x = c + ∫ t in (0 : ℝ)..x, Φ t (f t)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (Φ x (f x)) (Icc (0 : ℝ) 1) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (Φ x (f x)) x) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (left_mem_Icc.mpr zero_le_one) c)
  exact Euler.exists_solution hc c (M := ⟨M, hM0⟩) hM

/-- The same vector construction retains the uniform vanishing-residual estimate. -/
theorem exercise26_vector_residual {k : ℕ}
    (Φ : ℝ → EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (c : EuclideanSpace ℝ (Fin k))
    (hc : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin k) => Φ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ))
    (hb : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z, ‖Φ t z‖ ≤ M) :
    TendstoUniformlyOn (fun n => Euler.residual Φ c (n + 1))
      (fun _ => 0) atTop (Icc (0 : ℝ) 1) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (left_mem_Icc.mpr zero_le_one) c)
  exact Euler.residual_uniform hc c (M := ⟨M, hM0⟩) hM

end Rudin.Chapter07
