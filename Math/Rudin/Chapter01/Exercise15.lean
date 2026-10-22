module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R01E15: equality in the finite complex Schwarz inequality

Source: Rudin, Exercise 1.15, book page 23 (PDF page 32), referring to
Theorem 1.35, book page 15 (PDF page 24). `Fin n` reindexes `1, …, n`.
The source sum is `a j * conj (b j)`. Mathlib conjugates the first argument,
so the bridge uses `inner b a`. The Euclidean norm, not the function-space
supremum norm, gives the sums of squared moduli. Both zero-vector branches
are explicit in the final criterion, including when `n = 0`.
-/

@[expose] public section

namespace Rudin.Chapter01

open scoped ComplexConjugate

/-- Bridge from the source finite sum to the complex Euclidean inner product. -/
theorem exercise15_inner_sum {n : ℕ} (a b : Fin n → ℂ) :
    inner ℂ (WithLp.toLp 2 b) (WithLp.toLp 2 a) =
      ∑ j, a j * conj (b j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]

/-- Bridge from the Euclidean norm to the source sum of squared moduli. -/
theorem exercise15_norm_sq_sum {n : ℕ} (a : Fin n → ℂ) :
    ‖WithLp.toLp 2 a‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
  exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 a)

/-- The finite complex Schwarz inequality in the source's notation. -/
theorem exercise15_schwarz {n : ℕ} (a b : Fin n → ℂ) :
    ‖∑ j, a j * conj (b j)‖ ^ 2 ≤
      (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by
  rw [← exercise15_inner_sum, ← exercise15_norm_sq_sum,
    ← exercise15_norm_sq_sum, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (by
    simpa [mul_comm] using norm_inner_le_norm (WithLp.toLp 2 b) (WithLp.toLp 2 a)) 2

/-- An asymmetric equality criterion: zero first vector or proportional vectors. -/
theorem exercise15_proportional {n : ℕ} (a b : Fin n → ℂ) :
    ‖∑ j, a j * conj (b j)‖ ^ 2 =
        (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) ↔
      (∀ j, a j = 0) ∨ ∃ c : ℂ, ∀ j, b j = c * a j := by
  rw [← exercise15_inner_sum, ← exercise15_norm_sq_sum,
    ← exercise15_norm_sq_sum, norm_inner_symm,
    ← mul_pow, sq_eq_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have ht := (norm_inner_eq_norm_tfae ℂ (WithLp.toLp 2 a) (WithLp.toLp 2 b)).out 1 3
  rw [ht]
  have hz : WithLp.toLp 2 a = 0 ↔ ∀ j, a j = 0 := by
    constructor
    · intro h j
      exact congrArg (fun x : EuclideanSpace ℂ (Fin n) => x j) h
    · intro h
      ext j
      exact h j
  have hs (c : ℂ) : WithLp.toLp 2 b = c • WithLp.toLp 2 a ↔
      ∀ j, b j = c * a j := by
    constructor
    · intro h j
      exact congrArg (fun x : EuclideanSpace ℂ (Fin n) => x j) h
    · intro h
      ext j
      exact h j
  exact or_congr hz (exists_congr hs)

/-- Complete equality classification with both zero-vector branches explicit. -/
theorem exercise15 {n : ℕ} (a b : Fin n → ℂ) :
    ‖∑ j, a j * conj (b j)‖ ^ 2 =
        (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) ↔
      (∀ j, a j = 0) ∨ (∀ j, b j = 0) ∨
        ∃ c : ℂ, c ≠ 0 ∧ ∀ j, b j = c * a j := by
  rw [exercise15_proportional]
  constructor
  · rintro (ha | ⟨c, hc⟩)
    · exact Or.inl ha
    · by_cases hzero : c = 0
      · exact Or.inr (Or.inl (by simpa [hzero] using hc))
      · exact Or.inr (Or.inr ⟨c, hzero, hc⟩)
  · rintro (ha | hb | ⟨c, _, hc⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨0, by simpa using hb⟩
    · exact Or.inr ⟨c, hc⟩

end Rudin.Chapter01
