module

public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Set.Countable

/-!
# R02E03: a real number which is not algebraic

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.3, book page 43 (PDF page 52).

The union of the finite real root sets of integer polynomials is countable.
It cannot contain every real number. The conclusion uses the explicit
nonzero integer-polynomial condition of Exercise 2.2.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- The real roots of all integer polynomials form a countable set. The root
set of the zero polynomial is empty under Mathlib's `rootSet` convention. -/
theorem real_integer_polynomial_roots_countable :
    (⋃ p : Polynomial ℤ, p.rootSet ℝ).Countable := by
  let : Countable (Polynomial ℤ) :=
    (Polynomial.toFinsuppIso ℤ).injective.countable
  exact Set.countable_iUnion fun p => (p.rootSet_finite ℝ).countable

/-- Some real number is not a root of any nonzero integer polynomial. -/
theorem exercise03 :
    ∃ x : ℝ, ∀ p : Polynomial ℤ, p ≠ 0 →
      p.eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
  have hne : (⋃ p : Polynomial ℤ, p.rootSet ℝ) ≠ Set.univ := by
    intro h
    exact Set.not_countable_univ (h ▸ real_integer_polynomial_roots_countable)
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  refine ⟨x, fun p hp hroot => hx ?_⟩
  exact Set.mem_iUnion.2 ⟨p, Polynomial.mem_rootSet.2
    ⟨hp, by simpa only [Polynomial.aeval_def, algebraMap_int_eq] using hroot⟩⟩

end Rudin.Chapter02
