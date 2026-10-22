module

public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Countable

/-!
# R02E02: countably infinitely many algebraic complex numbers

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.2, book page 43 (PDF page 52).

The coefficients are integers. The condition `p ≠ 0` means that they are not
all zero; it does not require a specified leading coefficient to be nonzero.
Every finite coefficient list in the source defines such a polynomial, and
polynomial coefficients give a finite list by truncation at `natDegree`.

We identify the set with the union of the finite complex root sets of integer
polynomials. Infinitude is proved separately, using the natural numbers in `ℂ`,
so that the conclusion is countably infinite, not just at most countable.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- Complex roots of nonzero polynomials with integer coefficients. -/
def algebraicNumbers : Set ℂ :=
  {z | ∃ p : Polynomial ℤ, p ≠ 0 ∧ p.eval₂ (Int.castRingHom ℂ) z = 0}

/-- The explicit integer-polynomial predicate agrees with root-set membership. -/
theorem mem_algebraicNumbers_iff (z : ℂ) :
    z ∈ algebraicNumbers ↔ ∃ p : Polynomial ℤ, z ∈ p.rootSet ℂ := by
  simp only [algebraicNumbers, Set.mem_ofPred_eq, Polynomial.mem_rootSet,
    Polynomial.aeval_def]
  rfl

/-- Algebraic numbers are exactly the union of the integer-polynomial root sets. -/
theorem algebraicNumbers_eq_iUnion :
    algebraicNumbers = ⋃ p : Polynomial ℤ, p.rootSet ℂ := by
  ext z
  simp only [mem_algebraicNumbers_iff, Set.mem_iUnion]

/-- There are at most countably many algebraic complex numbers. -/
theorem algebraicNumbers_countable : algebraicNumbers.Countable := by
  let : Countable (Polynomial ℤ) :=
    (Polynomial.toFinsuppIso ℤ).injective.countable
  rw [algebraicNumbers_eq_iUnion]
  exact Set.countable_iUnion fun p => (p.rootSet_finite ℂ).countable

/-- Each natural number is a root of the nonzero integer polynomial `X - C n`. -/
theorem natCast_mem_algebraicNumbers (n : ℕ) : (n : ℂ) ∈ algebraicNumbers := by
  apply (mem_algebraicNumbers_iff _).2
  refine ⟨Polynomial.X - Polynomial.C (n : ℤ), ?_⟩
  rw [Polynomial.mem_rootSet]
  exact ⟨Polynomial.X_sub_C_ne_zero _, by simp⟩

/-- The natural numbers embed into the set, which is therefore infinite. -/
theorem algebraicNumbers_infinite : algebraicNumbers.Infinite := by
  exact Set.infinite_of_injective_forall_mem Nat.cast_injective
    natCast_mem_algebraicNumbers

/-- The algebraic complex numbers form a countably infinite set. -/
theorem exercise02 : algebraicNumbers.Countable ∧ algebraicNumbers.Infinite :=
  ⟨algebraicNumbers_countable, algebraicNumbers_infinite⟩

end Rudin.Chapter02
