module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# R09E04: null spaces and ranges are vector spaces

Source: Rudin, Exercise 9.4, book page 239 (PDF page 248), and
Section 9.30, book page 228. A `Submodule K X` is a vector subspace:
its subtype has the inherited addition and scalar multiplication, and a
`Module K` instance. The carrier equalities identify the exact source sets.
No dimension or nontriviality assumption is used.
-/

@[expose] public section

namespace Rudin.Chapter09

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The null space is a vector subspace with the inherited operations. -/
theorem exercise04_kernel (A : X →ₗ[K] Y) :
    ∃ S : Submodule K X, (S : Set X) = {x | A x = 0} :=
  ⟨A.ker, rfl⟩

/-- The range is a vector subspace with the inherited operations. -/
theorem exercise04_range (A : X →ₗ[K] Y) :
    ∃ S : Submodule K Y, (S : Set Y) = Set.range A :=
  ⟨A.range, rfl⟩

end Rudin.Chapter09
