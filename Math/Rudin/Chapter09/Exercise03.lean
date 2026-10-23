module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# R09E03: a trivial kernel implies injectivity

Source: Rudin, Exercise 9.3, book page 239 (PDF page 248).
The argument applies to arbitrary vector spaces, including the zero space.
-/

@[expose] public section

namespace Rudin.Chapter09

/-- A linear map that maps only zero to zero is one-to-one. -/
theorem exercise03 {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (hA : ∀ x, A x = 0 → x = 0) :
    Function.Injective A := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hA
  rw [map_sub, hxy, sub_self]

end Rudin.Chapter09
