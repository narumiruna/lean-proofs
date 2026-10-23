module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# R09E02: composition and inverse of linear maps

Source: Rudin, Exercise 9.2, book page 239 (PDF page 248), and
Sections 9.4 and 9.6, book pages 207–208. Invertibility means bijectivity.
The inverse-linearity theorem starts with an ordinary two-sided inverse,
not with a linear equivalence. No dimension or nontriviality assumption is used.
-/

@[expose] public section

namespace Rudin.Chapter09

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- The composite `BA` is linear. -/
theorem exercise02_composition (A : X →ₗ[K] Y) (B : Y →ₗ[K] Z) :
    IsLinearMap K (B ∘ A) :=
  (B.comp A).isLinear

/-- A two-sided inverse of a linear operator is linear. -/
theorem exercise02_inverse_linearity (A : X →ₗ[K] X) (g : X → X)
    (hleft : Function.LeftInverse g A) (hright : Function.RightInverse g A) :
    IsLinearMap K g := by
  have hinj := hleft.injective
  constructor
  · intro x y
    apply hinj
    rw [hright, map_add, hright, hright]
  · intro c x
    apply hinj
    rw [hright, map_smul, hright]

/-- The inverse is bijective, and its two-sided inverse is the original map. -/
theorem exercise02_inverse_invertibility (A : X →ₗ[K] X) (g : X → X)
    (hleft : Function.LeftInverse g A) (hright : Function.RightInverse g A) :
    Function.Bijective g ∧ Function.LeftInverse A g ∧ Function.RightInverse A g :=
  ⟨⟨hright.injective, hleft.surjective⟩, hright, hleft⟩

/-- An invertible linear operator has a linear, invertible inverse. -/
theorem exercise02_inverse (A : X →ₗ[K] X) (hA : Function.Bijective A) :
    ∃ g : X → X, IsLinearMap K g ∧ Function.Bijective g ∧
      Function.LeftInverse g A ∧ Function.RightInverse g A ∧
      Function.LeftInverse A g ∧ Function.RightInverse A g := by
  let e := Equiv.ofBijective A hA
  have hl : Function.LeftInverse e.symm A := e.symm_apply_apply
  have hr : Function.RightInverse e.symm A := e.apply_symm_apply
  exact ⟨e.symm, exercise02_inverse_linearity A e.symm hl hr,
    e.symm.bijective, hl, hr, hr, hl⟩

end Rudin.Chapter09
