module

public import Mathlib.Data.Set.Basic

/-!
# R02E01: the empty set is a subset of every set

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.1, book page 43 (PDF page 52).
-/

@[expose] public section

namespace Rudin.Chapter02

/-- The empty set is a subset of every set, in any ambient type. -/
theorem exercise01 {α : Type*} (A : Set α) : (∅ : Set α) ⊆ A := by
  intro x hx
  exact False.elim hx

end Rudin.Chapter02
