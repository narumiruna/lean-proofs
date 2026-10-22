module

public import Mathlib.Order.Bounds.Basic

/-!
# R01E04: order of lower and upper bounds

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 1.4, book page 22 (PDF page 31).
-/

@[expose] public section

namespace Rudin.Chapter01

/-- A lower bound of a nonempty set is at most each upper bound. -/
theorem exercise04 {α : Type*} [LinearOrder α] (E : Set α) (hE : E.Nonempty)
    (a b : α) (ha : a ∈ lowerBounds E) (hb : b ∈ upperBounds E) : a ≤ b := by
  obtain ⟨x, hx⟩ := hE
  exact (ha hx).trans (hb hx)

end Rudin.Chapter01
