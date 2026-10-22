module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# R01E05: the infimum and the supremum of the negated set

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 1.5, book page 22 (PDF page 31).

The image `(fun x : ℝ => -x) '' A` is Rudin's set `-A`.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Negation changes a nonempty bounded-below real set into a nonempty
bounded-above set, whose supremum is the negative of the original infimum. -/
theorem exercise05 (A : Set ℝ) (hA : A.Nonempty) (hbelow : BddBelow A) :
    ((fun x : ℝ => -x) '' A).Nonempty ∧
      BddAbove ((fun x : ℝ => -x) '' A) ∧
      sInf A = -sSup ((fun x : ℝ => -x) '' A) := by
  have hneg : ((fun x : ℝ => -x) '' A).Nonempty := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨-x, ⟨x, hx, rfl⟩⟩
  have habove : BddAbove ((fun x : ℝ => -x) '' A) := by
    obtain ⟨b, hb⟩ := hbelow
    refine ⟨-b, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact neg_le_neg (hb hx)
  refine ⟨hneg, habove, le_antisymm ?_ ?_⟩
  · apply le_neg_of_le_neg
    apply csSup_le hneg
    rintro _ ⟨x, hx, rfl⟩
    exact neg_le_neg (csInf_le hbelow hx)
  · apply le_csInf hA
    intro x hx
    exact neg_le_of_neg_le (le_csSup habove ⟨x, hx, rfl⟩)

end Rudin.Chapter01
