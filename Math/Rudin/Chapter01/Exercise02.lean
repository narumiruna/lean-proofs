module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.NormNum.IsSquare

/-!
# R01E02: no rational square root of 12

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 1.2, book page 22 (PDF page 31).
-/

@[expose] public section

namespace Rudin.Chapter01

/-- No rational number has square 12. -/
theorem exercise02 (q : ℚ) : q ^ 2 ≠ 12 := by
  intro h
  have hs : IsSquare (12 : ℚ) := ⟨q, by simpa [pow_two] using h.symm⟩
  have hn : IsSquare (12 : ℕ) := Rat.isSquare_natCast_iff.mp hs
  norm_num at hn

end Rudin.Chapter01
