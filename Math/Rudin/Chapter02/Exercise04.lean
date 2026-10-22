module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Set.Countable
public import Mathlib.NumberTheory.Real.Irrational

/-!
# R02E04: the irrational numbers are uncountable

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.4, book page 43 (PDF page 52).
-/

@[expose] public section

namespace Rudin.Chapter02

/-- The set of irrational real numbers is not countable. -/
theorem exercise04 : ¬ ({x : ℝ | Irrational x} : Set ℝ).Countable := by
  intro h
  have hr : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have hu : (Set.range ((↑) : ℚ → ℝ)) ∪ {x : ℝ | Irrational x} = Set.univ := by
    ext x
    simp only [Irrational, Set.mem_union, Set.mem_range, Set.mem_ofPred_eq,
      Set.mem_univ, iff_true]
    exact Classical.em _
  exact Set.not_countable_univ (hu ▸ hr.union h)

end Rudin.Chapter02
