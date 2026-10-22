module

public import Math.Rudin.Chapter02.Exercise12

/-!
# R02E06: derived sets and closure

Source: Rudin, Exercise 2.6, book page 43 (PDF page 52).
The counterexample is the positive reciprocal sequence: its derived set is
`{0}`, whose derived set is empty.
-/

@[expose] public section

open Set Topology

namespace Rudin.Chapter02

/-- The accumulation points of a metric-space set form a closed set. -/
theorem exercise06_derived_closed {X : Type*} [MetricSpace X] (E : Set X) :
    IsClosed (derivedSet E) :=
  isClosed_derivedSet E

/-- A set and its closure have the same accumulation points. -/
theorem exercise06_closure_limit_points {X : Type*} [MetricSpace X] (E : Set X) :
    closure E = E ∪ derivedSet E ∧ derivedSet (closure E) = derivedSet E :=
  ⟨closure_eq_self_union_derivedSet E, derivedSet_closure E⟩

/-- Exact derived sets for the reciprocal-sequence counterexample. -/
theorem exercise06_counterexample :
    derivedSet (range reciprocalTerm) = {0} ∧
    derivedSet (derivedSet (range reciprocalTerm)) = ∅ ∧
    derivedSet (range reciprocalTerm) ≠ derivedSet (derivedSet (range reciprocalTerm)) := by
  rw [derivedSet_reciprocalRange, derivedSet_of_finite (finite_singleton (0 : ℝ))]
  exact ⟨rfl, rfl, by simp⟩

/-- Sets and their derived sets need not have the same accumulation points. -/
theorem exercise06_derived_limit_points :
    ∃ E : Set ℝ, derivedSet E ≠ derivedSet (derivedSet E) :=
  ⟨range reciprocalTerm, exercise06_counterexample.2.2⟩

end Rudin.Chapter02
