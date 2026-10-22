module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Algebra.Module.PerfectSpace
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# R02E09: interior and closure

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.9, book page 43 (PDF page 52).

Parts (a)--(d) hold in any metric space. In (e), the punctured real line has
itself as interior, but its closure has the whole real line as interior.
In (f), a singleton is closed but its interior is empty.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- The interior of a set is open. -/
theorem exercise09a {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpen (interior E) := isOpen_interior

/-- A set is open exactly when it equals its interior. -/
theorem exercise09b {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpen E ↔ interior E = E := interior_eq_iff_isOpen.symm

/-- Every open subset of a set lies in its interior. -/
theorem exercise09c {X : Type*} [MetricSpace X] {E G : Set X}
    (hGE : G ⊆ E) (hG : IsOpen G) : G ⊆ interior E :=
  hG.subset_interior_iff.2 hGE

/-- The complement of the interior equals the closure of the complement. -/
theorem exercise09d {X : Type*} [MetricSpace X] (E : Set X) :
    (interior E)ᶜ = closure Eᶜ := by
  rw [closure_eq_compl_interior_compl, compl_compl]

/-- A set and its closure need not have the same interior: take the punctured
real line. -/
theorem exercise09e :
    interior ({0}ᶜ : Set ℝ) ≠ interior (closure ({0}ᶜ : Set ℝ)) := by
  rw [closure_compl_singleton, interior_univ,
    isClosed_singleton.isOpen_compl.interior_eq]
  intro h
  have hz : (0 : ℝ) ∈ ({0}ᶜ : Set ℝ) := h.symm ▸ Set.mem_univ 0
  exact hz rfl

/-- A set and its interior need not have the same closure: take a singleton
in the real line. -/
theorem exercise09f :
    closure ({0} : Set ℝ) ≠ closure (interior ({0} : Set ℝ)) := by
  rw [closure_singleton, interior_singleton, closure_empty]
  exact Set.singleton_ne_empty 0

end Rudin.Chapter02
