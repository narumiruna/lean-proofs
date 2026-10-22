module

public import Mathlib.Topology.MetricSpace.Basic

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# R02E23: a countable base in a separable metric space

Source: Rudin, Third Edition, book page 45 (PDF page 54).
The hypothesis is the existence of an at most countable dense subset.
The conclusion spells out the neighborhood refinement property.
-/

@[expose] public section

namespace Rudin.Chapter02

open TopologicalSpace Set

theorem exercise23 {X : Type*} [MetricSpace X]
    (h : ∃ D : Set X, D.Countable ∧ Dense D) :
    ∃ B : Set (Set X), B.Countable ∧
      (∀ V ∈ B, IsOpen V) ∧
      ∀ (G : Set X), IsOpen G → ∀ x ∈ G, ∃ V ∈ B, x ∈ V ∧ V ⊆ G := by
  let : SeparableSpace X := ⟨h⟩
  let : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  obtain ⟨B, hB, _, hb⟩ := exists_countable_basis X
  exact ⟨B, hB, fun _ hV => hb.isOpen hV,
    fun _ hG _ hx => hb.exists_subset_of_mem_open hx hG⟩

end Rudin.Chapter02
