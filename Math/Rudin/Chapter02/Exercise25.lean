module

public import Math.Rudin.Chapter02.Exercise23
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# R02E25: separability and a countable base for compact metric spaces

Source: Rudin, Third Edition, book page 45 (PDF page 54).
Both families can be empty when the space is empty.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set TopologicalSpace

theorem exercise25_separable (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ D : Set X, D.Countable ∧ Dense D :=
  exists_countable_dense X

theorem exercise25_base (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ B : Set (Set X), B.Countable ∧
      (∀ V ∈ B, IsOpen V) ∧
      ∀ (G : Set X), IsOpen G → ∀ x ∈ G, ∃ V ∈ B, x ∈ V ∧ V ⊆ G :=
  exercise23 (exercise25_separable X)

end Rudin.Chapter02
