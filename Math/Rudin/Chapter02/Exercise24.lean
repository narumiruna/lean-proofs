module

public import Mathlib.Topology.MetricSpace.Basic

public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# R02E24: separability from the accumulation-point property

Source: Rudin, Third Edition, book page 45 (PDF page 54).
Later results are allowed: the accumulation-point property first gives
countable compactness, then sequential compactness and metric compactness.
No hypothesis that the ambient space is infinite or nonempty is used.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Filter Topology TopologicalSpace

/-- The limit-point hypothesis implies metric compactness. -/
theorem compact_of_infinite_accumulation {X : Type*} [MetricSpace X]
    (h : ∀ E : Set X, E.Infinite → ∃ x : X, AccPt x (𝓟 E)) :
    IsCompact (Set.univ : Set X) := by
  have hc : IsCountablyCompact (Set.univ : Set X) :=
    isCountablyCompact_iff_infinite_subset_has_accPt.mpr
      (fun E _ hE => by
        obtain ⟨x, hx⟩ := h E hE
        exact ⟨x, Set.mem_univ x, hx⟩)
  exact hc.isSeqCompact.isCompact

theorem exercise24 {X : Type*} [MetricSpace X]
    (h : ∀ E : Set X, E.Infinite → ∃ x : X, AccPt x (𝓟 E)) :
    ∃ D : Set X, D.Countable ∧ Dense D := by
  let : CompactSpace X := ⟨compact_of_infinite_accumulation h⟩
  exact exists_countable_dense X

end Rudin.Chapter02
