module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Real.Cardinality

/-!
# R02E19: separated sets and uncountability

Source: Rudin, Third Edition, book page 44 (PDF page 53).
Separated sets mean that neither set meets the closure of the other.
This is weaker than disjoint closures.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set

/-- Rudin's separation condition, not a positive-distance condition. -/
def separatedSets {X : Type*} [TopologicalSpace X] (A B : Set X) : Prop :=
  Disjoint (closure A) B ∧ Disjoint A (closure B)

theorem exercise19_a {X : Type*} [MetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (h : Disjoint A B) :
    separatedSets A B := by
  simpa [separatedSets, hA.closure_eq, hB.closure_eq] using And.intro h h

theorem exercise19_b {X : Type*} [MetricSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (h : Disjoint A B) :
    separatedSets A B :=
  ⟨h.closure_left hB, h.closure_right hA⟩

theorem exercise19_c {X : Type*} [MetricSpace X] (p : X) (δ : ℝ) :
    separatedSets {q | dist p q < δ} {q | δ < dist p q} := by
  apply exercise19_b (isOpen_lt (continuous_const.dist continuous_id) continuous_const)
    (isOpen_lt continuous_const (continuous_const.dist continuous_id))
  exact Set.disjoint_left.mpr fun _ h₁ h₂ => (lt_asymm h₁ h₂)

/-- A connected metric space with two distinct points cannot be countable. -/
theorem exercise19_d {X : Type*} [MetricSpace X] [PreconnectedSpace X]
    (a b : X) (hab : a ≠ b) : ¬ (Set.univ : Set X).Countable := by
  intro hc
  have him : IsPreconnected ((fun x => dist a x) '' (Set.univ : Set X)) :=
    isPreconnected_univ.image _ (continuous_const.dist continuous_id).continuousOn
  have hI : Set.Icc 0 (dist a b) ⊆ (fun x => dist a x) '' (Set.univ : Set X) :=
    him.Icc_subset (by exact ⟨a, Set.mem_univ a, dist_self a⟩)
      ⟨b, Set.mem_univ b, rfl⟩
  have hle := Cardinal.Real.Icc_countable_iff.mp ((hc.image _).mono hI)
  exact (dist_pos.mpr hab).not_ge hle

end Rudin.Chapter02
