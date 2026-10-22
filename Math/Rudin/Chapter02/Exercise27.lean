module

public import Mathlib.Topology.Perfect
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R02E27: condensation points

Source: Rudin, Third Edition, book page 45 (PDF page 54).
A condensation point need not belong to the original set. The result is proved
for every set in a second-countable space, so it also covers the stated
uncountable Euclidean set.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Filter Topology TopologicalSpace

/-- Every open neighborhood meets the set in uncountably many points. -/
def condensationPoints {X : Type*} [TopologicalSpace X] (E : Set X) : Set X :=
  {x | ∀ U : Set X, IsOpen U → x ∈ U → ¬ (U ∩ E).Countable}

theorem condensationPoints_closed {X : Type*} [TopologicalSpace X] (E : Set X) :
    IsClosed (condensationPoints E) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  change ¬ (∀ U : Set X, IsOpen U → x ∈ U → ¬ (U ∩ E).Countable) at hx
  push Not at hx
  obtain ⟨U, hU, hxU, hct⟩ := hx
  apply mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  exact fun h => h U hU hy hct

theorem exercise27_countable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (E : Set X) : (E \ condensationPoints E).Countable := by
  obtain ⟨B, hB, _, hb⟩ := exists_countable_basis X
  have hc : (⋃ U ∈ {U ∈ B | (U ∩ E).Countable}, U ∩ E).Countable :=
    (hB.mono (sep_subset _ _)).biUnion (fun U hU => hU.2)
  apply hc.mono
  rintro x ⟨hxE, hx⟩
  change ¬ (∀ U : Set X, IsOpen U → x ∈ U → ¬ (U ∩ E).Countable) at hx
  push Not at hx
  obtain ⟨U, hU, hxU, hct⟩ := hx
  obtain ⟨V, hVB, hxV, hVU⟩ := hb.exists_subset_of_mem_open hxU hU
  exact mem_biUnion ⟨hVB, hct.mono (inter_subset_inter_left E hVU)⟩ ⟨hxV, hxE⟩

theorem exercise27_perfect {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (E : Set X) : Perfect (condensationPoints E) := by
  refine ⟨condensationPoints_closed E, ?_⟩
  rw [preperfect_iff_nhds]
  intro x hx U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  by_contra! hn
  have hc : (V ∩ E).Countable := by
    apply ((exercise27_countable E).union (Set.countable_singleton x)).mono
    rintro y ⟨hyV, hyE⟩
    by_cases hyP : y ∈ condensationPoints E
    · exact Or.inr (hn y ⟨hVU hyV, hyP⟩)
    · exact Or.inl ⟨hyE, hyP⟩
  exact hx V hV hxV hc

end Rudin.Chapter02
