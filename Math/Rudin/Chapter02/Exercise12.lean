module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic

/-!
# R02E12: compactness of the reciprocal sequence

Source: Rudin, Exercise 2.12, book page 44 (PDF page 53).
The proof selects one cover member at zero, uses convergence to cover a tail,
and selects finitely many cover members for the remaining terms. It does not
use the Heine–Borel theorem.
-/

@[expose] public section

open Set Filter Topology

namespace Rudin.Chapter02

/-- The positive reciprocal sequence, indexed starting at zero. -/
noncomputable def reciprocalTerm (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Zero together with the reciprocals of the positive integers. -/
def reciprocalSet : Set ℝ := insert 0 (range reciprocalTerm)

theorem reciprocalTerm_pos (n : ℕ) : 0 < reciprocalTerm n := by
  unfold reciprocalTerm
  positivity

theorem reciprocalTerm_tendsto : Tendsto reciprocalTerm atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem reciprocalTerm_injective : Function.Injective reciprocalTerm := by
  intro m n h
  simp only [reciprocalTerm, one_div, inv_inj] at h
  exact_mod_cast (add_right_cancel h : (m : ℝ) = n)

/-- The explicit construction agrees with the positive-integer formulation. -/
theorem mem_reciprocalSet_iff (x : ℝ) :
    x ∈ reciprocalSet ↔ x = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ) := by
  constructor
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n + 1, by omega, by simp [reciprocalTerm]⟩
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact mem_insert _ _
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact mem_insert_of_mem _ ⟨m, by simp [reciprocalTerm]⟩

/-- Direct finite-subcover argument for a sequence and its limit. -/
theorem convergentSequence_finite_subcover {X : Type*} [TopologicalSpace X]
    {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a))
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : insert a (range u) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, insert a (range u) ⊆ ⋃ i ∈ t, U i := by
  classical
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcover (mem_insert _ _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu ((hU i₀).mem_nhds hi₀))
  have hm (n : ℕ) : ∃ i, u n ∈ U i :=
    mem_iUnion.mp (hcover (mem_insert_of_mem _ (mem_range_self n)))
  choose f hf using hm
  refine ⟨insert i₀ ((Finset.range N).image f), ?_⟩
  rintro x (rfl | ⟨n, rfl⟩)
  · exact mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hi₀⟩
  · by_cases hn : n < N
    · exact mem_iUnion₂.mpr ⟨f n, Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩), hf n⟩
    · exact mem_iUnion₂.mpr ⟨i₀, Finset.mem_insert_self _ _, hN n (by omega)⟩

/-- Every open cover of the set in Exercise 12 has a finite subcover. -/
theorem reciprocalSet_finite_subcover {ι : Type*} (U : ι → Set ℝ)
    (hU : ∀ i, IsOpen (U i)) (hcover : reciprocalSet ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, reciprocalSet ⊆ ⋃ i ∈ t, U i :=
  convergentSequence_finite_subcover reciprocalTerm_tendsto U hU hcover

/-- Compactness follows from the open-cover definition, not Heine–Borel. -/
theorem exercise12 : IsCompact reciprocalSet :=
  isCompact_of_finite_subcover reciprocalSet_finite_subcover

/-- A finite set has no accumulation points in a T1 space. -/
theorem derivedSet_of_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) : derivedSet s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hs.not_infinite (Set.Infinite.of_accPt hx)

/-- A convergent sequence has no accumulation point other than its limit. -/
theorem derivedSet_range_subset_limit {X : Type*} [TopologicalSpace X] [T2Space X]
    {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a)) :
    derivedSet (range u) ⊆ {a} := by
  intro x hx
  by_contra hxa
  obtain ⟨V, W, hV, hW, hxV, haW, hVW⟩ := t2_separation (show x ≠ a by simpa using hxa)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu (hW.mem_nhds haW))
  have hinf := Set.Infinite.of_accPt (hx.nhds_inter (hV.mem_nhds hxV))
  apply hinf
  apply ((Set.finite_lt_nat N).image u).subset
  rintro y ⟨hyV, n, rfl⟩
  apply mem_image_of_mem
  by_contra hn
  exact Set.disjoint_left.mp hVW hyV (hN n (by simpa using hn))

/-- Convergence through points different from the limit gives an accumulation point. -/
theorem limit_mem_derivedSet_range {X : Type*} [TopologicalSpace X]
    {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a))
    (hne : ∀ n, u n ≠ a) : a ∈ derivedSet (range u) := by
  rw [mem_derivedSet, accPt_iff_nhds]
  intro V hV
  obtain ⟨n, hn⟩ := (show ∀ᶠ n in atTop, u n ∈ V from hu hV).exists
  exact ⟨u n, ⟨hn, mem_range_self n⟩, hne n⟩

/-- The reciprocal sequence has exactly one accumulation point. -/
theorem derivedSet_reciprocalRange : derivedSet (range reciprocalTerm) = {0} := by
  apply Subset.antisymm (derivedSet_range_subset_limit reciprocalTerm_tendsto)
  intro x hx
  rcases mem_singleton_iff.mp hx with rfl
  exact limit_mem_derivedSet_range reciprocalTerm_tendsto
    (fun n => ne_of_gt (reciprocalTerm_pos n))

/-- Adding zero does not change the accumulation points. -/
theorem derivedSet_reciprocalSet : derivedSet reciprocalSet = {0} := by
  rw [reciprocalSet, ← singleton_union, derivedSet_union,
    derivedSet_of_finite (finite_singleton 0), empty_union, derivedSet_reciprocalRange]

theorem reciprocalSet_countable : reciprocalSet.Countable :=
  (countable_range reciprocalTerm).insert 0

theorem reciprocalSet_infinite : reciprocalSet.Infinite :=
  (Set.infinite_range_of_injective reciprocalTerm_injective).mono (subset_insert _ _)

end Rudin.Chapter02
