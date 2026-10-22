module

public import Math.Rudin.Chapter02.Exercise12
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# R02E05: a bounded set with exactly three accumulation points

Source: Rudin, Exercise 2.5, book page 43 (PDF page 52).
Use three translates of the positive reciprocal sequence, with limits 0, 2, 4.
-/

@[expose] public section

open Set Filter Topology

namespace Rudin.Chapter02

/-- Three reciprocal sequences tending to 0, 2, and 4. -/
def threeLimitSet : Set ℝ :=
  range reciprocalTerm ∪ range (fun n => 2 + reciprocalTerm n) ∪
    range (fun n => 4 + reciprocalTerm n)

/-- A translate of the reciprocal sequence has precisely its translation as limit point. -/
theorem derivedSet_translated_reciprocalRange (a : ℝ) :
    derivedSet (range (fun n => a + reciprocalTerm n)) = {a} := by
  have ht : Tendsto (fun n => a + reciprocalTerm n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add reciprocalTerm_tendsto
  apply Subset.antisymm (derivedSet_range_subset_limit ht)
  rintro x (rfl : x = a)
  exact limit_mem_derivedSet_range ht (fun n => by
    have := reciprocalTerm_pos n
    linarith)

/-- There are no accumulation points other than the three specified ones. -/
theorem derivedSet_threeLimitSet : derivedSet threeLimitSet = {0, 2, 4} := by
  rw [threeLimitSet, derivedSet_union, derivedSet_union,
    derivedSet_reciprocalRange, derivedSet_translated_reciprocalRange,
    derivedSet_translated_reciprocalRange]
  ext x
  simp only [mem_union, mem_singleton_iff, mem_insert_iff]
  tauto

/-- The construction lies in the bounded interval [0, 5]. -/
theorem threeLimitSet_subset : threeLimitSet ⊆ Icc 0 5 := by
  have hb (n : ℕ) : 0 < reciprocalTerm n ∧ reciprocalTerm n ≤ 1 := by
    refine ⟨reciprocalTerm_pos n, ?_⟩
    dsimp [reciprocalTerm]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  rintro x ((⟨n, rfl⟩ | ⟨n, rfl⟩) | ⟨n, rfl⟩) <;>
    have := hb n <;> constructor <;> linarith

theorem threeLimitSet_bounded : Bornology.IsBounded threeLimitSet :=
  (Metric.isBounded_Icc 0 5).subset threeLimitSet_subset

/-- The exact derived set has three distinct elements. -/
theorem threeLimitSet_derived_ncard : (derivedSet threeLimitSet).ncard = 3 := by
  rw [derivedSet_threeLimitSet]
  norm_num

/-- The explicit bounded set has exactly the three limit points 0, 2, and 4. -/
theorem exercise05 : Bornology.IsBounded threeLimitSet ∧
    derivedSet threeLimitSet = {0, 2, 4} ∧ (derivedSet threeLimitSet).ncard = 3 :=
  ⟨threeLimitSet_bounded, derivedSet_threeLimitSet, threeLimitSet_derived_ncard⟩

end Rudin.Chapter02
