module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# R02E07: closure and unions

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.7, book page 43 (PDF page 52).

Part (a) also holds for `n = 0`, when the union is empty. Part (b) uses
`A (n + 1)` to retain the source's positive indexing. The strict example is
`A i = {1 / i}` in the real line: zero is a new closure point of the union,
but belongs to none of the singleton closures.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- Closure commutes with the finite union indexed by `1 ≤ i ≤ n`. -/
theorem exercise07a {X : Type*} [MetricSpace X] (A : ℕ → Set X) (n : ℕ) :
    closure (⋃ i ∈ Finset.Icc 1 n, A i) =
      ⋃ i ∈ Finset.Icc 1 n, closure (A i) :=
  Finset.closure_biUnion _ _

/-- Each individual closure is contained in the closure of the countable union. -/
theorem exercise07b_inclusion {X : Type*} [MetricSpace X] (A : ℕ → Set X) :
    (⋃ n : ℕ, closure (A (n + 1))) ⊆ closure (⋃ n : ℕ, A (n + 1)) := by
  refine Set.iUnion_subset fun n => closure_mono ?_
  exact Set.subset_iUnion (fun k : ℕ => A (k + 1)) n

/-- A countable union of closed singleton sets can have a new closure point. -/
theorem exercise07b_strict :
    (⋃ n : ℕ, closure ({1 / ((n + 1 : ℕ) : ℝ)} : Set ℝ)) ⊂
      closure (⋃ n : ℕ, ({1 / ((n + 1 : ℕ) : ℝ)} : Set ℝ)) := by
  refine Set.ssubset_iff_subset_ne.2 ⟨exercise07b_inclusion
    (fun i => ({1 / (i : ℝ)} : Set ℝ)), ?_⟩
  intro heq
  have hzero : (0 : ℝ) ∈ closure
      (⋃ n : ℕ, ({1 / ((n + 1 : ℕ) : ℝ)} : Set ℝ)) := by
    apply mem_closure_of_tendsto
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
            Filter.atTop (nhds 0)))
    exact Filter.Eventually.of_forall fun n =>
      Set.mem_iUnion.2 ⟨n, by simp only [Set.mem_singleton_iff, Nat.cast_add, Nat.cast_one]⟩
  rw [← heq] at hzero
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hzero
  rw [closure_singleton, Set.mem_singleton_iff] at hn
  exact (one_div_ne_zero (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)) hn.symm

end Rudin.Chapter02
