module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# R02E20: closure and interior of a connected set

Source: Rudin, Third Edition, book 44 (PDF 53).
Rudin's connectedness convention is `IsPreconnected`: the empty set is allowed.
Closure preserves this property in every topological space. Interior does not:
in the Euclidean plane, take the two open half-planes x ≠ 0 and add the origin.
This set is star-convex at the origin. Its interior consists of the two
half-planes and is not even preconnected.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Topology

/-- This includes the empty set and is stronger than the metric-space version. -/
theorem exercise20_closure_connected {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsPreconnected S) : IsPreconnected (closure S) :=
  hS.closure

/-- Two open half-planes joined only at the origin, in the Euclidean plane. -/
def exercise20_example : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ≠ 0 ∨ p = 0}

theorem exercise20_example_connected : IsConnected exercise20_example := by
  have hs : StarConvex ℝ (0 : EuclideanSpace ℝ (Fin 2)) exercise20_example := by
    intro y hy a b ha hb hab
    simp only [smul_zero, zero_add]
    by_cases hb0 : b = 0
    · subst b
      exact Or.inr (zero_smul ℝ y)
    · rcases hy with hy | rfl
      · apply Or.inl
        change b * y 0 ≠ 0
        exact mul_ne_zero hb0 hy
      · exact Or.inr (smul_zero b)
  exact (hs.isPathConnected (Or.inr rfl)).isConnected

theorem exercise20_example_interior :
    interior exercise20_example = {p : EuclideanSpace ℝ (Fin 2) | p 0 ≠ 0} := by
  have hz : (0 : EuclideanSpace ℝ (Fin 2)) ∉ interior exercise20_example := by
    let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t => t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
    have hf : Continuous f := continuous_id.smul continuous_const
    have hp : f ⁻¹' exercise20_example = {0} := by
      ext t
      simp [f, exercise20_example, PiLp.smul_apply,
        smul_eq_zero, PiLp.single_eq_zero_iff]
    intro h
    have h' : (0 : ℝ) ∈ interior (f ⁻¹' exercise20_example) :=
      preimage_interior_subset_interior_preimage hf (by simpa [f] using h)
    simp [hp, interior_singleton] at h'
  apply Set.Subset.antisymm
  · intro p hp
    rcases interior_subset hp with h | rfl
    · exact h
    · exact (hz hp).elim
  · apply interior_maximal
    · intro p hp
      exact Or.inl hp
    · exact isOpen_ne_fun (PiLp.continuous_apply 2 _ 0) continuous_const

/-- The interior has points on both sides of x = 0 but no point on x = 0. -/
theorem exercise20_example_interior_not_preconnected :
    ¬ IsPreconnected (interior exercise20_example) := by
  intro hs
  have hn : EuclideanSpace.single (0 : Fin 2) (-1 : ℝ) ∈
      interior exercise20_example := by
    rw [exercise20_example_interior]
    simp
  have hp : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈
      interior exercise20_example := by
    rw [exercise20_example_interior]
    simp
  have hz : (0 : ℝ) ∈ (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ''
      interior exercise20_example :=
    hs.intermediate_value hn hp (PiLp.continuous_apply 2 _ 0).continuousOn
      (by norm_num)
  obtain ⟨p, hpi, hp0⟩ := hz
  rw [exercise20_example_interior] at hpi
  exact hpi hp0

/-- An explicit witness for the negative answer to the interior question. -/
theorem exercise20_interior_counterexample :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
      IsConnected S ∧ ¬ IsPreconnected (interior S) :=
  ⟨exercise20_example, exercise20_example_connected,
    exercise20_example_interior_not_preconnected⟩

end Rudin.Chapter02
