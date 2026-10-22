module

public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open Filter Set Metric
open scoped Topology

namespace Rudin.Chapter03

/-- Nonempty nested closed bounded sets of vanishing diameter in a complete
metric space have a common point. Indices start at zero. -/
theorem exercise21_intersection_exists {X : Type*} [MetricSpace X] [CompleteSpace X]
    (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n)) (hne : ∀ n, (E n).Nonempty)
    (hb : ∀ n, Bornology.IsBounded (E n)) (hnest : ∀ n, E (n + 1) ⊆ E n)
    (hd : Tendsto (fun n => diam (E n)) atTop (𝓝 0)) :
    (⋂ n, E n).Nonempty := by
  have ha : Antitone E := antitone_nat_of_succ_le hnest
  apply nonempty_iInter_of_nonempty_biInter hc hb _ hd
  intro N
  obtain ⟨x, hx⟩ := hne N
  exact ⟨x, mem_iInter.mpr fun n => mem_iInter.mpr fun hn => ha hn hx⟩

/-- Vanishing diameter gives uniqueness, without a completeness assumption. -/
theorem exercise21_intersection_unique {X : Type*} [MetricSpace X]
    (E : ℕ → Set X) (hb : ∀ n, Bornology.IsBounded (E n))
    (hd : Tendsto (fun n => diam (E n)) atTop (𝓝 0)) :
    (⋂ n, E n).Subsingleton := by
  intro x hx y hy
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have h : ∀ n, dist x y ≤ diam (E n) := fun n =>
    dist_le_diam_of_mem (hb n) (mem_iInter.mp hx n) (mem_iInter.mp hy n)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hd (Eventually.of_forall h)

/-- The source conclusion: the intersection consists of exactly one point. -/
theorem exercise21_singleton {X : Type*} [MetricSpace X] [CompleteSpace X]
    (E : ℕ → Set X) (hc : ∀ n, IsClosed (E n)) (hne : ∀ n, (E n).Nonempty)
    (hb : ∀ n, Bornology.IsBounded (E n)) (hnest : ∀ n, E (n + 1) ⊆ E n)
    (hd : Tendsto (fun n => diam (E n)) atTop (𝓝 0)) :
    ∃ x, (⋂ n, E n) = {x} := by
  obtain ⟨x, hx⟩ := exercise21_intersection_exists E hc hne hb hnest hd
  exact ⟨x, (exercise21_intersection_unique E hb hd).eq_singleton_of_mem hx⟩

end Rudin.Chapter03
