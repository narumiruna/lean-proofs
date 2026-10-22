module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- The distances of two Cauchy sequences have a finite real limit.
Only the real numbers, not the ambient metric space, need to be complete. -/
theorem exercise23_distance_limit {X : Type*} [MetricSpace X]
    {p q : ℕ → X} (hp : CauchySeq p) (hq : CauchySeq q) :
    ∃ d : ℝ, Tendsto (fun n => dist (p n) (q n)) atTop (𝓝 d) := by
  apply cauchySeq_tendsto_of_complete
  exact uniformContinuous_dist.comp_cauchySeq (hp.prodMk hq)

end Rudin.Chapter03
