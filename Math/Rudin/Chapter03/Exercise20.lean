module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- A Cauchy sequence with a subsequence converging in the original space converges
in that space. No completeness assumption is needed. -/
theorem exercise20_full_convergence {X : Type*} [MetricSpace X]
    {p : ℕ → X} (hp : CauchySeq p) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {x : X} (hx : Tendsto (p ∘ φ) atTop (𝓝 x)) : Tendsto p atTop (𝓝 x) :=
  tendsto_nhds_of_cauchySeq_of_subseq hp hφ.tendsto_atTop hx

end Rudin.Chapter03
