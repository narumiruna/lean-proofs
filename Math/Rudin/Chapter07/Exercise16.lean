module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter07

/-- On a compact space, an equicontinuous pointwise convergent sequence converges uniformly.
The codomain may be any uniform space; in particular it may be real or complex. -/
theorem exercise16_uniform_convergence {K Y : Type*} [TopologicalSpace K]
    [CompactSpace K] [UniformSpace Y] {f : ℕ → K → Y} {g : K → Y}
    (he : Equicontinuous f) (hp : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformly f g atTop := by
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((he.tendsto_uniformFun_iff_pi atTop g).mpr (tendsto_pi_nhds.mpr hp))

/-- The compact-set formulation includes the empty set. -/
theorem exercise16_uniform_convergence_on {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {K : Set X} (hK : IsCompact K) {f : ℕ → X → Y} {g : X → Y}
    (he : Equicontinuous (fun n (x : K) => f n x))
    (hp : ∀ x ∈ K, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (exercise16_uniform_convergence he (fun x => hp x x.property))

end Rudin.Chapter07
