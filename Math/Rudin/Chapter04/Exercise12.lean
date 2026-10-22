module

public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section
namespace Rudin.Chapter04

/-- The composition of uniformly continuous maps between metric spaces is uniformly continuous. -/
theorem exercise12_composition {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
    [MetricSpace Z] {f : X → Y} {g : Y → Z}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (g ∘ f) :=
  hg.comp hf

end Rudin.Chapter04
