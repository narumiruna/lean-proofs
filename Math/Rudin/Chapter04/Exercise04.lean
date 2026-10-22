module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter04

/-- Density is asserted in the actual range subtype, not in the ambient codomain. -/
theorem exercise04_image_density {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) {E : Set X} (hE : Dense E) :
    Dense ((fun x : X => (⟨f x, mem_range_self x⟩ : Set.range f)) '' E) := by
  let F : X → Set.range f := fun x => ⟨f x, mem_range_self x⟩
  have hF : Continuous F := hf.subtype_mk _
  have hsurj : Function.Surjective F := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact hsurj.denseRange.dense_image hF hE

/-- Continuous functions agreeing on a dense subset agree everywhere. -/
theorem exercise04_dense_uniqueness {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    {E : Set X} (hE : Dense E) (h : EqOn f g E) : f = g := by
  funext x
  exact closure_minimal h (isClosed_eq hf hg) (hE x)

end Rudin.Chapter04
