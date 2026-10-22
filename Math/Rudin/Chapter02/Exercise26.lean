module

public import Math.Rudin.Chapter02.Exercise24

/-!
# R02E26: compactness from accumulation points

Source: Rudin, Third Edition, book page 45 (PDF page 54).
The conclusion is the finite-subcover property for an arbitrary indexed
open cover, including covers of an empty space.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Filter Topology

theorem exercise26 {X : Type*} [MetricSpace X]
    (h : ∀ E : Set X, E.Infinite → ∃ x : X, AccPt x (𝓟 E))
    {ι : Type*} (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i :=
  (compact_of_infinite_accumulation h).elim_finite_subcover U ho hcover

end Rudin.Chapter02
