module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# R09E01: the set of finite linear combinations is a vector space

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 9.1, book page 239 (PDF page 248); definition in Section 9.1,
book page 204.

We use an arbitrary vector space over a field, which includes Rudin's real
Euclidean spaces. `finiteLinearCombinations` is the explicit set in the source,
not a definition by `Submodule.span`. A finite set of vectors and a coefficient
function describe a finite linear combination; repeated vectors can be collected
by adding their coefficients. Empty sums are allowed. For a nonempty generating
set, they add no new vector, since zero is also a one-term combination.

The membership theorem proves the bridge to Mathlib's span. The submodule
construction equips exactly this set with the inherited vector space structure.
The final theorem states the nonemptiness and both closure properties in
Rudin's definition of a vector space (Section 9.1(a)).
-/

@[expose] public section

namespace Rudin.Chapter09

variable (K : Type*) {X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- All finite linear combinations of vectors in `S`. -/
def finiteLinearCombinations (S : Set X) : Set X :=
  {x | ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    ∃ c : X → K, ∑ y ∈ t, c y • y = x}

/-- The explicit finite-combination set agrees with Mathlib's span. -/
theorem mem_finiteLinearCombinations_iff (S : Set X) (x : X) :
    x ∈ finiteLinearCombinations K S ↔ x ∈ Submodule.span K S := by
  constructor
  · rintro ⟨t, ht, c, rfl⟩
    exact Submodule.sum_mem _ fun y hy =>
      Submodule.smul_mem _ _ (Submodule.subset_span (ht hy))
  · intro hx
    obtain ⟨c, t, ht, _, hc⟩ :=
      Submodule.mem_span_iff_exists_finset_subset.mp hx
    exact ⟨t, ht, c, hc⟩

/-- The vector space structure on the explicit finite-combination set. -/
def finiteCombinationSubmodule (S : Set X) : Submodule K X where
  carrier := finiteLinearCombinations K S
  zero_mem' := (mem_finiteLinearCombinations_iff K S 0).mpr (Submodule.zero_mem _)
  add_mem' := fun hx hy => (mem_finiteLinearCombinations_iff K S _).mpr
    (Submodule.add_mem _ ((mem_finiteLinearCombinations_iff K S _).mp hx)
      ((mem_finiteLinearCombinations_iff K S _).mp hy))
  smul_mem' := fun c _ hx => (mem_finiteLinearCombinations_iff K S _).mpr
    (Submodule.smul_mem _ c ((mem_finiteLinearCombinations_iff K S _).mp hx))

/-- The span of a nonempty set satisfies Rudin's vector space definition. -/
theorem exercise01 (S : Set X) (hS : S.Nonempty) :
    (finiteLinearCombinations K S).Nonempty ∧
      (∀ x ∈ finiteLinearCombinations K S, ∀ y ∈ finiteLinearCombinations K S,
        x + y ∈ finiteLinearCombinations K S) ∧
      (∀ (c : K) (x : X), x ∈ finiteLinearCombinations K S →
        c • x ∈ finiteLinearCombinations K S) := by
  obtain ⟨s, hs⟩ := hS
  refine ⟨⟨s, (mem_finiteLinearCombinations_iff K S s).mpr
    (Submodule.subset_span hs)⟩, ?_, ?_⟩
  · intro x hx y hy
    exact (finiteCombinationSubmodule K S).add_mem hx hy
  · intro c x hx
    exact (finiteCombinationSubmodule K S).smul_mem c hx

end Rudin.Chapter09
