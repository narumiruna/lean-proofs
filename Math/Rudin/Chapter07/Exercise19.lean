module

public import Mathlib

@[expose] public section

open Set Filter Topology
open scoped Topology

namespace Rudin.Chapter07

/-- Compact families are equicontinuous. No nonempty hypothesis is used. -/
theorem exercise19_necessity_equicontinuous {K Y : Type*} [MetricSpace K]
    [CompactSpace K] [MetricSpace Y] {S : Set C(K, Y)} (hS : IsCompact S) :
    Equicontinuous (fun f : S => (f.val : K → Y)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let e : K → C(S, Y) := fun x => ⟨fun f => f.val x,
    (continuous_eval_const x).comp continuous_subtype_val⟩
  have he : Continuous e := ContinuousMap.continuous_of_continuous_uncurry e
    ((continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)).comp continuous_swap)
  exact equicontinuous_iff_continuous.mpr
    ((ContinuousMap.continuous_iff_continuous_uniformFun e).mp he)

/-- Compact families are closed for the supremum metric. -/
theorem exercise19_necessity_closed {K Y : Type*} [TopologicalSpace K]
    [MetricSpace Y] {S : Set C(K, Y)} (hS : IsCompact S) : IsClosed S :=
  hS.isClosed

/-- Every evaluation image of a compact family is bounded. -/
theorem exercise19_necessity_bounded {K Y : Type*} [TopologicalSpace K]
    [MetricSpace Y] {S : Set C(K, Y)} (hS : IsCompact S) (x : K) :
    Bornology.IsBounded ((fun f : C(K, Y) => f x) '' S) :=
  (hS.image (continuous_eval_const x)).isBounded

/-- Pointwise bounded equicontinuous families have compact closure. -/
theorem exercise19_compact_closure {K Y : Type*} [MetricSpace K] [CompactSpace K]
    [MetricSpace Y] [ProperSpace Y] {S : Set C(K, Y)}
    (hb : ∀ x, Bornology.IsBounded ((fun f : C(K, Y) => f x) '' S))
    (he : Equicontinuous (fun f : S => (f.val : K → Y))) : IsCompact (closure S) := by
  let : T2Space (UniformOnFun K Y {s : Set K | IsCompact s}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have h := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun f : C(K, Y) => (f : K → Y))
    (𝔖 := {s : Set K | IsCompact s}) (fun _ hs => hs)
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    (fun s _ => he.equicontinuousOn s)
    (fun _ _ x _ => ⟨closure ((fun f : C(K, Y) => f x) '' S),
      (hb x).isCompact_closure, fun f hf => subset_closure ⟨f, hf, rfl⟩⟩)
  exact h

/-- Closed, pointwise bounded, equicontinuous families are compact.
Proper metric codomains include both real and complex scalars. -/
theorem exercise19_sufficiency {K Y : Type*} [MetricSpace K] [CompactSpace K]
    [MetricSpace Y] [ProperSpace Y] {S : Set C(K, Y)}
    (hc : IsClosed S)
    (hb : ∀ x, Bornology.IsBounded ((fun f : C(K, Y) => f x) '' S))
    (he : Equicontinuous (fun f : S => (f.val : K → Y))) : IsCompact S := by
  simpa only [hc.closure_eq] using exercise19_compact_closure hb he

/-- The full Ascoli equivalence, including empty domains and empty families. -/
theorem exercise19_ascoli_iff {K Y : Type*} [MetricSpace K] [CompactSpace K]
    [MetricSpace Y] [ProperSpace Y] (S : Set C(K, Y)) :
    IsCompact S ↔ IsClosed S ∧
      (∀ x, Bornology.IsBounded ((fun f : C(K, Y) => f x) '' S)) ∧
      Equicontinuous (fun f : S => (f.val : K → Y)) := by
  exact ⟨fun h => ⟨exercise19_necessity_closed h, exercise19_necessity_bounded h,
    exercise19_necessity_equicontinuous h⟩,
    fun ⟨hc, hb, he⟩ => exercise19_sufficiency hc hb he⟩

end Rudin.Chapter07
