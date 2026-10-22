module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter04

/-- The graph of a continuous map on a compact metric domain is compact. -/
theorem exercise06_continuous_graph_compact {E Y : Type*} [MetricSpace E]
    [CompactSpace E] [MetricSpace Y] {f : E → Y} (hf : Continuous f) :
    IsCompact (range (fun x => (x, f x))) :=
  isCompact_range (continuous_id.prodMk hf)

/-- A compact graph forces continuity; no continuity hypothesis is used here. -/
theorem exercise06_compact_graph_continuous {E Y : Type*} [MetricSpace E]
    [MetricSpace Y] {f : E → Y}
    (h : IsCompact (range (fun x => (x, f x)))) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro F hF
  have hc := (h.inter_right (hF.preimage continuous_snd)).image continuous_fst
  have heq : Prod.fst '' (range (fun x => (x, f x)) ∩ Prod.snd ⁻¹' F) = f ⁻¹' F := by
    ext x
    constructor
    · rintro ⟨p, ⟨⟨y, rfl⟩, hy⟩, rfl⟩
      exact hy
    · intro hx
      exact ⟨(x, f x), ⟨⟨x, rfl⟩, hx⟩, rfl⟩
  rw [heq] at hc
  exact hc.isClosed

/-- Both directions of the source equivalence, including an empty domain. -/
theorem exercise06_graph_equivalence {E Y : Type*} [MetricSpace E]
    [CompactSpace E] [MetricSpace Y] (f : E → Y) :
    Continuous f ↔ IsCompact (range (fun x => (x, f x))) :=
  ⟨exercise06_continuous_graph_compact, exercise06_compact_graph_continuous⟩

end Rudin.Chapter04
