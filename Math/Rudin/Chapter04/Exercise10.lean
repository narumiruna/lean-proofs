module

public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter04

/-- Failure of uniform continuity supplies the two sequences in the source proof. -/
theorem exercise10_nonuniform_sequences {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (h : ¬ UniformContinuous f) :
    ∃ ε > 0, ∃ p q : ℕ → X,
      Tendsto (fun n => dist (p n) (q n)) atTop (𝓝 0) ∧
      ∀ n, ε < dist (f (p n)) (f (q n)) := by
  classical
  rw [Metric.uniformContinuous_iff] at h
  push Not at h
  obtain ⟨e, he, h⟩ := h
  have hex : ∀ n : ℕ, ∃ a b : X,
      dist a b < 1 / ((n : ℝ) + 1) ∧ e ≤ dist (f a) (f b) := by
    intro n
    exact h _ (by positivity)
  choose p q hpq using hex
  refine ⟨e / 2, by positivity, p, q, ?_, fun n => ?_⟩
  · exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hpq n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact lt_of_lt_of_le (by linarith) (hpq n).2

/-- The compact subsequence argument, rather than an appeal to the uniform continuity theorem. -/
theorem exercise10_compact_uniform_continuity {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y) (hf : Continuous f) : UniformContinuous f := by
  by_contra h
  obtain ⟨ε, hε, p, q, hpq, hsep⟩ := exercise10_nonuniform_sequences f h
  obtain ⟨x, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq p
  have hq : Tendsto (q ∘ φ) atTop (𝓝 x) :=
    hp.congr_dist (hpq.comp hφ.tendsto_atTop)
  have hd : Tendsto (fun n => dist (f (p (φ n))) (f (q (φ n)))) atTop (𝓝 0) := by
    simpa using (hf.continuousAt.tendsto.comp hp).dist (hf.continuousAt.tendsto.comp hq)
  have hevent := hd.eventually_lt_const hε
  obtain ⟨n, hn⟩ := hevent.exists
  exact (not_lt_of_ge (hsep (φ n)).le) hn

end Rudin.Chapter04
