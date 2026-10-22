module

public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open Set Metric
open scoped ENNReal

namespace Rudin.Chapter04

/-- The extension of the source diameter: zero for the empty set, top if unbounded. -/
noncomputable def exercise09_diameter {X : Type*} [MetricSpace X] (E : Set X) : ℝ≥0∞ :=
  Metric.ediam E

theorem exercise09_diameter_empty {X : Type*} [MetricSpace X] :
    exercise09_diameter (∅ : Set X) = 0 := Metric.ediam_empty

theorem exercise09_diameter_unbounded {X : Type*} [MetricSpace X]
    (E : Set X) (hE : ¬ Bornology.IsBounded E) :
    exercise09_diameter E = ⊤ := Metric.ediam_of_unbounded hE

/-- On a nonempty bounded set, the extension is the real supremum of pairwise distances. -/
theorem exercise09_diameter_agrees {X : Type*} [MetricSpace X]
    (E : Set X) (hne : E.Nonempty) (hb : Bornology.IsBounded E) :
    exercise09_diameter E = ENNReal.ofReal (sSup {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}) := by
  have hlub : IsLUB {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} (Metric.diam E) := by
    refine ⟨?_, ?_⟩
    · rintro r ⟨x, hx, y, hy, rfl⟩
      exact Metric.dist_le_diam_of_mem hb hx hy
    · intro b h
      exact Metric.diam_le_of_forall_dist_le_of_nonempty hne
        (fun x hx y hy => h ⟨x, hx, y, hy, rfl⟩)
  have hdist : ({r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨dist x x, x, hx, x, hx, rfl⟩
  rw [hlub.csSup_eq hdist, exercise09_diameter, Metric.diam]
  exact (ENNReal.ofReal_toReal hb.ediam_ne_top).symm

/-- Uniform continuity controls the extended diameters of all subsets, including empty ones. -/
theorem exercise09_uniform_to_diameter {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : UniformContinuous f) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ E : Set X, exercise09_diameter E < ENNReal.ofReal δ →
        exercise09_diameter (f '' E) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun E hE => ?_⟩
  have hb : ediam (f '' E) ≤ ENNReal.ofReal (ε / 2) := by
    apply Metric.ediam_le_of_forall_dist_le
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    apply (hd ?_).le
    have hxy := lt_of_le_of_lt (Metric.edist_le_ediam_of_mem hx hy) hE
    rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ] at hxy
  exact hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))

/-- Two-point sets recover the usual uniform continuity condition. -/
theorem exercise09_diameter_to_uniform {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y)
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ E : Set X, exercise09_diameter E < ENNReal.ofReal δ →
        exercise09_diameter (f '' E) < ENNReal.ofReal ε) :
    UniformContinuous f := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h ε hε
  refine ⟨δ, hδ, fun {x y} hxy => ?_⟩
  have hp : exercise09_diameter ({x, y} : Set X) < ENNReal.ofReal δ := by
    simpa [exercise09_diameter, Metric.ediam_pair, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hδ] using hxy
  have hi := hd {x, y} hp
  have hx : f x ∈ f '' ({x, y} : Set X) := mem_image_of_mem _ (by simp)
  have hy : f y ∈ f '' ({x, y} : Set X) := mem_image_of_mem _ (by simp)
  have := lt_of_le_of_lt (Metric.edist_le_ediam_of_mem hx hy) hi
  rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at this

end Rudin.Chapter04
