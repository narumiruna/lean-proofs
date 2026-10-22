module

public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

@[expose] public section
namespace Rudin.Chapter04
open Set Filter Topology

/-- Uniform continuity sends every Cauchy sequence to a Cauchy sequence. -/
theorem exercise11_cauchy_images {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : UniformContinuous f) {u : ℕ → X} (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := hf.comp_cauchySeq hu

/-- Density supplies an actual sequence in the subset tending to each ambient point. -/
theorem exercise11_approximating_sequence {X : Type*} [MetricSpace X]
    {E : Set X} (hE : Dense E) (x : X) :
    ∃ u : ℕ → E, Tendsto (fun n => (u n : X)) atTop (𝓝 x) := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp (hE x)
  exact ⟨fun n => ⟨u n, hu n⟩, ht⟩

/-- Fix one approximating sequence at every point. No recursion is used. -/
noncomputable def exercise11Approx {X : Type*} [MetricSpace X]
    {E : Set X} (hE : Dense E) (x : X) : ℕ → E :=
  Classical.choose (exercise11_approximating_sequence hE x)

theorem exercise11_approx_tendsto {X : Type*} [MetricSpace X]
    {E : Set X} (hE : Dense E) (x : X) :
    Tendsto (fun n => (exercise11Approx hE x n : X)) atTop (𝓝 x) :=
  Classical.choose_spec (exercise11_approximating_sequence hE x)

/-- A convergent ambient approximating sequence is Cauchy in the subset; its image
is Cauchy, and completeness supplies its limit. -/
theorem exercise11_image_limit {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} {f : E → Y} (hf : UniformContinuous f)
    {u : ℕ → E} {x : X} (hu : Tendsto (fun n => (u n : X)) atTop (𝓝 x)) :
    ∃ y, Tendsto (f ∘ u) atTop (𝓝 y) := by
  have hc : CauchySeq u :=
    Metric.cauchySeq_iff.mpr ((Metric.cauchySeq_iff (u := fun n => (u n : X))).mp hu.cauchySeq)
  exact cauchySeq_tendsto_of_complete (exercise11_cauchy_images hf hc)

/-- Sequence comparison: any two approximations to the same point have the same
image limit. This proves independence of all the sequence choices. -/
theorem exercise11_compare_sequences {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {E : Set X} {f : E → Y} (hf : UniformContinuous f)
    {u v : ℕ → E} {x : X} {a b : Y}
    (hu : Tendsto (fun n => (u n : X)) atTop (𝓝 x))
    (hv : Tendsto (fun n => (v n : X)) atTop (𝓝 x))
    (ha : Tendsto (f ∘ u) atTop (𝓝 a)) (hb : Tendsto (f ∘ v) atTop (𝓝 b)) : a = b := by
  have hzero : Tendsto (fun n => dist (f (u n)) (f (v n))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hf ε hε
    have hd : Tendsto (fun n => dist (u n : X) (v n : X)) atTop (𝓝 0) := by
      simpa using hu.dist hv
    filter_upwards [hd.eventually (gt_mem_nhds hδ)] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hmod hn
  exact dist_eq_zero.mp (tendsto_nhds_unique (ha.dist hb) hzero)

/-- The extension is constructed as the limit of the Cauchy image of the chosen sequence. -/
noncomputable def exercise11Extension {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} (hE : Dense E) (f : E → Y)
    (hf : UniformContinuous f) (x : X) : Y :=
  Classical.choose (exercise11_image_limit hf (exercise11_approx_tendsto hE x))

theorem exercise11_extension_limit {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} (hE : Dense E) {f : E → Y}
    (hf : UniformContinuous f) (x : X) :
    Tendsto (f ∘ exercise11Approx hE x) atTop (𝓝 (exercise11Extension hE f hf x)) :=
  Classical.choose_spec (exercise11_image_limit hf (exercise11_approx_tendsto hE x))

/-- Comparing with the constant sequence proves agreement on the original domain. -/
theorem exercise11_extension_eq {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} (hE : Dense E) {f : E → Y}
    (hf : UniformContinuous f) (x : E) : exercise11Extension hE f hf x = f x := by
  exact exercise11_compare_sequences hf (exercise11_approx_tendsto hE x)
    (u := exercise11Approx hE x) (v := fun _ => x) tendsto_const_nhds
    (exercise11_extension_limit hE hf x) tendsto_const_nhds

/-- The sequence construction is uniformly continuous, by passing the original
uniform estimate to the limits of two approximating sequences. -/
theorem exercise11_extension_uniformContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} (hE : Dense E) {f : E → Y}
    (hf : UniformContinuous f) : UniformContinuous (exercise11Extension hE f hf) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hd := (exercise11_approx_tendsto hE x).dist (exercise11_approx_tendsto hE y)
  have hevent : ∀ᶠ n in atTop,
      dist (f (exercise11Approx hE x n)) (f (exercise11Approx hE y n)) ≤ ε / 2 := by
    filter_upwards [hd.eventually (gt_mem_nhds hxy)] with n hn
    exact (hmod hn).le
  have hle := le_of_tendsto
    ((exercise11_extension_limit hE hf x).dist (exercise11_extension_limit hE hf y)) hevent
  exact lt_of_le_of_lt hle (by linarith)

/-- Exercise 11's alternative proof of Exercise 13, through Cauchy images and
completeness of the real numbers. It also covers the empty ambient space. -/
theorem exercise11_extension_via_sequences {X : Type*} [MetricSpace X]
    {E : Set X} (hE : Dense E) (f : E → ℝ) (hf : UniformContinuous f) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x : E, g x = f x :=
  ⟨exercise11Extension hE f hf, (exercise11_extension_uniformContinuous hE hf).continuous,
    exercise11_extension_eq hE hf⟩

end Rudin.Chapter04
