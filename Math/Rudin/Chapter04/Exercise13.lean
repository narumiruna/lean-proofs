module

public import Math.Rudin.Chapter04.Exercise11
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section
namespace Rudin.Chapter04
open Set Topology

/-- The requested real extension. The construction in Exercise 11 also proves uniform continuity. -/
theorem exercise13_real_extension {X : Type*} [MetricSpace X] {E : Set X}
    (hE : Dense E) (f : E → ℝ) (hf : UniformContinuous f) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x : E, g x = f x :=
  exercise11_extension_via_sequences hE f hf

/-- Continuous extensions from a dense subset are unique, for any metric target. -/
theorem exercise13_uniqueness {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {E : Set X} (hE : Dense E) {f : E → Y} {g h : X → Y}
    (hg : Continuous g) (hh : Continuous h)
    (hgf : ∀ x : E, g x = f x) (hhf : ∀ x : E, h x = f x) : g = h := by
  apply hg.ext_on hE hh
  intro x hx
  exact (hgf ⟨x, hx⟩).trans (hhf ⟨x, hx⟩).symm

/-- Every complete metric range admits an extension. No nonemptiness assumption is needed. -/
theorem exercise13_complete_range {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompleteSpace Y] {E : Set X} (hE : Dense E) (f : E → Y)
    (hf : UniformContinuous f) :
    ∃ g : X → Y, UniformContinuous g ∧ (∀ x : E, g x = f x) ∧
      ∀ h : X → Y, Continuous h → (∀ x : E, h x = f x) → h = g := by
  refine ⟨exercise11Extension hE f hf, exercise11_extension_uniformContinuous hE hf,
    exercise11_extension_eq hE hf, ?_⟩
  intro h hh heq
  exact exercise13_uniqueness hE hh
    (exercise11_extension_uniformContinuous hE hf).continuous heq (exercise11_extension_eq hE hf)

/-- In particular the answer is yes for every Euclidean space, including dimension zero. -/
theorem exercise13_euclidean_range {X : Type*} [MetricSpace X] {E : Set X}
    (hE : Dense E) (k : ℕ) (f : E → EuclideanSpace ℝ (Fin k))
    (hf : UniformContinuous f) :
    ∃ g : X → EuclideanSpace ℝ (Fin k), Continuous g ∧ ∀ x : E, g x = f x := by
  obtain ⟨g, hg, heq, _⟩ := exercise13_complete_range hE f hf
  exact ⟨g, hg.continuous, heq⟩

/-- The answer is yes for every compact metric range. -/
theorem exercise13_compact_range {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace Y] {E : Set X} (hE : Dense E) (f : E → Y)
    (hf : UniformContinuous f) :
    ∃ g : X → Y, Continuous g ∧ ∀ x : E, g x = f x := by
  obtain ⟨g, hg, heq, _⟩ := exercise13_complete_range hE f hf
  exact ⟨g, hg.continuous, heq⟩

/-- The punctured real line is the counterexample range and the dense domain subset. -/
def exercise13Punctured : Set ℝ := {(0 : ℝ)}ᶜ

theorem exercise13_punctured_dense : Dense exercise13Punctured :=
  dense_compl_singleton 0

theorem exercise13_punctured_not_complete : ¬ CompleteSpace exercise13Punctured := by
  intro hc
  have hclosed := (completeSpace_coe_iff_isComplete.mp hc).isClosed
  have hz : (0 : ℝ) ∈ exercise13Punctured := by
    rw [← hclosed.closure_eq]
    exact exercise13_punctured_dense 0
  exact hz rfl

/-- The identity on the punctured line cannot extend continuously across zero while
keeping its values in the punctured line. -/
theorem exercise13_punctured_no_extension :
    ¬ ∃ g : ℝ → exercise13Punctured, Continuous g ∧ ∀ x : exercise13Punctured, g x = x := by
  rintro ⟨g, hg, heq⟩
  have hid : (fun x => (g x : ℝ)) = id := by
    apply (continuous_subtype_val.comp hg).ext_on exercise13_punctured_dense continuous_id
    intro x hx
    exact congrArg Subtype.val (heq ⟨x, hx⟩)
  have hz : (g 0 : ℝ) = 0 := congrFun hid 0
  exact (g 0).property hz

/-- Thus the answer for arbitrary metric ranges is no: the dense-domain identity
is uniformly continuous but has no continuous extension, and its range is not complete. -/
theorem exercise13_arbitrary_range :
    Dense exercise13Punctured ∧
      UniformContinuous (id : exercise13Punctured → exercise13Punctured) ∧
      ¬ CompleteSpace exercise13Punctured ∧
      ¬ ∃ g : ℝ → exercise13Punctured, Continuous g ∧
        ∀ x : exercise13Punctured, g x = id x :=
  ⟨exercise13_punctured_dense, uniformContinuous_id,
    exercise13_punctured_not_complete, exercise13_punctured_no_extension⟩

end Rudin.Chapter04
