module

public import Math.Rudin.Chapter03.Exercise24
public import Mathlib.Topology.Instances.Rat

/-!
# Rudin, Chapter 3, Exercise 25

The domain of the identification is exactly the quotient of rational Cauchy
sequences constructed in Exercise 24, with its limit-distance metric.
The identification sends each constant-sequence class to the usual real
value of that rational number.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Rudin.Chapter03

/-- The usual embedding preserves the metric specified by the source. -/
theorem exercise25_rat_isometry : Isometry ((↑) : ℚ → ℝ) :=
  Isometry.of_dist_eq Rat.dist_cast

/-- A real-valued map on the actual Cauchy-sequence quotient of Exercise 24. -/
def exercise25_toReal (p : Exercise24.Completion ℚ) : ℝ :=
  UniformSpace.Completion.extension ((↑) : ℚ → ℝ) (Exercise24.toCompletion p)

theorem exercise25_toReal_isometry : Isometry exercise25_toReal :=
  exercise25_rat_isometry.completion_extension.comp Exercise24.toCompletion_isometry

/-- Compatibility with the constant-sequence embedding, not just an abstract
isometry between two complete spaces. -/
@[simp] theorem exercise25_toReal_embed (q : ℚ) :
    exercise25_toReal (Exercise24.embed q) = (q : ℝ) := by
  unfold exercise25_toReal
  rw [Exercise24.toCompletion_embed,
    UniformSpace.Completion.extension_coe Rat.uniformContinuous_coe_real]

theorem exercise25_toReal_surjective : Function.Surjective exercise25_toReal := by
  have hc : IsClosed (range exercise25_toReal) :=
    exercise25_toReal_isometry.isClosedEmbedding.isClosed_range
  have hsub : range ((↑) : ℚ → ℝ) ⊆ range exercise25_toReal := by
    rintro _ ⟨q, rfl⟩
    exact ⟨Exercise24.embed q, exercise25_toReal_embed q⟩
  intro x
  exact hc.closure_subset_iff.mpr hsub (Rat.denseRange_cast x)

/-- The completion in the precise sense of Exercise 24 is the real line. -/
def exercise25_rational_completion : Exercise24.Completion ℚ ≃ᵢ ℝ where
  toEquiv := Equiv.ofBijective exercise25_toReal
    ⟨exercise25_toReal_isometry.injective, exercise25_toReal_surjective⟩
  isometry_toFun := exercise25_toReal_isometry

@[simp] theorem exercise25_rational_completion_embed (q : ℚ) :
    exercise25_rational_completion (Exercise24.embed q) = (q : ℝ) :=
  exercise25_toReal_embed q

/-- A represented rational Cauchy sequence maps to its usual real limit. -/
theorem exercise25_representative_limit (s : Exercise24.Sequence ℚ) :
    Tendsto (fun n => (s.val n : ℝ)) atTop
      (𝓝 (exercise25_rational_completion (Exercise24.classOf s))) := by
  simpa only [Function.comp_def, exercise25_rational_completion_embed] using
    exercise25_rational_completion.continuous.continuousAt.tendsto.comp
      (Exercise24.tendsto_embed_classOf s)

/-- The quotient distance is the ordinary absolute-value distance on the real line. -/
theorem exercise25_distance (p q : Exercise24.Completion ℚ) :
    dist p q = |exercise25_rational_completion p - exercise25_rational_completion q| := by
  rw [← exercise25_rational_completion.isometry.dist_eq, Real.dist_eq]

/-- The identification has complete domain and dense image of the original rationals. -/
theorem exercise25_completeness_density :
    CompleteSpace (Exercise24.Completion ℚ) ∧
      DenseRange (fun q : ℚ => exercise25_rational_completion (Exercise24.embed q)) := by
  refine ⟨inferInstance, ?_⟩
  simpa only [exercise25_rational_completion_embed] using
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))

/-- Classification of the source quotient, including the embedding, completeness,
and density conditions required of this identification. -/
theorem exercise25_identification :
    ∃ e : Exercise24.Completion ℚ ≃ᵢ ℝ,
      (∀ q : ℚ, e (Exercise24.embed q) = (q : ℝ)) ∧
      CompleteSpace (Exercise24.Completion ℚ) ∧
      DenseRange (fun q : ℚ => e (Exercise24.embed q)) :=
  ⟨exercise25_rational_completion, exercise25_rational_completion_embed,
    exercise25_completeness_density⟩

end Rudin.Chapter03
