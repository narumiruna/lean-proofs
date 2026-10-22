module

public import Mathlib
public import Math.Rudin.Chapter02.Exercise10

@[expose] public section
namespace Rudin.Chapter04
open Set

/-- The inverse on the image is continuous, and its domain is compact. -/
theorem exercise26_inverse_continuity {Y Z : Type*} [MetricSpace Y] [MetricSpace Z]
    [CompactSpace Y] {g : Y → Z} (hg : Continuous g) (hi : Function.Injective g) :
    ∃ e : Y ≃ₜ range g, (∀ y, (e y : Z) = g y) ∧
      Continuous e.symm ∧ UniformContinuous e.symm := by
  let e := (hg.isClosedEmbedding hi).isEmbedding.toHomeomorph
  let : CompactSpace (range g) := isCompact_iff_compactSpace.mp (isCompact_range hg)
  exact ⟨e, fun _ => rfl, e.symm.continuous,
    CompactSpace.uniformContinuous_of_continuous e.symm.continuous⟩

/-- No continuity assumption is made on f. -/
theorem exercise26_uniform_continuity {X Y Z : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z] [CompactSpace Y]
    {f : X → Y} {g : Y → Z} (hg : Continuous g) (hi : Function.Injective g)
    (hh : UniformContinuous (g ∘ f)) : UniformContinuous f := by
  obtain ⟨e, he, _, heu⟩ := exercise26_inverse_continuity hg hi
  have hh' : UniformContinuous (fun x => (⟨g (f x), ⟨f x, rfl⟩⟩ : range g)) :=
    hh.subtype_mk _
  have hid : (fun x => e.symm ⟨g (f x), ⟨f x, rfl⟩⟩) = f := by
    funext x
    apply e.injective
    apply Subtype.ext
    simpa using he (f x) |>.symm
  simpa only [Function.comp_def, hid] using heu.comp hh'

theorem exercise26_continuity {X Y Z : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z] [CompactSpace Y]
    {f : X → Y} {g : Y → Z} (hg : Continuous g) (hi : Function.Injective g)
    (hh : Continuous (g ∘ f)) : Continuous f :=
  (hg.isClosedEmbedding hi).isEmbedding.isInducing.continuous_iff.mpr hh

/-- The reverse implication also holds: continuous g is uniformly continuous on compact Y. -/
theorem exercise26_uniform_continuity_forward {X Y Z : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z] [CompactSpace Y]
    {f : X → Y} {g : Y → Z} (hg : Continuous g)
    (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  (CompactSpace.uniformContinuous_of_continuous hg).comp hf

/-- Continuity in the forward direction does not require compactness or injectivity. -/
theorem exercise26_continuity_forward {X Y Z : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Continuous g)
    (hf : Continuous f) : Continuous (g ∘ f) :=
  hg.comp hf

/-- X and Z are the ordinary compact unit interval. -/
abbrev exercise26X : Type := ↥(Icc (0 : ℝ) 1)
/-- Y has the same underlying points, but the zero-one metric. -/
def exercise26Y : Type := ↥(Icc (0 : ℝ) 1)

noncomputable instance exercise26Y_metric : MetricSpace exercise26Y :=
  Rudin.Chapter02.zeroOneMetric exercise26Y

instance exercise26Y_discrete : DiscreteTopology exercise26Y :=
  Rudin.Chapter02.zeroOne_discreteTopology

def exercise26f (x : exercise26X) : exercise26Y := x
def exercise26g (y : exercise26Y) : exercise26X := y

theorem exercise26X_compact : CompactSpace exercise26X := inferInstance

theorem exercise26Y_infinite : Infinite exercise26Y := by
  have h : (Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite zero_lt_one
  exact h.to_subtype

theorem exercise26Y_noncompact : ¬ IsCompact (univ : Set exercise26Y) := by
  let := exercise26Y_infinite
  intro h
  have hf : (univ : Set exercise26Y).Finite := isCompact_iff_finite.mp h
  exact Set.infinite_univ hf

theorem exercise26g_continuous_injective :
    Continuous exercise26g ∧ Function.Injective exercise26g :=
  ⟨continuous_of_discreteTopology, fun _ _ h => h⟩

theorem exercise26h_uniformContinuous : UniformContinuous (exercise26g ∘ exercise26f) :=
  uniformContinuous_id

theorem exercise26f_not_continuous : ¬ Continuous exercise26f := by
  intro h
  have hr : range exercise26f = univ := by
    ext y
    simp only [mem_range, mem_univ, iff_true]
    exact ⟨y, rfl⟩
  exact exercise26Y_noncompact (hr ▸ isCompact_range h)

theorem exercise26f_not_uniformContinuous : ¬ UniformContinuous exercise26f :=
  fun h => exercise26f_not_continuous h.continuous

/-- Compact X,Z, noncompact Y, and a continuous injective g; h is uniformly
continuous, but f is not uniformly continuous. -/
theorem exercise26_noncompact_uniform_failure :
    CompactSpace exercise26X ∧ ¬ IsCompact (univ : Set exercise26Y) ∧
    Continuous exercise26g ∧ Function.Injective exercise26g ∧
    UniformContinuous (exercise26g ∘ exercise26f) ∧ ¬ UniformContinuous exercise26f :=
  ⟨exercise26X_compact, exercise26Y_noncompact, exercise26g_continuous_injective.1,
    exercise26g_continuous_injective.2, exercise26h_uniformContinuous,
    exercise26f_not_uniformContinuous⟩

theorem exercise26_noncompact_continuity_failure :
    CompactSpace exercise26X ∧ ¬ IsCompact (univ : Set exercise26Y) ∧
    Continuous exercise26g ∧ Function.Injective exercise26g ∧
    Continuous (exercise26g ∘ exercise26f) ∧ ¬ Continuous exercise26f :=
  ⟨exercise26X_compact, exercise26Y_noncompact, exercise26g_continuous_injective.1,
    exercise26g_continuous_injective.2, exercise26h_uniformContinuous.continuous,
    exercise26f_not_continuous⟩

end Rudin.Chapter04
