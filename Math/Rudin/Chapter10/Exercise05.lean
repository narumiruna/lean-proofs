module

public import Math.Rudin.Chapter04.Exercise22
public import Mathlib.Topology.PartitionOfUnity

@[expose] public section
noncomputable section
namespace Rudin.Chapter10
universe u v
open Set Filter
open scoped Topology

/-- The metric separating quotient, with constants in the empty-set cases. -/
def exercise05_separator {X : Type*} [MetricSpace X] (A B : Set X) : X → ℝ :=
  if A = ∅ then fun _ => 1 else if B = ∅ then fun _ => 0
  else Rudin.Chapter04.exercise22_f A B

theorem exercise05_separator_spec {X : Type*} [MetricSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B) :
    Continuous (exercise05_separator A B) ∧
    (∀ x, exercise05_separator A B x ∈ Icc (0 : ℝ) 1) ∧
    EqOn (exercise05_separator A B) (fun _ => 0) A ∧
    EqOn (exercise05_separator A B) (fun _ => 1) B := by
  classical
  by_cases ha : A = ∅
  · simp [exercise05_separator, ha, continuous_const, EqOn]
  by_cases hb : B = ∅
  · simp [exercise05_separator, ha, hb, continuous_const, EqOn]
  have han := Set.nonempty_iff_ne_empty.mpr ha
  have hbn := Set.nonempty_iff_ne_empty.mpr hb
  simp only [exercise05_separator, ite_eq_right ha, ite_eq_right hb]
  exact ⟨Rudin.Chapter04.exercise22_continuous hA hB han hbn hd,
    Rudin.Chapter04.exercise22_range hA hB han hbn hd,
    fun x hx => (Rudin.Chapter04.exercise22_zero_fiber hA hB han hbn hd x).mpr hx,
    fun x hx => (Rudin.Chapter04.exercise22_one_fiber hA hB han hbn hd x).mpr hx⟩

/-- A metric bump: one on an open neighborhood and topological support inside U. -/
theorem exercise05_bump {X : Type*} [MetricSpace X] {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ f : X → ℝ,
      Continuous f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      EqOn f (fun _ => 1) V ∧ tsupport f ⊆ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := normal_exists_closure_subset isClosed_singleton hU
    (singleton_subset_iff.mpr hx)
  obtain ⟨V, hV, hxV, hVW⟩ := normal_exists_closure_subset isClosed_singleton hW hxW
  have hd : Disjoint Wᶜ (closure V) := disjoint_left.mpr fun y hy hz => hy (hVW hz)
  obtain ⟨hc, hr, hzero, hone⟩ := exercise05_separator_spec hW.isClosed_compl
    isClosed_closure hd
  refine ⟨V, hV, hxV (mem_singleton x), exercise05_separator Wᶜ (closure V), hc, hr,
    hone.mono subset_closure, ?_⟩
  apply (closure_mono ?_).trans hWU
  intro y hy
  by_contra hn
  exact hy (hzero hn)

/-- Finite extraction and the source ordered-product construction. This helper
also applies to smooth bump functions. Empty compact sets need no index. -/
theorem exercise05_finite_bumps {X : Type u} {I : Type v} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (U : I → Set X) (p : (X → ℝ) → Prop)
    (bump : ∀ x ∈ K, ∃ i : I, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ f : C(X, ℝ), (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
        EqOn f (fun _ => 1) V ∧ tsupport f ⊆ U i ∧ p f) :
    ∃ (J : Type u) (_ : Fintype J) (a : J → I) (f : BumpCovering J X K),
      f.IsSubordinate (U ∘ a) ∧ ∀ j, p (f j) := by
  classical
  choose a V hV hmem f hr hone hs hp using fun x : K => bump x x.property
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hmem ⟨x,hx⟩⟩)
  let g : BumpCovering t X K := {
    toFun := fun j => f j.val
    locallyFinite' := locallyFinite_of_finite _
    nonneg' := fun j y => (hr j.val y).1
    le_one' := fun j y => (hr j.val y).2
    eventuallyEq_one' := by
      intro x hxK
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hxK)
      exact ⟨⟨j,hj⟩, Filter.Eventually.mono ((hV j).mem_nhds hxj)
        (fun y hy => hone j hy)⟩ }
  exact ⟨↥t, inferInstance, fun j => a j.val, g, (fun j => hs j.val), fun j => hp j.val⟩

/-- The finite metric-space partition of unity. Support means closure of the
nonzero set; no local compactness or nonempty-set hypothesis is imposed. -/
theorem exercise05_metric_partition {X : Type u} {I : Type v} [MetricSpace X]
    {K : Set X} (hK : IsCompact K) (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (J : Type u) (_ : Fintype J) (a : J → I) (ψ : J → X → ℝ),
      (∀ j, Continuous (ψ j)) ∧ (∀ j x, ψ j x ∈ Icc (0 : ℝ) 1) ∧
      (∀ j, tsupport (ψ j) ⊆ U (a j)) ∧ (∀ x ∈ K, ∑ j, ψ j x = 1) := by
  obtain ⟨J, inst, a, f, hf, _⟩ := exercise05_finite_bumps hK U (fun _ => True) (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨V, hV, hxV, g, hc, hr, hone, hs⟩ := exercise05_bump (hU i) hi
    exact ⟨i, V, hV, hxV, ⟨g,hc⟩, hr, hone, hs, trivial⟩)
  let := inst
  exact ⟨J, inst, a, fun j => f.toPartitionOfUnity j,
    fun j => (f.toPartitionOfUnity j).continuous,
    fun j x => ⟨f.toPartitionOfUnity.nonneg j x, f.toPartitionOfUnity.le_one j x⟩,
    hf.toPartitionOfUnity, fun x hx => by simpa only [finsum_eq_sum_of_fintype] using f.toPartitionOfUnity.sum_eq_one hx⟩

end Rudin.Chapter10
