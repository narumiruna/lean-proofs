module

public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences

/-!
# Rudin, Chapter 3, Exercise 24

The carrier is the quotient of Cauchy sequences by distance tending to zero,
not the library's quotient of Cauchy filters. The map `toCompletion` identifies
these two constructions. The metric is pulled back along this injective map;
`distance_limit` proves that it is exactly the limit of distances required by
part (b). No nonemptiness hypothesis on the original metric space is used.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Rudin.Chapter03.Exercise24

universe u
variable {X : Type u} [MetricSpace X]

/-- The source's Cauchy sequences (indexed from zero instead of one). -/
def Sequence (X : Type u) [MetricSpace X] := {s : ℕ → X // CauchySeq s}

/-- Rudin's relation, defined using the original metric, before taking a quotient. -/
def Equivalent (s t : Sequence X) : Prop :=
  Tendsto (fun n => dist (s.val n) (t.val n)) atTop (𝓝 0)

/-- Every source sequence converges after mapping into the library completion. -/
theorem exists_completion_limit (s : Sequence X) :
    ∃ z : UniformSpace.Completion X,
      Tendsto (fun n => (s.val n : UniformSpace.Completion X)) atTop (𝓝 z) :=
  cauchySeq_tendsto_of_complete
    (UniformSpace.Completion.coe_isometry.uniformContinuous.comp_cauchySeq s.property)

/-- The limit is selected only from an existence theorem for the given sequence. -/
def sequenceLimit (s : Sequence X) : UniformSpace.Completion X :=
  Classical.choose (exists_completion_limit s)

theorem tendsto_sequenceLimit (s : Sequence X) :
    Tendsto (fun n => (s.val n : UniformSpace.Completion X)) atTop (𝓝 (sequenceLimit s)) :=
  Classical.choose_spec (exists_completion_limit s)

/-- In particular, the real limit in part (b) exists, even if `X` is not complete. -/
theorem sequence_distance_limit (s t : Sequence X) :
    Tendsto (fun n => dist (s.val n) (t.val n)) atTop
      (𝓝 (dist (sequenceLimit s) (sequenceLimit t))) := by
  simpa only [UniformSpace.Completion.dist_eq] using
    (tendsto_sequenceLimit s).dist (tendsto_sequenceLimit t)

/-- The real number specified in part (b), defined as the limit of original distances. -/
def sequenceDistance (s t : Sequence X) : ℝ :=
  atTop.limUnder (fun n => dist (s.val n) (t.val n))

/-- This limit is not a default value for a divergent sequence. -/
theorem sequenceDistance_eq (s t : Sequence X) :
    sequenceDistance s t = dist (sequenceLimit s) (sequenceLimit t) :=
  (sequence_distance_limit s t).limUnder_eq

/-- The key bridge: precisely the source-equivalent sequences have the same limit. -/
theorem equivalent_iff_limit_eq (s t : Sequence X) :
    Equivalent s t ↔ sequenceLimit s = sequenceLimit t := by
  constructor
  · intro h
    exact dist_eq_zero.mp (tendsto_nhds_unique (sequence_distance_limit s t) h)
  · intro h
    simpa only [Equivalent, h, dist_self] using sequence_distance_limit s t

/-- Part (a), including all three equivalence-relation axioms. -/
theorem exercise24_a : Equivalence (Equivalent (X := X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact (equivalent_iff_limit_eq s s).2 rfl
  · intro s t h
    exact (equivalent_iff_limit_eq t s).2 ((equivalent_iff_limit_eq s t).1 h).symm
  · intro s t r hst htr
    exact (equivalent_iff_limit_eq s r).2
      (((equivalent_iff_limit_eq s t).1 hst).trans ((equivalent_iff_limit_eq t r).1 htr))

/-- The limit of distances does not depend on either representative. -/
theorem exercise24_b_well_defined (s s' t t' : Sequence X)
    (hs : Equivalent s s') (ht : Equivalent t t') :
    sequenceDistance s t = sequenceDistance s' t' := by
  simp only [sequenceDistance_eq, (equivalent_iff_limit_eq s s').1 hs,
    (equivalent_iff_limit_eq t t').1 ht]

/-- The setoid uses the actual limit-zero relation, not equality in the library completion. -/
def sequenceSetoid (X : Type u) [MetricSpace X] : Setoid (Sequence X) :=
  ⟨Equivalent, exercise24_a⟩

/-- Rudin's `X*`, as an actual quotient of Cauchy sequences. -/
def Completion (X : Type u) [MetricSpace X] := Quotient (sequenceSetoid X)

/-- The equivalence class of a sequence. -/
def classOf (s : Sequence X) : Completion X := Quotient.mk (sequenceSetoid X) s

/-- The source's distance function, obtained by descending the real limit to classes. -/
def delta : Completion X → Completion X → ℝ :=
  Quotient.lift₂ sequenceDistance
    (fun s t s' t' hs ht => exercise24_b_well_defined s s' t t' hs ht)

@[simp] theorem delta_classOf (s t : Sequence X) :
    delta (classOf s) (classOf t) = sequenceDistance s t := rfl

/-- If `X` is empty, there are no sequences, hence no equivalence classes. -/
instance instIsEmpty [IsEmpty X] : IsEmpty (Completion X) :=
  ⟨fun p => Quotient.inductionOn p (fun s => isEmptyElim (s.val 0))⟩

/-- The proved map from source classes to the library's filter completion. -/
def toCompletion : Completion X → UniformSpace.Completion X :=
  Quotient.lift sequenceLimit (fun s t h => (equivalent_iff_limit_eq s t).1 h)

@[simp] theorem toCompletion_classOf (s : Sequence X) :
    toCompletion (classOf s) = sequenceLimit s := rfl

theorem toCompletion_injective : Function.Injective (toCompletion (X := X)) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro s t h
  exact Quotient.sound ((equivalent_iff_limit_eq s t).2 h)

/-- Every library completion point comes from a Cauchy sequence in `X`.
This proof also applies when `X` is empty: it does not select an arbitrary point of `X`. -/
theorem toCompletion_surjective : Function.Surjective (toCompletion (X := X)) := by
  intro z
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    (UniformSpace.Completion.denseRange_coe z)
  choose s hs using hv
  have hslim : Tendsto (fun n => (s n : UniformSpace.Completion X)) atTop (𝓝 z) := by
    simpa only [hs] using hvlim
  have hsc : CauchySeq s := by
    apply Metric.cauchySeq_iff.mpr
    simpa only [UniformSpace.Completion.dist_eq] using
      (Metric.cauchySeq_iff.mp hslim.cauchySeq)
  refine ⟨classOf ⟨s, hsc⟩, ?_⟩
  exact tendsto_nhds_unique (tendsto_sequenceLimit ⟨s, hsc⟩) hslim

/-- The metric is transported only after injectivity of the bridge has been proved. -/
instance instMetricSpace : MetricSpace (Completion X) :=
  MetricSpace.induced toCompletion toCompletion_injective inferInstance

theorem toCompletion_isometry : Isometry (toCompletion (X := X)) :=
  MetricSpace.isometry_induced toCompletion toCompletion_injective

/-- An explicit isometric identification, not a replacement of the source quotient. -/
def completionEquiv : Completion X ≃ᵢ UniformSpace.Completion X where
  toEquiv := Equiv.ofBijective toCompletion ⟨toCompletion_injective, toCompletion_surjective⟩
  isometry_toFun := toCompletion_isometry

/-- The transported metric equals the independently descended limit-distance function. -/
theorem dist_eq_delta (p q : Completion X) : dist p q = delta p q := by
  refine Quotient.inductionOn₂ p q ?_
  intro s t
  exact (sequenceDistance_eq s t).symm

/-- Part (b): the quotient distance is the limit required in the source. -/
theorem distance_limit (s t : Sequence X) :
    Tendsto (fun n => dist (s.val n) (t.val n)) atTop
      (𝓝 (dist (classOf s) (classOf t))) :=
  sequence_distance_limit s t

/-- All metric axioms for the limit-distance metric on source equivalence classes. -/
theorem exercise24_b_metric :
    (∀ p : Completion X, dist p p = 0) ∧
    (∀ p q : Completion X, 0 ≤ dist p q) ∧
    (∀ p q : Completion X, dist p q = 0 ↔ p = q) ∧
    (∀ p q : Completion X, dist p q = dist q p) ∧
    (∀ p q r : Completion X, dist p r ≤ dist p q + dist q r) :=
  ⟨dist_self, fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero, dist_comm, dist_triangle⟩

/-- Part (c): completeness of the actual Cauchy-sequence quotient. -/
instance instCompleteSpace : CompleteSpace (Completion X) :=
  completionEquiv.completeSpace

theorem exercise24_c : CompleteSpace (Completion X) := inferInstance

/-- The constant Cauchy sequence at a point. -/
def constantSequence (x : X) : Sequence X := ⟨fun _ => x, cauchySeq_const x⟩

/-- Part (d): the map is defined as the class of the constant sequence. -/
def embed (x : X) : Completion X := classOf (constantSequence x)

/-- The embedding uses exactly the constant-sequence class from the source. -/
theorem exercise24_d_embedding (x : X) : embed x = classOf (constantSequence x) := rfl

@[simp] theorem toCompletion_embed (x : X) :
    toCompletion (embed x) = (x : UniformSpace.Completion X) :=
  tendsto_nhds_unique (tendsto_sequenceLimit (constantSequence x)) tendsto_const_nhds

/-- Part (d), the exact distance identity. -/
theorem exercise24_d (x y : X) : dist (embed x) (embed y) = dist x y := by
  rw [← toCompletion_isometry.dist_eq, toCompletion_embed, toCompletion_embed,
    UniformSpace.Completion.dist_eq]

theorem embed_isometry : Isometry (embed (X := X)) := Isometry.of_dist_eq exercise24_d

theorem embed_injective : Function.Injective (embed (X := X)) := embed_isometry.injective

/-- Each source sequence converges to its own equivalence class. -/
theorem tendsto_embed_classOf (s : Sequence X) :
    Tendsto (fun n => embed (s.val n)) atTop (𝓝 (classOf s)) := by
  apply toCompletion_isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, toCompletion_embed, toCompletion_classOf] using
    tendsto_sequenceLimit s

/-- Part (e): the constant-sequence embedding has dense range. -/
theorem exercise24_e_density : DenseRange (embed (X := X)) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro s
  exact mem_closure_of_tendsto (tendsto_embed_classOf s)
    (Eventually.of_forall (fun n => mem_range_self (s.val n)))

/-- Part (e): if the original metric space is complete, every class is constant. -/
theorem exercise24_e_surjective [CompleteSpace X] : Function.Surjective (embed (X := X)) := by
  intro p
  refine Quotient.inductionOn p ?_
  intro s
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete s.property
  refine ⟨x, Quotient.sound ?_⟩
  change Equivalent (constantSequence x) s
  simpa only [Equivalent, constantSequence, dist_comm] using
    (tendsto_iff_dist_tendsto_zero.mp hx)

/-- The source's equality `φ(X) = X*` when `X` is complete. -/
theorem exercise24_e_range [CompleteSpace X] : range (embed (X := X)) = univ :=
  range_eq_univ.mpr exercise24_e_surjective

end Rudin.Chapter03.Exercise24
