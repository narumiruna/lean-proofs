module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Bases
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# R02E29: disjoint open interval components

The source says “segments” (book 45, PDF 54). With two finite real endpoints
as in Definition 2.17, that assertion is false: see
`exercise29_bounded_segment_obstruction`. The decomposition below uses the
extended convention supported by book 278: bounded open intervals, either
open ray, and the whole line. Its members are nonempty connected components;
the empty open set has an empty family. Countable means at most countable.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Topology

/-- The extended segment convention, not a claim about finite endpoints. -/
def exercise29_OpenInterval (I : Set ℝ) : Prop :=
  (∃ a b : ℝ, I = Ioo a b) ∨ (∃ a : ℝ, I = Ioi a) ∨
    (∃ b : ℝ, I = Iio b) ∨ I = univ

/-- Only components with a point in the open set are included. -/
def exercise29_components (U : Set ℝ) : Set (Set ℝ) :=
  {I | ∃ x ∈ U, I = connectedComponentIn U x}

theorem exercise29_interval_shape {I : Set ℝ} (ho : IsOpen I)
    (hn : I.Nonempty) (hc : IsPreconnected I) : exercise29_OpenInterval I := by
  have hi := ho.interior_eq.symm
  rcases hc.mem_intervals with (h | h | h | h | h | h | h | h | h | h)
  · rw [h, interior_Icc] at hi
    exact Or.inl ⟨_, _, h.trans hi⟩
  · rw [h, interior_Ico] at hi
    exact Or.inl ⟨_, _, h.trans hi⟩
  · rw [h, interior_Ioc] at hi
    exact Or.inl ⟨_, _, h.trans hi⟩
  · exact Or.inl ⟨_, _, h⟩
  · rw [h, interior_Ici] at hi
    exact Or.inr (Or.inl ⟨_, h.trans hi⟩)
  · exact Or.inr (Or.inl ⟨_, h⟩)
  · rw [h, interior_Iic] at hi
    exact Or.inr (Or.inr (Or.inl ⟨_, h.trans hi⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, h⟩))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (hn.ne_empty h).elim

/-- The explicit component construction, including maximal connected components. -/
theorem exercise29_open_interval_decomposition {U : Set ℝ} (hU : IsOpen U) :
    (exercise29_components U).Countable ∧
      (exercise29_components U).PairwiseDisjoint id ∧
      (∀ I ∈ exercise29_components U,
        I.Nonempty ∧ IsOpen I ∧ IsPreconnected I ∧ exercise29_OpenInterval I) ∧
      ⋃₀ exercise29_components U = U := by
  have hd : (exercise29_components U).PairwiseDisjoint id := by
    intro I hI J hJ hne
    obtain ⟨x, hx, rfl⟩ := hI
    obtain ⟨y, hy, rfl⟩ := hJ
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hne ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm)
  have ho : ∀ I ∈ exercise29_components U, IsOpen I := by
    rintro I ⟨x, hx, rfl⟩
    exact hU.connectedComponentIn
  have hn : ∀ I ∈ exercise29_components U, I.Nonempty := by
    rintro I ⟨x, hx, rfl⟩
    exact connectedComponentIn_nonempty_iff.mpr hx
  refine ⟨hd.countable_of_isOpen ho hn, hd, ?_, ?_⟩
  · intro I hI
    have hc : IsPreconnected I := by
      obtain ⟨x, hx, rfl⟩ := hI
      exact isPreconnected_connectedComponentIn
    exact ⟨hn I hI, ho I hI, hc, exercise29_interval_shape (ho I hI) (hn I hI) hc⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨I, ⟨y, hy, rfl⟩, hx⟩
      exact connectedComponentIn_subset U y hx
    · intro x hx
      exact mem_sUnion.mpr ⟨connectedComponentIn U x, ⟨x, hx, rfl⟩,
        mem_connectedComponentIn hx⟩

/-- The source assertion under the explicitly extended segment convention. -/
theorem exercise29_source_segments {U : Set ℝ} (hU : IsOpen U) :
    ∃ C : Set (Set ℝ), C.Countable ∧ C.PairwiseDisjoint id ∧
      (∀ I ∈ C, I.Nonempty ∧ IsOpen I ∧ exercise29_OpenInterval I) ∧ ⋃₀ C = U := by
  obtain ⟨hc, hd, hm, hu⟩ := exercise29_open_interval_decomposition hU
  exact ⟨exercise29_components U, hc, hd, fun I hI =>
    ⟨(hm I hI).1, (hm I hI).2.1, (hm I hI).2.2.2⟩, hu⟩

theorem exercise29_components_empty : exercise29_components ∅ = ∅ := by
  ext I
  simp [exercise29_components]

/-- A nonempty preconnected open set has just itself as component. This applies
in particular to either ray and to the whole line. -/
theorem exercise29_components_of_preconnected {U : Set ℝ}
    (hn : U.Nonempty) (hc : IsPreconnected U) : exercise29_components U = {U} := by
  ext I
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [hc.connectedComponentIn hx]
  · rintro rfl
    obtain ⟨x, hx⟩ := hn
    exact ⟨x, hx, (hc.connectedComponentIn hx).symm⟩

/-- Boundary checks for the permitted unbounded components. -/
theorem exercise29_components_Ioi (a : ℝ) : exercise29_components (Ioi a) = {Ioi a} :=
  exercise29_components_of_preconnected nonempty_Ioi isPreconnected_Ioi

theorem exercise29_components_Iio (b : ℝ) : exercise29_components (Iio b) = {Iio b} :=
  exercise29_components_of_preconnected nonempty_Iio isPreconnected_Iio

theorem exercise29_components_univ : exercise29_components univ = {univ} :=
  exercise29_components_of_preconnected Set.univ_nonempty isPreconnected_univ

/-- The whole line is open and connected, but no disjoint family of bounded
open segments covers it. No countability assumption can repair this claim;
empty segments are allowed here as well. -/
theorem exercise29_bounded_segment_obstruction :
    IsOpen (univ : Set ℝ) ∧ IsConnected (univ : Set ℝ) ∧
      ¬ ∃ (ι : Type) (a b : ι → ℝ),
        Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
          (⋃ i, Ioo (a i) (b i)) = univ := by
  refine ⟨isOpen_univ, isConnected_univ, ?_⟩
  rintro ⟨ι, a, b, hd, hu⟩
  have hz : (0 : ℝ) ∈ ⋃ i, Ioo (a i) (b i) := by rw [hu]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  have heq : (Ioo (a i) (b i))ᶜ = ⋃ j, ⋃ (_ : j ≠ i), Ioo (a j) (b j) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ ⋃ j, Ioo (a j) (b j) := by rw [hu]; trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨by rintro rfl; exact hx hj, hj⟩⟩
    · intro hx
      obtain ⟨j, hji, hj⟩ := mem_iUnion.mp hx |>.imp fun j hj => mem_iUnion.mp hj
      exact fun hxi => Set.disjoint_left.mp (hd hji) hj hxi
  have hcl : IsClopen (Ioo (a i) (b i)) := by
    refine ⟨isOpen_compl_iff.mp ?_, isOpen_Ioo⟩
    rw [heq]
    exact isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_Ioo
  have hall := hcl.eq_univ ⟨0, hi⟩
  have ha : a i ∈ Ioo (a i) (b i) := by rw [hall]; trivial
  exact (lt_irrefl (a i)) ha.1

end Rudin.Chapter02
