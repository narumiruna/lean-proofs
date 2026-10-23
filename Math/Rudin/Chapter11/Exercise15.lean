module

public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Data.EReal.BigOperators
public import Mathlib.Tactic

/-! # Chapter 11, Exercise 15

Elementary sets are finite unions of intervals contained in `(0,1]`.
The charge is Lebesgue length plus the indicator of the right-hand germ at zero.
The inner approximation in Definition 11.5 is closed in the ambient real line,
hence compact here. Relative closedness alone would not imply nonregularity.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Rudin.Chapter11
namespace ElementaryCharge

/-- Bounded real intervals, including all endpoint choices and degenerate cases. -/
def intervals : Set (Set ℝ) := {s | s ⊆ Ioc 0 1 ∧ OrdConnected s}

/-- The literal four bounded interval types from Definition 11.4. -/
def fourIntervals : Set (Set ℝ) := {s | ∃ a b : ℝ, a ≤ b ∧ s ⊆ Ioc 0 1 ∧
  (s = Icc a b ∨ s = Ico a b ∨ s = Ioc a b ∨ s = Ioo a b)}

/-- Order-connected subsets of the bounded domain are exactly these four types.
This includes the empty set, represented by `(1,1)`, and singletons `[a,a]`. -/
theorem intervals_eq_fourIntervals : intervals = fourIntervals := by
  ext s
  constructor
  · intro hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, 1, le_rfl, empty_subset _, Or.inr (Or.inr (Or.inr (by simp)))⟩
    have hb : BddBelow s := ⟨0, fun x hx ↦ (hs.1 hx).1.le⟩
    have ha : BddAbove s := ⟨1, fun x hx ↦ (hs.1 hx).2⟩
    have hc : IsConnected s := ⟨hne, isPreconnected_iff_ordConnected.mpr hs.2⟩
    refine ⟨sInf s, sSup s, csInf_le_csSup hne hb ha, hs.1, ?_⟩
    have h := mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
      (hc.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
    simpa only [mem_insert_iff, mem_singleton_iff] using h
  · rintro ⟨a, b, _, hsub, h⟩
    refine ⟨hsub, ?_⟩
    rcases h with rfl | rfl | rfl | rfl <;> infer_instance

/-- Finite unions of the intervals in `(0,1]`. -/
def elementary : Set (Set ℝ) := supClosure intervals

theorem intervals_semiring : IsSetSemiring intervals := by
  classical
  refine ⟨⟨empty_subset _, ordConnected_empty⟩,
    (fun s hs t ht ↦ ⟨inter_subset_left.trans hs.1, hs.2.inter ht.2⟩), ?_⟩
  intro s hs t ht
  by_cases ht0 : t = ∅
  · refine ⟨{s}, ?_, ?_, ?_⟩
    · simpa using hs
    · simp
    · simp [ht0]
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr ht0
  let L := (s \ t) ∩ Iio y
  let R := (s \ t) ∩ Ioi y
  have hL : L ∈ intervals := by
    refine ⟨fun x hx ↦ hs.1 hx.1.1, ⟨?_⟩⟩
    intro a ha b hb z hz
    refine ⟨⟨hs.2.out ha.1.1 hb.1.1 hz, ?_⟩, lt_of_le_of_lt hz.2 hb.2⟩
    intro hzt
    exact hb.1.2 (ht.2.out hzt hy ⟨hz.2, hb.2.le⟩)
  have hR : R ∈ intervals := by
    refine ⟨fun x hx ↦ hs.1 hx.1.1, ⟨?_⟩⟩
    intro a ha b hb z hz
    refine ⟨⟨hs.2.out ha.1.1 hb.1.1 hz, ?_⟩, lt_of_lt_of_le ha.2 hz.1⟩
    intro hzt
    exact ha.1.2 (ht.2.out hy hzt ⟨ha.2.le, hz.1⟩)
  have hd : Disjoint L R := disjoint_left.mpr fun x hx hx' ↦ (not_lt_of_gt hx.2) hx'.2
  refine ⟨{L, R}, ?_, ?_, ?_⟩
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  · intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hd
    · exact hd.symm
    · exact (huv rfl).elim
  · simp only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton]
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy x y with h | rfl | h
      · exact Or.inl ⟨hx, h⟩
      · exact (hx.2 hy).elim
      · exact Or.inr ⟨hx, h⟩
    · rintro (hx | hx) <;> exact hx.1

/-- Thus these finite unions are exactly an actual ring of elementary sets. -/
theorem elementary_ring : IsSetRing elementary := intervals_semiring.isSetRing_supClosure

/-- The ring is precisely the finite-union closure of the four actual interval types. -/
theorem elementary_eq_fourIntervals : elementary = supClosure fourIntervals := by
  rw [elementary, intervals_eq_fourIntervals]

/-- Every elementary set has a finite disjoint interval decomposition. -/
theorem disjoint_decomposition {s : Set ℝ} (hs : s ∈ elementary) :
    ∃ I : Finset (Set ℝ), ↑I ⊆ intervals ∧ (I : Set (Set ℝ)).PairwiseDisjoint id ∧
      s = ⋃₀ (I : Set (Set ℝ)) := by
  obtain ⟨P, hP⟩ := intervals_semiring.mem_supClosure_iff.mp hs
  exact ⟨P.parts, hP, P.disjoint, by simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts.symm⟩

/-- A literal finite disjoint union characterization of the ring. -/
theorem elementary_iff_finite_disjoint {s : Set ℝ} : s ∈ elementary ↔
    ∃ I : Finset (Set ℝ), ↑I ⊆ fourIntervals ∧
      (I : Set (Set ℝ)).PairwiseDisjoint id ∧ s = ⋃₀ (I : Set (Set ℝ)) := by
  constructor
  · intro hs
    obtain ⟨I, hI, hd, he⟩ := disjoint_decomposition hs
    exact ⟨I, by rwa [← intervals_eq_fourIntervals], hd, he⟩
  · rintro ⟨I, hI, _, rfl⟩
    have h := elementary_ring.biUnion_mem I (fun t ht ↦
      subset_supClosure (show t ∈ intervals by rw [intervals_eq_fourIntervals]; exact hI ht))
    simpa only [sUnion_eq_biUnion, Finset.mem_coe] using h

/-- A set contains every sufficiently small positive number. -/
def Germ (s : Set ℝ) : Prop := s ∈ 𝓝[>] (0 : ℝ)

local instance : DecidablePred Germ := Classical.decPred _

/-- A canonical set function, independent of any interval decomposition. -/
def φ (s : Set ℝ) : ℝ≥0∞ := volume s + if Germ s then 1 else 0

theorem interval_germ_constant {s : Set ℝ} (hs : s ∈ intervals) : Germ s ∨ Germ sᶜ := by
  classical
  by_cases h : ∀ ε > (0 : ℝ), ∃ x ∈ s, x < ε
  · obtain ⟨b, hb, _⟩ := h 1 zero_lt_one
    left
    apply Filter.mem_of_superset (Ioo_mem_nhdsGT (hs.1 hb).1)
    intro x hx
    obtain ⟨a, ha, hax⟩ := h x hx.1
    exact hs.2.out ha hb ⟨hax.le, hx.2.le⟩
  · push Not at h
    obtain ⟨ε, hε, he⟩ := h
    right
    apply Filter.mem_of_superset (Ioo_mem_nhdsGT hε)
    intro x hx hxs
    exact (not_le_of_gt hx.2) (he x hxs)

theorem germ_union_constant {s t : Set ℝ} (hs : Germ s ∨ Germ sᶜ)
    (ht : Germ t ∨ Germ tᶜ) : Germ (s ∪ t) ∨ Germ (s ∪ t)ᶜ := by
  rcases hs with hs | hs
  · exact Or.inl (Filter.mem_of_superset hs subset_union_left)
  · rcases ht with ht | ht
    · exact Or.inl (Filter.mem_of_superset ht subset_union_right)
    · exact Or.inr (by simpa only [Germ, compl_union] using inter_mem hs ht)

/-- Each elementary set has a constant zero-or-one indicator near zero. -/
theorem germ_constant {s : Set ℝ} (hs : s ∈ elementary) : Germ s ∨ Germ sᶜ := by
  exact supClosure_min (fun _ h ↦ interval_germ_constant h)
    (fun _ hs _ ht ↦ germ_union_constant hs ht) hs

/-- The literal indicator is eventually constant, with value zero or one. -/
theorem indicator_germ_constant {s : Set ℝ} (hs : s ∈ elementary) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧
      s.indicator (fun _ ↦ (1 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ ↦ c) := by
  classical
  rcases germ_constant hs with h | h
  · refine ⟨1, Or.inr rfl, ?_⟩
    filter_upwards [show ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ s from h] with x hx
    simp [hx]
  · refine ⟨0, Or.inl rfl, ?_⟩
    filter_upwards [show ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ sᶜ from h] with x hx
    simp [show x ∉ s from hx]

/-- A concrete eventual membership dichotomy, derived from finite interval unions. -/
theorem eventual_membership {s : Set ℝ} (hs : s ∈ elementary) :
    ∃ δ > (0 : ℝ), (∀ x ∈ Ioo 0 δ, x ∈ s) ∨ (∀ x ∈ Ioo 0 δ, x ∉ s) := by
  rcases germ_constant hs with h | h
  · obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
    exact ⟨δ, hδ, Or.inl hsub⟩
  · obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
    exact ⟨δ, hδ, Or.inr hsub⟩

theorem subset_domain {s : Set ℝ} (hs : s ∈ elementary) : s ⊆ Ioc 0 1 := by
  exact supClosure_min (t := {s : Set ℝ | s ⊆ Ioc 0 1}) (fun _ h ↦ h.1)
    (fun _ hs _ ht ↦ union_subset hs ht) hs

theorem measurable {s : Set ℝ} (hs : s ∈ elementary) : MeasurableSet s := by
  exact supClosure_min (t := {s : Set ℝ | MeasurableSet s}) (fun _ h ↦ h.2.measurableSet)
    (fun s hs t ht ↦ (show MeasurableSet s from hs).union (show MeasurableSet t from ht)) hs

theorem finite_value {s : Set ℝ} (hs : s ∈ elementary) : φ s ≠ ∞ := by
  have hv : volume s < ∞ := (measure_mono (subset_domain hs)).trans_lt measure_Ioc_lt_top
  unfold φ
  split_ifs <;> finiteness

theorem germ_not_compl {s : Set ℝ} (hs : Germ sᶜ) : ¬ Germ s := by
  intro h
  have he : (∅ : Set ℝ) ∈ 𝓝[>] (0 : ℝ) := by simpa using inter_mem h hs
  exact Filter.empty_notMem _ he

theorem germ_add {s t : Set ℝ} (hs : s ∈ elementary) (ht : t ∈ elementary)
    (hd : Disjoint s t) :
    (if Germ (s ∪ t) then (1 : ℝ≥0∞) else 0) =
      (if Germ s then 1 else 0) + (if Germ t then 1 else 0) := by
  classical
  rcases germ_constant hs with hs | hs <;> rcases germ_constant ht with ht | ht
  · have he : (∅ : Set ℝ) ∈ 𝓝[>] (0 : ℝ) := by
      simpa only [Set.disjoint_iff_inter_eq_empty.mp hd] using inter_mem hs ht
    exact (Filter.empty_notMem _ he).elim
  · have hu : Germ (s ∪ t) := Filter.mem_of_superset hs subset_union_left
    simp [hu, hs, germ_not_compl ht]
  · have hu : Germ (s ∪ t) := Filter.mem_of_superset ht subset_union_right
    simp [hu, ht, germ_not_compl hs]
  · have hu : Germ (s ∪ t)ᶜ := by simpa only [Germ, compl_union] using inter_mem hs ht
    simp [germ_not_compl hu, germ_not_compl hs, germ_not_compl ht]

/-- Finite additivity for the canonical charge. -/
theorem additive {s t : Set ℝ} (hs : s ∈ elementary) (ht : t ∈ elementary)
    (hd : Disjoint s t) : φ (s ∪ t) = φ s + φ t := by
  unfold φ
  rw [measure_union hd (measurable ht), germ_add hs ht hd]
  ac_rfl

theorem φ_empty : φ ∅ = 0 := by
  simp [φ, Germ, Filter.empty_notMem]

/-- The constructed additive content has the canonical set-based value `φ`. -/
def content : AddContent ℝ≥0∞ elementary :=
  elementary_ring.addContent_of_union φ φ_empty (fun hs ht hd ↦ additive hs ht hd)

/-- Finite disjoint unions have the sum of their component values. -/
theorem finite_additivity {ι : Type*} (I : Finset ι) (s : ι → Set ℝ)
    (hs : ∀ i ∈ I, s i ∈ elementary) (hd : (I : Set ι).PairwiseDisjoint s) :
    φ (⋃ i ∈ I, s i) = ∑ i ∈ I, φ (s i) :=
  addContent_biUnion_eq (m := content) elementary_ring hs hd

/-- Different finite disjoint decompositions of the same set give the same sum. -/
theorem well_defined {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (s : ι → Set ℝ) (t : κ → Set ℝ)
    (hs : ∀ i ∈ I, s i ∈ elementary) (ht : ∀ j ∈ J, t j ∈ elementary)
    (hd : (I : Set ι).PairwiseDisjoint s) (he : (J : Set κ).PairwiseDisjoint t)
    (hunion : (⋃ i ∈ I, s i) = ⋃ j ∈ J, t j) :
    (∑ i ∈ I, φ (s i)) = ∑ j ∈ J, φ (t j) := by
  rw [← finite_additivity I s hs hd, ← finite_additivity J t ht he, hunion]

theorem not_germ_of_away {s : Set ℝ} {a : ℝ} (ha : 0 < a) (hs : s ⊆ Ici a) :
    ¬ Germ s := by
  apply germ_not_compl
  apply Filter.mem_of_superset (Ioo_mem_nhdsGT ha)
  intro x hx hxs
  exact (not_le_of_gt hx.2) (hs hxs)

/-- All four endpoint conventions, including `a=b`, have ordinary length away from zero. -/
theorem interval_prescriptions {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (_hb : b ≤ 1) :
    φ (Icc a b) = ENNReal.ofReal (b-a) ∧
    φ (Ico a b) = ENNReal.ofReal (b-a) ∧
    φ (Ioc a b) = ENNReal.ofReal (b-a) ∧
    φ (Ioo a b) = ENNReal.ofReal (b-a) := by
  have hcc := not_germ_of_away ha (show Icc a b ⊆ Ici a from fun _ hx ↦ hx.1)
  have hco := not_germ_of_away ha (show Ico a b ⊆ Ici a from fun _ hx ↦ hx.1)
  have hoc := not_germ_of_away ha (show Ioc a b ⊆ Ici a from fun _ hx ↦ hx.1.le)
  have hoo := not_germ_of_away ha (show Ioo a b ⊆ Ici a from fun _ hx ↦ hx.1.le)
  simp [φ, hcc, hco, hoc, hoo, Real.volume_Icc, Real.volume_Ico,
    Real.volume_Ioc, Real.volume_Ioo]

theorem intervals_elementary {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    Icc a b ∈ elementary ∧ Ico a b ∈ elementary ∧
    Ioc a b ∈ elementary ∧ Ioo a b ∈ elementary := by
  have hsub : Icc a b ⊆ Ioc (0 : ℝ) 1 := fun x hx ↦ ⟨ha.trans_le hx.1, hx.2.trans hb⟩
  exact ⟨subset_supClosure ⟨hsub, ordConnected_Icc⟩,
    subset_supClosure ⟨Ico_subset_Icc_self.trans hsub, ordConnected_Ico⟩,
    subset_supClosure ⟨Ioc_subset_Icc_self.trans hsub, ordConnected_Ioc⟩,
    subset_supClosure ⟨Ioo_subset_Icc_self.trans hsub, ordConnected_Ioo⟩⟩

theorem singleton_value {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) : φ {a} = 0 := by
  simpa using (interval_prescriptions ha le_rfl ha1).1

theorem zero_interval_prescriptions {b : ℝ} (hb : 0 < b) (_hb1 : b ≤ 1) :
    φ (Ioo 0 b) = 1 + ENNReal.ofReal b ∧ φ (Ioc 0 b) = 1 + ENNReal.ofReal b := by
  have hoo : Germ (Ioo 0 b) := Ioo_mem_nhdsGT hb
  have hoc : Germ (Ioc 0 b) := Filter.mem_of_superset hoo Ioo_subset_Ioc_self
  simp [φ, hoo, hoc, Real.volume_Ioo, Real.volume_Ioc, add_comm]

theorem zero_intervals_elementary {b : ℝ} (hb1 : b ≤ 1) :
    Ioo 0 b ∈ elementary ∧ Ioc 0 b ∈ elementary := by
  have hsub : Ioc (0 : ℝ) b ⊆ Ioc 0 1 := fun x hx ↦ ⟨hx.1, hx.2.trans hb1⟩
  exact ⟨subset_supClosure ⟨Ioo_subset_Ioc_self.trans hsub, ordConnected_Ioo⟩,
    subset_supClosure ⟨hsub, ordConnected_Ioc⟩⟩

/-- The source's real-valued charge. `φ` is its finite extended-nonnegative encoding. -/
def charge (s : Set ℝ) : ℝ := (φ s).toReal

theorem charge_nonneg (s : Set ℝ) : 0 ≤ charge s := ENNReal.toReal_nonneg

theorem ofReal_charge {s : Set ℝ} (hs : s ∈ elementary) :
    ENNReal.ofReal (charge s) = φ s := ENNReal.ofReal_toReal (finite_value hs)

/-- The real formula is length plus a zero-or-one right-germ indicator. -/
theorem charge_formula {s : Set ℝ} (hs : s ∈ elementary) :
    charge s = (volume s).toReal + if Germ s then 1 else 0 := by
  have hv : volume s ≠ ∞ := ((measure_mono (subset_domain hs)).trans_lt
    measure_Ioc_lt_top).ne
  simp only [charge, φ]
  split_ifs <;> simp [ENNReal.toReal_add hv]

theorem charge_interval_prescriptions {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    charge (Icc a b) = b-a ∧ charge (Ico a b) = b-a ∧
    charge (Ioc a b) = b-a ∧ charge (Ioo a b) = b-a := by
  obtain ⟨hcc, hco, hoc, hoo⟩ := interval_prescriptions ha hab hb
  simp [charge, hcc, hco, hoc, hoo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem charge_zero_interval_prescriptions {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    charge (Ioo 0 b) = 1+b ∧ charge (Ioc 0 b) = 1+b := by
  obtain ⟨hoo, hoc⟩ := zero_interval_prescriptions hb hb1
  simp [charge, hoo, hoc, ENNReal.toReal_add, hb.le]

theorem charge_finite_additivity {ι : Type*} (I : Finset ι) (s : ι → Set ℝ)
    (hs : ∀ i ∈ I, s i ∈ elementary) (hd : (I : Set ι).PairwiseDisjoint s) :
    charge (⋃ i ∈ I, s i) = ∑ i ∈ I, charge (s i) := by
  simp only [charge, finite_additivity I s hs hd]
  exact ENNReal.toReal_sum (fun i hi ↦ finite_value (hs i hi))

/-- Decomposition independence with exactly the real-valued source prescriptions. -/
theorem charge_well_defined {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (s : ι → Set ℝ) (t : κ → Set ℝ)
    (hs : ∀ i ∈ I, s i ∈ elementary) (ht : ∀ j ∈ J, t j ∈ elementary)
    (hd : (I : Set ι).PairwiseDisjoint s) (he : (J : Set κ).PairwiseDisjoint t)
    (hunion : (⋃ i ∈ I, s i) = ⋃ j ∈ J, t j) :
    (∑ i ∈ I, charge (s i)) = ∑ j ∈ J, charge (t j) := by
  rw [← charge_finite_additivity I s hs hd, ← charge_finite_additivity J t ht he, hunion]

/-- Closed subsets of the domain are bounded away from the missing endpoint zero. -/
theorem closed_away_zero {F : Set ℝ} (hF : IsClosed F) (hsub : F ⊆ Ioc 0 1) :
    ∃ a > (0 : ℝ), F ⊆ Ici a := by
  have hzero : (0 : ℝ) ∈ Fᶜ := fun h ↦ (lt_irrefl 0) (hsub h).1
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl 0 hzero
  refine ⟨a, ha, fun x hx ↦ ?_⟩
  by_contra hnot
  have hxa : x < a := lt_of_not_ge hnot
  have hin : x ∈ Metric.ball 0 a := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos (hsub hx).1] using hxa
  exact hball hin hx

theorem compact_away_zero {F : Set ℝ} (hF : IsCompact F) (hsub : F ⊆ Ioc 0 1) :
    ∃ a > (0 : ℝ), F ⊆ Ici a := closed_away_zero hF.isClosed hsub

/-- Ambient closed subsets of this bounded domain are compact, as in PDF 314. -/
theorem closed_subset_compact {F : Set ℝ} (hF : IsClosed F) (hsub : F ⊆ Ioc 0 1) :
    IsCompact F :=
  isCompact_Icc.of_isClosed_subset hF (hsub.trans Ioc_subset_Icc_self)

/-- Definition 11.5, with relative openness only at the included upper endpoint.
The inner set is closed in `ℝ`, as required by the source's compactness argument.
All values are finite; `toReal` writes the source's two real inequalities literally. -/
def EndpointRegular : Prop := ∀ A ∈ elementary, ∀ ε : ℝ, 0 < ε →
  ∃ F ∈ elementary, ∃ G ∈ elementary,
    IsClosed F ∧ IsOpen (((↑) : Ioc (0 : ℝ) 1 → ℝ) ⁻¹' G) ∧
    F ⊆ A ∧ A ⊆ G ∧ (φ G).toReal - ε ≤ (φ A).toReal ∧
    (φ A).toReal ≤ (φ F).toReal + ε

/-- The unmodified ambient-topology condition in Definition 11.5. -/
def Regular : Prop := ∀ A ∈ elementary, ∀ ε : ℝ, 0 < ε →
  ∃ F ∈ elementary, ∃ G ∈ elementary,
    IsClosed F ∧ IsOpen G ∧ F ⊆ A ∧ A ⊆ G ∧
    (φ G).toReal - ε ≤ (φ A).toReal ∧ (φ A).toReal ≤ (φ F).toReal + ε

theorem regular_implies_endpoint_regular (h : Regular) : EndpointRegular := by
  intro A hA ε hε
  obtain ⟨F, hF, G, hG, hclosed, hopen, hFA, hAG, hup, hlo⟩ := h A hA ε hε
  exact ⟨F, hF, G, hG, hclosed, hopen.preimage continuous_subtype_val, hFA, hAG, hup, hlo⟩

/-- The witness `(0,1/2)` avoids the upper endpoint `1`. Even the weaker
relative-open variant fails, because compact inner sets lose the germ mass. -/
theorem nonregular_endpoint : ¬ EndpointRegular := by
  intro h
  obtain ⟨F, hF, G, hG, hclosed, hopen, hsub, hsup, hupper, hlower⟩ :=
    h (Ioo 0 (1/2)) (zero_intervals_elementary (by norm_num : (1/2 : ℝ) ≤ 1)).1
      (1/2) (by norm_num)
  have hcompact := closed_subset_compact hclosed (subset_domain hF)
  obtain ⟨a, ha, haway⟩ := compact_away_zero hcompact (subset_domain hF)
  have hφF : φ F = volume F := by simp [φ, not_germ_of_away ha haway]
  have hφA : φ (Ioo 0 (1/2)) = 1 + ENNReal.ofReal (1/2) :=
    (zero_interval_prescriptions (by norm_num) (by norm_num)).1
  have hvol : volume F ≤ ENNReal.ofReal (1/2) := by
    simpa using (measure_mono (μ := volume) hsub)
  have hr : (volume F).toReal ≤ 1/2 := by
    simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rw [hφA, hφF, ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top] at hlower
  norm_num at hlower
  linarith

/-- Failure of the actual ambient-topology condition of Definition 11.5. -/
theorem nonregular : ¬ Regular := fun h ↦ nonregular_endpoint (regular_implies_endpoint_regular h)

/-- The actual dyadic partition of `(0,1]`. -/
def dyadic (n : ℕ) : Set ℝ := Ioc ((1/2 : ℝ)^(n+1)) ((1/2 : ℝ)^n)

private theorem dyadic_antitone : Antitone (fun n : ℕ ↦ (1/2 : ℝ)^n) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1/2) n]

theorem dyadic_elementary (n : ℕ) : dyadic n ∈ elementary := by
  apply (intervals_elementary (by positivity : 0 < (1/2 : ℝ)^(n+1)) _).2.2.1
  simpa using dyadic_antitone (Nat.zero_le n)

theorem dyadic_disjoint : Pairwise (fun m n ↦ Disjoint (dyadic m) (dyadic n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · apply Disjoint.symm
    exact Ioc_disjoint_Ioc_of_le (dyadic_antitone (Nat.succ_le_of_lt h))
  · exact Ioc_disjoint_Ioc_of_le (dyadic_antitone (Nat.succ_le_of_lt h))

theorem dyadic_union : (⋃ n, dyadic n) = Ioc 0 1 := by
  apply Subset.antisymm
  · refine iUnion_subset fun n ↦ subset_domain (dyadic_elementary n)
  · intro x hx
    have hlim : Tendsto (fun n : ℕ ↦ (1/2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hex : ∃ n : ℕ, (1/2 : ℝ)^n < x :=
      (hlim.eventually (Iio_mem_nhds hx.1)).exists
    have hz : Nat.find hex ≠ 0 := by
      intro hz
      have h := Nat.find_spec hex
      rw [hz, pow_zero] at h
      exact (not_lt_of_ge hx.2) h
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · have hh := Nat.find_spec hex
      rw [hn] at hh
      exact hh
    · exact le_of_not_gt (Nat.find_min hex (by omega : n < Nat.find hex))

theorem dyadic_value (n : ℕ) : φ (dyadic n) = volume (dyadic n) := by
  have hg : ¬ Germ (dyadic n) := not_germ_of_away
    (by positivity : 0 < (1/2 : ℝ)^(n+1)) (fun x hx ↦ hx.1.le)
  simp [φ, hg]

/-- Countable additivity on a family of sets; no topology or ambient measurable
space is imposed on that family. A sigma-ring is a special case. -/
def CountablyAdditiveOn (ψ : Set ℝ → ℝ≥0∞) (S : Set (Set ℝ)) : Prop :=
  ∀ s : ℕ → Set ℝ, (∀ n, s n ∈ S) → Pairwise (fun m n ↦ Disjoint (s m) (s n)) →
    (⋃ n, s n) ∈ S → ψ (⋃ n, s n) = ∑' n, ψ (s n)

/-- No countably additive extension exists on ANY family containing the elementary
ring, hence in particular on any sigma-ring containing it. -/
theorem no_countable_extension (S : Set (Set ℝ)) (hS : elementary ⊆ S) :
    ¬ ∃ ψ : Set ℝ → ℝ≥0∞,
      (∀ A ∈ elementary, ψ A = φ A) ∧ CountablyAdditiveOn ψ S := by
  rintro ⟨ψ, hagree, hadd⟩
  have h := hadd dyadic (fun n ↦ hS (dyadic_elementary n)) dyadic_disjoint
    (by rw [dyadic_union]; exact hS (zero_intervals_elementary le_rfl).2)
  have hsum : (∑' n, ψ (dyadic n)) = volume (Ioc (0 : ℝ) 1) := by
    simp_rw [hagree _ (dyadic_elementary _), dyadic_value]
    rw [← measure_iUnion dyadic_disjoint (fun n ↦ measurable (dyadic_elementary n)), dyadic_union]
  rw [dyadic_union, hagree _ (zero_intervals_elementary le_rfl).2,
    (zero_interval_prescriptions zero_lt_one le_rfl).2, hsum] at h
  norm_num at h

/-- The dyadic charges have real sum `1`, whereas their union has charge `2`. -/
theorem dyadic_charge_hasSum : HasSum (fun n ↦ charge (dyadic n)) 1 := by
  have hsum : (∑' n, volume (dyadic n)) = 1 := by
    rw [← measure_iUnion dyadic_disjoint (fun n ↦ measurable (dyadic_elementary n)), dyadic_union]
    simp
  have hfin : ∀ n, volume (dyadic n) ≠ ∞ := fun n ↦
    ((measure_mono (subset_domain (dyadic_elementary n))).trans_lt measure_Ioc_lt_top).ne
  have hs := ENNReal.hasSum_toReal (by rw [hsum]; norm_num : (∑' n, volume (dyadic n)) ≠ ∞)
  have ht : (∑' n, (volume (dyadic n)).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq hfin, hsum]
    simp
  simpa only [charge, dyadic_value, ht] using hs

/-- The series condition in Definition 11.2 for extended-real-valued functions.
Only ordinary ordered partial sums are required. Unconditional countable
additivity, and the source's extra exclusion of simultaneous infinities, are stronger. -/
def CountablyAdditiveERealOn (ψ : Set ℝ → EReal) (S : Set (Set ℝ)) : Prop :=
  ∀ s : ℕ → Set ℝ, (∀ n, s n ∈ S) → Pairwise (fun m n ↦ Disjoint (s m) (s n)) →
    (⋃ n, s n) ∈ S →
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, ψ (s n)) atTop (𝓝 (ψ (⋃ n, s n)))

/-- Full source obstruction: even a signed extended-real-valued extension is
impossible on any family containing the ring. In particular no sigma-ring works. -/
theorem no_extendedReal_countable_extension (S : Set (Set ℝ)) (hS : elementary ⊆ S) :
    ¬ ∃ ψ : Set ℝ → EReal,
      (∀ A ∈ elementary, ψ A = (charge A : EReal)) ∧ CountablyAdditiveERealOn ψ S := by
  rintro ⟨ψ, hagree, hadd⟩
  have h := hadd dyadic (fun n ↦ hS (dyadic_elementary n)) dyadic_disjoint
    (by rw [dyadic_union]; exact hS (zero_intervals_elementary le_rfl).2)
  have hA : charge (Ioc 0 1) = 2 := by
    convert (charge_zero_interval_prescriptions zero_lt_one le_rfl).2 using 1; norm_num
  simp_rw [hagree _ (dyadic_elementary _), dyadic_union,
    hagree _ (zero_intervals_elementary le_rfl).2, hA] at h
  have hlim := continuous_coe_real_ereal.continuousAt.tendsto.comp
    dyadic_charge_hasSum.tendsto_sum_nat
  simp only [Function.comp_def, EReal.coe_finsetSum, EReal.coe_one] at hlim
  have hbad := tendsto_nhds_unique h hlim
  norm_num at hbad

alias charge_empty := φ_empty

end ElementaryCharge
end Rudin.Chapter11
