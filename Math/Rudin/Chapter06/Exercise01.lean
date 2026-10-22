module

public import Math.Rudin.Support.StieltjesPrototype

/-!
# R06E01: a function supported at one point

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 6.1, book page 138 (PDF page 147). Definitions 6.1–6.2,
book pages 120–122 (PDF pages 129–131), use weakly increasing partition
nodes and extrema on closed subintervals. We use those Darboux sums,
not a measure integral. The interval may be a singleton.

Continuity is relative to `[a,b]`. Thus the theorem includes both endpoints
and requires no properties of the integrator outside the interval.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype

/-- The real function equal to one at `x₀` and zero elsewhere. -/
noncomputable def pointSpike (x₀ x : ℝ) : ℝ := if x = x₀ then 1 else 0

private theorem spike_bounds (x₀ x : ℝ) :
    0 ≤ pointSpike x₀ x ∧ pointSpike x₀ x ≤ 1 := by
  unfold pointSpike
  split_ifs <;> norm_num

private theorem spike_image_nonempty (x₀ : ℝ) {s t : ℝ} (hst : s ≤ t) :
    (pointSpike x₀ '' Icc s t).Nonempty :=
  ⟨_, ⟨s, ⟨le_rfl, hst⟩, rfl⟩⟩

private theorem spike_image_bddBelow (x₀ s t : ℝ) :
    BddBelow (pointSpike x₀ '' Icc s t) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact (spike_bounds x₀ x).1

private theorem spike_image_bddAbove (x₀ s t : ℝ) :
    BddAbove (pointSpike x₀ '' Icc s t) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact (spike_bounds x₀ x).2

private theorem spike_inf (x₀ : ℝ) {s t : ℝ} (hst : s < t) :
    sInf (pointSpike x₀ '' Icc s t) = 0 := by
  apply le_antisymm
  · apply csInf_le (spike_image_bddBelow x₀ s t)
    by_cases hs : s = x₀
    · refine ⟨t, ⟨hst.le, le_rfl⟩, ?_⟩
      simp [pointSpike, ne_of_gt (hs ▸ hst)]
    · exact ⟨s, ⟨le_rfl, hst.le⟩, by simp [pointSpike, hs]⟩
  · apply le_csInf (spike_image_nonempty x₀ hst.le)
    rintro _ ⟨x, _, rfl⟩
    exact (spike_bounds x₀ x).1

private theorem spike_sup_nonneg (x₀ : ℝ) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ sSup (pointSpike x₀ '' Icc s t) :=
  (spike_bounds x₀ s).1.trans
    (le_csSup (spike_image_bddAbove x₀ s t) ⟨s, ⟨le_rfl, hst⟩, rfl⟩)

private theorem spike_sup_le_one (x₀ : ℝ) {s t : ℝ} (hst : s ≤ t) :
    sSup (pointSpike x₀ '' Icc s t) ≤ 1 := by
  apply csSup_le (spike_image_nonempty x₀ hst)
  rintro _ ⟨x, _, rfl⟩
  exact (spike_bounds x₀ x).2

private theorem spike_sup_zero (x₀ : ℝ) {s t : ℝ} (hst : s ≤ t)
    (hx : x₀ ∉ Icc s t) : sSup (pointSpike x₀ '' Icc s t) = 0 := by
  apply le_antisymm
  · apply csSup_le (spike_image_nonempty x₀ hst)
    rintro _ ⟨x, hxt, rfl⟩
    have hne : x ≠ x₀ := by rintro rfl; exact hx hxt
    simp [pointSpike, hne]
  · exact spike_sup_nonneg x₀ hst

private theorem node_mem {a b : ℝ} (p : Partition a b) {i : ℕ} (hi : i ≤ p.n) :
    p.x i ∈ Icc a b := by
  have hm := p.increasing
  constructor
  · simpa only [p.first] using hm (by simp) hi (Nat.zero_le _)
  · simpa only [p.last] using hm hi (by simp) hi

/-- Every lower Darboux sum of the point-supported function is zero. -/
theorem pointSpike_lowerSum {a b : ℝ} (p : Partition a b) (x₀ : ℝ) (α : ℝ → ℝ) :
    lowerSum p (pointSpike x₀) α = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hle := p.increasing (show i ≤ p.n by omega)
    (show i + 1 ≤ p.n by omega) (Nat.le_succ i)
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [spike_inf x₀ hlt, zero_mul]
  · rw [heq, sub_self, mul_zero]

/-- All upper Darboux sums are nonnegative for an interval-monotone integrator. -/
theorem pointSpike_upperSum_nonneg {a b : ℝ} (p : Partition a b) (x₀ : ℝ)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b)) :
    0 ≤ upperSum p (pointSpike x₀) α := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_nonneg (spike_sup_nonneg x₀ (left_isTag p i hi').2)
    (sub_nonneg.mpr (hα (node_mem p (by omega)) (node_mem p (by omega))
      (left_isTag p i hi').2))

private def twoPartition {a b : ℝ} (u : ℝ) (hau : a < u) (hub : u < b) :
    Partition a b where
  n := 2
  pos := by decide
  x := fun i => if i = 0 then a else if i = 1 then u else b
  first := by simp
  last := by simp
  increasing := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    interval_cases i <;> interval_cases j <;> norm_num at * <;> linarith

private def threePartition {a b : ℝ} (u v : ℝ)
    (hau : a < u) (huv : u < v) (hvb : v < b) : Partition a b where
  n := 3
  pos := by decide
  x := fun i => if i = 0 then a else if i = 1 then u else if i = 2 then v else b
  first := by simp
  last := by simp
  increasing := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    interval_cases i <;> interval_cases j <;> norm_num at * <;> linarith

private theorem two_upperSum {a b : ℝ} (u : ℝ) (hau : a < u) (hub : u < b)
    (f α : ℝ → ℝ) :
    upperSum (twoPartition u hau hub) f α =
      sSup (f '' Icc a u) * (α u - α a) +
      sSup (f '' Icc u b) * (α b - α u) := by
  simp [upperSum, twoPartition, Finset.sum_range_succ]

private theorem three_upperSum {a b : ℝ} (u v : ℝ)
    (hau : a < u) (huv : u < v) (hvb : v < b) (f α : ℝ → ℝ) :
    upperSum (threePartition u v hau huv hvb) f α =
      sSup (f '' Icc a u) * (α u - α a) +
      sSup (f '' Icc u v) * (α v - α u) +
      sSup (f '' Icc v b) * (α b - α v) := by
  simp [upperSum, threePartition, Finset.sum_range_succ]

private theorem single_upperSum {a b : ℝ} (hab : a < b) (f α : ℝ → ℝ) :
    upperSum (single hab.le) f α = sSup (f '' Icc a b) * (α b - α a) := by
  simp [upperSum, single]

/-- Isolate `x₀` in `[u,v]`; omit a tail when it has zero length. -/
private theorem isolating_partition {a b x₀ u v : ℝ} (hab : a < b)
    (hau : a ≤ u) (hux : u ≤ x₀) (hxv : x₀ ≤ v) (hvb : v ≤ b) (huv : u < v)
    (hleft : a < u → u < x₀) (hright : v < b → x₀ < v)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b)) :
    ∃ p : Partition a b, upperSum p (pointSpike x₀) α ≤ α v - α u := by
  have hmid : sSup (pointSpike x₀ '' Icc u v) * (α v - α u) ≤ α v - α u := by
    exact (mul_le_mul_of_nonneg_right (spike_sup_le_one x₀ huv.le)
      (sub_nonneg.mpr (hα ⟨hau, by linarith⟩ ⟨by linarith, hvb⟩ huv.le))).trans_eq
      (one_mul _)
  by_cases hua : u = a
  · subst u
    by_cases hv : v = b
    · subst v
      exact ⟨single hab.le, by rw [single_upperSum hab]; exact hmid⟩
    · have hvb' : v < b := lt_of_le_of_ne hvb hv
      have hz := spike_sup_zero x₀ hvb (by
        intro h; exact (not_le_of_gt (hright hvb')) h.1)
      refine ⟨twoPartition v huv hvb', ?_⟩
      rw [two_upperSum, hz, zero_mul, add_zero]
      exact hmid
  · have hau' : a < u := lt_of_le_of_ne hau (Ne.symm hua)
    have hz := spike_sup_zero x₀ hau (by
      intro h; exact (not_le_of_gt (hleft hau')) h.2)
    by_cases hv : v = b
    · subst v
      refine ⟨twoPartition u hau' huv, ?_⟩
      rw [two_upperSum, hz, zero_mul, zero_add]
      exact hmid
    · have hvb' : v < b := lt_of_le_of_ne hvb hv
      have hz' := spike_sup_zero x₀ hvb (by
        intro h; exact (not_le_of_gt (hright hvb')) h.1)
      refine ⟨threePartition u v hau' huv hvb', ?_⟩
      rw [three_upperSum, hz, hz', zero_mul, zero_mul, zero_add, add_zero]
      exact hmid

/-- Continuity at the supported point gives arbitrarily small upper sums,
including when the point is an endpoint. -/
theorem pointSpike_small_upperSum {a b x₀ : ℝ} (hab : a < b)
    (hx : x₀ ∈ Icc a b) {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousWithinAt α (Icc a b) x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Partition a b, upperSum p (pointSpike x₀) α < ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by linarith)
  let u := max a (x₀ - δ / 2)
  let v := min b (x₀ + δ / 2)
  have hau : a ≤ u := le_max_left _ _
  have hux : u ≤ x₀ := max_le hx.1 (by linarith)
  have hxv : x₀ ≤ v := le_min hx.2 (by linarith)
  have hvb : v ≤ b := min_le_left _ _
  have huv : u < v := by
    exact max_lt (lt_min hab (by linarith [hx.1]))
      (lt_min (by linarith [hx.2]) (by linarith))
  have humem : u ∈ Icc a b := ⟨hau, hux.trans hx.2⟩
  have hvmem : v ∈ Icc a b := ⟨hx.1.trans hxv, hvb⟩
  have hud : dist u x₀ < δ := by
    rw [Real.dist_eq]
    apply abs_lt.mpr
    have hu : x₀ - δ / 2 ≤ u := le_max_right _ _
    constructor <;> linarith
  have hvd : dist v x₀ < δ := by
    rw [Real.dist_eq]
    apply abs_lt.mpr
    have hv : v ≤ x₀ + δ / 2 := min_le_right _ _
    constructor <;> linarith
  have huα := hcont humem hud
  have hvα := hcont hvmem hvd
  rw [Real.dist_eq] at huα hvα
  have hsmall : α v - α u < ε := by
    have := (abs_lt.mp huα).1
    have := (abs_lt.mp hvα).2
    linarith
  obtain ⟨p, hp⟩ := isolating_partition hab hau hux hxv hvb huv
    (fun h => max_lt (h.trans_le hux) (by linarith))
    (fun h => lt_min (hxv.trans_lt h) (by linarith)) hα
  exact ⟨p, hp.trans_lt hsmall⟩

/-- The nondegenerate case of R06E01, including either endpoint. -/
theorem exercise01_of_lt {a b x₀ : ℝ} (hab : a < b) (hx : x₀ ∈ Icc a b)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousWithinAt α (Icc a b) x₀) :
    HasDarbouxRSIntegral (pointSpike x₀) α a b 0 := by
  let : Nonempty (Partition a b) := ⟨single hab.le⟩
  refine ⟨hα, ⟨1, ?_⟩, ?_, ?_⟩
  · intro x _
    rw [abs_of_nonneg (spike_bounds x₀ x).1]
    exact (spike_bounds x₀ x).2
  · simp only [pointSpike_lowerSum, Set.range_const, csSup_singleton]
  · apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (Set.range_nonempty _)
    · rintro _ ⟨p, rfl⟩
      exact pointSpike_upperSum_nonneg p x₀ hα
    · intro ε hε
      obtain ⟨p, hp⟩ := pointSpike_small_upperSum hab hx hα hc hε
      exact ⟨_, ⟨p, rfl⟩, hp⟩

/-- R06E01: the actual lower and upper Darboux integrals both equal zero.
The interval may be a singleton. Monotonicity and continuity are only on `[a,b]`. -/
theorem exercise01 {a b x₀ : ℝ} (hab : a ≤ b) (hx : x₀ ∈ Icc a b)
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousWithinAt α (Icc a b) x₀) :
    HasDarbouxRSIntegral (pointSpike x₀) α a b 0 := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · exact exercise01_of_lt hlt hx hα hc
  · exact hasDarbouxRSIntegral_self (pointSpike x₀) α a

end Rudin.Chapter06
