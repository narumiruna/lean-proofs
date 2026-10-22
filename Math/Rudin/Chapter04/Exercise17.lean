module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter04

/-- An upward jump in the open source interval; both limits are finite real numbers. -/
def Exercise17Upward (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  x ∈ Ioo a b ∧ ∃ L R : ℝ,
    Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 R) ∧ L < R

/-- The rational triple in Rudin's hint, including the bounds on its endpoints. -/
def Exercise17Triple (f : ℝ → ℝ) (a b x : ℝ) (p q r : ℚ) : Prop :=
  a < (q : ℝ) ∧ (q : ℝ) < x ∧ x < (r : ℝ) ∧ (r : ℝ) < b ∧
    (∀ t ∈ Ioo (q : ℝ) x, f t < (p : ℝ)) ∧
    (∀ t ∈ Ioo x (r : ℝ), (p : ℝ) < f t)

/-- Simple discontinuity means two finite one-sided limits, but not continuity on the domain. -/
def Exercise17Simple (f : ℝ → ℝ) (a b x : ℝ) : Prop :=
  x ∈ Ioo a b ∧ (∃ L R : ℝ,
    Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 R)) ∧
    ¬ ContinuousWithinAt f (Ioo a b) x

/-- Hint (a). -/
theorem exercise17_a {L R : ℝ} (h : L < R) :
    ∃ p : ℚ, L < (p : ℝ) ∧ (p : ℝ) < R := exists_rat_btwn h

/-- Hint (b), for the same previously selected rational p. -/
theorem exercise17_b {f : ℝ → ℝ} {a x L : ℝ} {p : ℚ}
    (hax : a < x) (hL : Tendsto f (𝓝[<] x) (𝓝 L)) (hLp : L < (p : ℝ)) :
    ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < x ∧
      ∀ t ∈ Ioo (q : ℝ) x, f t < (p : ℝ) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hL.eventually (gt_mem_nhds hLp))
  obtain ⟨q, hq, hqx⟩ := exists_rat_btwn (max_lt hax hu)
  exact ⟨q, (le_max_left a u).trans_lt hq, hqx,
    fun t ht => hsub ⟨(le_max_right a u).trans_lt (hq.trans ht.1), ht.2⟩⟩

/-- Hint (c), still for the same rational p. -/
theorem exercise17_c {f : ℝ → ℝ} {b x R : ℝ} {p : ℚ}
    (hxb : x < b) (hR : Tendsto f (𝓝[>] x) (𝓝 R)) (hpR : (p : ℝ) < R) :
    ∃ r : ℚ, x < (r : ℝ) ∧ (r : ℝ) < b ∧
      ∀ t ∈ Ioo x (r : ℝ), (p : ℝ) < f t := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hR.eventually (lt_mem_nhds hpR))
  obtain ⟨r, hxr, hr⟩ := exists_rat_btwn (lt_min hxb hu)
  exact ⟨r, hxr, hr.trans_le (min_le_left b u),
    fun t ht => hsub ⟨ht.1, ht.2.trans_le (hr.le.trans (min_le_right b u))⟩⟩

/-- The construction retains all three conditions in one rational triple. -/
theorem exercise17_rational_triple {f : ℝ → ℝ} {a b x : ℝ}
    (hx : Exercise17Upward f a b x) :
    ∃ p q r : ℚ, Exercise17Triple f a b x p q r ∧
      ∃ L R : ℝ, Tendsto f (𝓝[<] x) (𝓝 L) ∧
        Tendsto f (𝓝[>] x) (𝓝 R) ∧ L < (p : ℝ) ∧ (p : ℝ) < R := by
  obtain ⟨hx, L, R, hL, hR, hLR⟩ := hx
  obtain ⟨p, hLp, hpR⟩ := exercise17_a hLR
  obtain ⟨q, haq, hqx, hq⟩ := exercise17_b hx.1 hL hLp
  obtain ⟨r, hxr, hrb, hr⟩ := exercise17_c hx.2 hR hpR
  exact ⟨p, q, r, ⟨haq, hqx, hxr, hrb, hq, hr⟩, L, R, hL, hR, hLp, hpR⟩

/-- No rational triple in the hint can represent two different points. -/
theorem exercise17_triple_uniqueness {f : ℝ → ℝ} {a b x y : ℝ} {p q r : ℚ}
    (hx : Exercise17Triple f a b x p q r)
    (hy : Exercise17Triple f a b y p q r) : x = y := by
  have hnot : ∀ x y : ℝ, Exercise17Triple f a b x p q r →
      Exercise17Triple f a b y p q r → x < y → False := by
    intro x y hx hy hxy
    have hlow := hy.2.2.2.2.1 ((x + y) / 2) (by constructor <;> linarith [hx.2.1])
    have hhigh := hx.2.2.2.2.2 ((x + y) / 2) (by constructor <;> linarith [hy.2.2.1])
    linarith
  rcases lt_trichotomy x y with h | h | h
  · exact (hnot x y hx hy h).elim
  · exact h
  · exact (hnot y x hy hx h).elim

/-- Countability follows from the literal rational-triple construction. -/
theorem exercise17_upward_jumps_countable (f : ℝ → ℝ) (a b : ℝ) :
    {x | Exercise17Upward f a b x}.Countable := by
  have ht : ∀ v : ℚ × ℚ × ℚ,
      {x | Exercise17Triple f a b x v.1 v.2.1 v.2.2}.Countable := by
    intro v
    apply Set.Subsingleton.countable
    intro x hx y hy
    exact exercise17_triple_uniqueness hx hy
  refine (countable_iUnion ht).mono ?_
  intro x hx
  obtain ⟨p, q, r, htr, _⟩ := exercise17_rational_triple hx
  exact mem_iUnion.mpr ⟨(p, q, r), htr⟩

/-- A right-isolated point of any level region belongs to a countable set. -/
theorem exercise17_isolated_region_countable (s : Set ℝ) :
    {x | x ∈ s ∧ ∀ᶠ t in 𝓝[>] x, t ∉ s}.Countable := by
  refine (countable_setOfPred_isolated_right_within (s := s)).mono ?_
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [inter_comm, nhdsWithin_inter', inf_principal_eq_bot]
  exact hx.2

/-- Points whose value is strictly below their finite right limit are countable. -/
theorem exercise17_value_below_right_limit (f : ℝ → ℝ) :
    {x | ∃ R : ℝ, Tendsto f (𝓝[>] x) (𝓝 R) ∧ f x < R}.Countable := by
  have ht (p : ℚ) := exercise17_isolated_region_countable {x | f x < (p : ℝ)}
  refine (countable_iUnion ht).mono ?_
  rintro x ⟨R, hR, hx⟩
  obtain ⟨p, hxp, hpR⟩ := exists_rat_btwn hx
  refine mem_iUnion.mpr ⟨p, hxp, ?_⟩
  filter_upwards [hR.eventually (lt_mem_nhds hpR)] with t ht
  exact not_lt_of_ge ht.le

/-- All discrepancies between a value and a finite right limit form a countable set. -/
theorem exercise17_right_limit_mismatch_countable (f : ℝ → ℝ) :
    {x | ∃ R : ℝ, Tendsto f (𝓝[>] x) (𝓝 R) ∧ f x ≠ R}.Countable := by
  refine ((exercise17_value_below_right_limit f).union
    (exercise17_value_below_right_limit (fun x => -f x))).mono ?_
  rintro x ⟨R, hR, hx⟩
  rcases lt_or_gt_of_ne hx with h | h
  · exact Or.inl ⟨R, hR, h⟩
  · exact Or.inr ⟨-R, hR.neg, neg_lt_neg h⟩

/-- Downward jumps and removable discontinuities are both at most countable. -/
theorem exercise17_other_simple_types (f : ℝ → ℝ) (a b : ℝ) :
    {x | x ∈ Ioo a b ∧ ∃ L R : ℝ,
      Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 R) ∧ R < L}.Countable ∧
    {x | x ∈ Ioo a b ∧ ∃ L : ℝ,
      Tendsto f (𝓝[<] x) (𝓝 L) ∧ Tendsto f (𝓝[>] x) (𝓝 L) ∧ f x ≠ L}.Countable := by
  constructor
  · refine (exercise17_upward_jumps_countable (fun x => -f x) a b).mono ?_
    rintro x ⟨hx, L, R, hL, hR, hRL⟩
    exact ⟨hx, -L, -R, hL.neg, hR.neg, neg_lt_neg hRL⟩
  · refine (exercise17_right_limit_mismatch_countable f).mono ?_
    rintro x ⟨_, L, _, hR, hx⟩
    exact ⟨L, hR, hx⟩

/-- Every simple discontinuity is a jump or a removable discontinuity. -/
theorem exercise17_simple_discontinuities_countable (f : ℝ → ℝ) (a b : ℝ) :
    {x | Exercise17Simple f a b x}.Countable := by
  have hd := exercise17_other_simple_types f a b
  refine ((exercise17_upward_jumps_countable f a b).union (hd.1.union hd.2)).mono ?_
  rintro x ⟨hx, ⟨L, R, hL, hR⟩, hnc⟩
  rcases lt_trichotomy L R with h | h | h
  · exact Or.inl ⟨hx, L, R, hL, hR, h⟩
  · right; right
    subst R
    refine ⟨hx, L, hL, hR, ?_⟩
    intro he
    have hc : ContinuousAt f x := by
      rw [continuousAt_iff_punctured_nhds, he, ← nhdsLT_sup_nhdsGT]
      exact hL.sup hR
    exact hnc hc.continuousWithinAt
  · exact Or.inr (Or.inl ⟨hx, L, R, hL, hR, h⟩)

/-- The domain-relative version: no limits or discontinuities are required at a or b. -/
theorem exercise17_simple_discontinuities_within_countable (f : ℝ → ℝ) (a b : ℝ) :
    {x | x ∈ Ioo a b ∧ (∃ L R : ℝ,
      Tendsto f (𝓝[Ioo a b ∩ Iio x] x) (𝓝 L) ∧
      Tendsto f (𝓝[Ioo a b ∩ Ioi x] x) (𝓝 R)) ∧
      ¬ ContinuousWithinAt f (Ioo a b) x}.Countable := by
  refine (exercise17_simple_discontinuities_countable f a b).mono ?_
  rintro x ⟨hx, ⟨L, R, hL, hR⟩, hnc⟩
  have hdom : Ioo a b ∈ 𝓝 x := Ioo_mem_nhds hx.1 hx.2
  have heL : 𝓝[Ioo a b ∩ Iio x] x = 𝓝[<] x :=
    nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hdom)
  have heR : 𝓝[Ioo a b ∩ Ioi x] x = 𝓝[>] x :=
    nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hdom)
  exact ⟨hx, ⟨L, R, heL ▸ hL, heR ▸ hR⟩, hnc⟩

end Rudin.Chapter04
