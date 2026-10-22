module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

namespace Rudin.Chapter04

open Set Metric

/-- Compact versus closed separation, with a strict bound and no nonemptiness assumptions. -/
theorem exercise21_positive_separation {X : Type*} [MetricSpace X]
    {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hd : Disjoint K F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ q ∈ F, δ < dist p q := by
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact ⟨1, by norm_num, by simp⟩
  rcases F.eq_empty_or_nonempty with rfl | hFn
  · exact ⟨1, by norm_num, by simp⟩
  obtain ⟨p₀, hp₀, hmin⟩ :=
    hK.exists_isMinOn hKn (continuous_infDist_pt F).continuousOn
  have hpos : 0 < infDist p₀ F := (hF.notMem_iff_infDist_pos hFn).mp
    (fun hp => Set.disjoint_left.mp hd hp₀ hp)
  refine ⟨infDist p₀ F / 2, half_pos hpos, ?_⟩
  intro p hp q hq
  exact (half_lt_self hpos).trans_le ((hmin hp).trans (infDist_le_dist_of_mem hq))

/-- The horizontal axis, in the product metric on the plane. -/
def exercise21_axis : Set (ℝ × ℝ) := {p | p.2 = 0}

/-- A closed hyperbola approaches the axis at infinity without meeting it. -/
def exercise21_hyperbola : Set (ℝ × ℝ) := {p | p.1 * p.2 = 1}

theorem exercise21_axis_closed : IsClosed exercise21_axis :=
  isClosed_eq continuous_snd continuous_const

theorem exercise21_hyperbola_closed : IsClosed exercise21_hyperbola :=
  isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

theorem exercise21_axis_hyperbola_disjoint :
    Disjoint exercise21_axis exercise21_hyperbola := by
  refine Set.disjoint_left.mpr ?_
  intro p hp hq
  change p.2 = 0 at hp
  change p.1 * p.2 = 1 at hq
  rw [hp, mul_zero] at hq
  norm_num at hq

theorem exercise21_axis_noncompact : ¬ IsCompact exercise21_axis := by
  intro h
  obtain ⟨M, hM⟩ := h.bddAbove_image (f := fun p => p.1) continuous_fst.continuousOn
  have ht := hM (mem_image_of_mem (fun p : ℝ × ℝ => p.1)
    (show (M + 1, 0) ∈ exercise21_axis from rfl))
  dsimp at ht
  linarith

theorem exercise21_hyperbola_noncompact : ¬ IsCompact exercise21_hyperbola := by
  intro h
  obtain ⟨M, hM⟩ := h.bddAbove_image (f := fun p => p.1) continuous_fst.continuousOn
  let t := |M| + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hp : (t, t⁻¹) ∈ exercise21_hyperbola := by
    change t * t⁻¹ = 1
    exact mul_inv_cancel₀ ht.ne'
  have hb := hM (mem_image_of_mem (fun p : ℝ × ℝ => p.1) hp)
  dsimp at hb
  have : M ≤ |M| := le_abs_self M
  dsimp [t] at hb
  linarith

/-- For every proposed positive bound, explicit points violate it. -/
theorem exercise21_axis_hyperbola_no_bound :
    ∀ δ : ℝ, 0 < δ → ∃ p ∈ exercise21_axis, ∃ q ∈ exercise21_hyperbola,
      dist p q < δ := by
  intro δ hδ
  let t := 2 / δ
  have ht : t ≠ 0 := div_ne_zero (by norm_num) hδ.ne'
  refine ⟨(t, 0), rfl, (t, t⁻¹), ?_, ?_⟩
  · change t * t⁻¹ = 1
    exact mul_inv_cancel₀ ht
  · have hi : t⁻¹ = δ / 2 := by dsimp [t]; field_simp
    simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, zero_sub, abs_neg,
      hi, abs_of_pos (half_pos hδ), max_eq_right (le_of_lt (half_pos hδ))]
    exact half_lt_self hδ

/-- Both sets are explicitly closed and noncompact; strict positive separation fails. -/
theorem exercise21_closed_noncompact_failure :
    IsClosed exercise21_axis ∧ IsClosed exercise21_hyperbola ∧
    ¬ IsCompact exercise21_axis ∧ ¬ IsCompact exercise21_hyperbola ∧
    Disjoint exercise21_axis exercise21_hyperbola ∧
    ¬ (∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ exercise21_axis,
      ∀ q ∈ exercise21_hyperbola, δ < dist p q) := by
  refine ⟨exercise21_axis_closed, exercise21_hyperbola_closed,
    exercise21_axis_noncompact, exercise21_hyperbola_noncompact,
    exercise21_axis_hyperbola_disjoint, ?_⟩
  rintro ⟨δ, hδ, hb⟩
  obtain ⟨p, hp, q, hq, hlt⟩ := exercise21_axis_hyperbola_no_bound δ hδ
  exact (hb p hp q hq).not_gt hlt

end Rudin.Chapter04
