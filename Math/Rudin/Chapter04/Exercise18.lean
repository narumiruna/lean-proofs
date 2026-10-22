module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter04

/-- Thomae's function uses the positive reduced denominator of the rational input. -/
noncomputable def exercise18Function (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ q : ℚ, (q : ℝ) = x then 1 / ((Classical.choose h).den : ℝ) else 0

theorem exercise18_rational_value (q : ℚ) :
    exercise18Function (q : ℝ) = 1 / (q.den : ℝ) := by
  unfold exercise18Function
  split_ifs with h
  · have he : Classical.choose h = q := Rat.cast_injective (Classical.choose_spec h)
    rw [he]
  · exact (h ⟨q, rfl⟩).elim

/-- Agreement with the source's reduced integer-fraction formula. -/
theorem exercise18_reduced_fraction (m n : ℤ) (hn : 0 < n)
    (hcop : Nat.Coprime m.natAbs n.natAbs) :
    exercise18Function ((m : ℝ) / (n : ℝ)) = 1 / (n : ℝ) := by
  have hd := Rat.den_div_eq_of_coprime hn hcop
  have hdr : ((((m : ℚ) / (n : ℚ)).den : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hd
  simpa only [Rat.cast_div, Rat.cast_intCast, hdr] using
    exercise18_rational_value ((m : ℚ) / (n : ℚ))

theorem exercise18_irrational_value {x : ℝ} (hx : Irrational x) :
    exercise18Function x = 0 := by
  unfold exercise18Function
  rw [dite_eq_right]
  rintro ⟨q, rfl⟩
  exact hx.ne_rat q rfl

theorem exercise18_zero : exercise18Function 0 = 1 := by
  simpa using exercise18_rational_value 0

/-- In a bounded interval there are only finitely many rationals of bounded denominator. -/
theorem exercise18_finite_denominators (B N : ℕ) :
    {x : ℝ | ∃ q : ℚ, (q : ℝ) = x ∧ |x| ≤ B ∧ q.den ≤ N}.Finite := by
  let s : Set (ℤ × ℕ) := Icc (-(B * N : ℤ)) (B * N : ℤ) ×ˢ Icc 0 N
  have hs : s.Finite := (finite_Icc _ _).prod (finite_Icc _ _)
  refine (hs.image (fun p => (p.1 : ℝ) / (p.2 : ℝ))).subset ?_
  rintro x ⟨q, rfl, hq, hd⟩
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have he : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
    rw [Rat.cast_def, div_mul_cancel₀ _ (ne_of_gt hden)]
  have hn : |(q.num : ℝ)| ≤ (B : ℝ) * N := by
    rw [he, abs_mul, abs_of_pos hden]
    exact mul_le_mul hq (by exact_mod_cast hd) (le_of_lt hden) (Nat.cast_nonneg B)
  have hni : -(B * N : ℤ) ≤ q.num ∧ q.num ≤ (B * N : ℤ) := by
    constructor
    · exact_mod_cast (abs_le.mp hn).1
    · exact_mod_cast (abs_le.mp hn).2
  exact ⟨(q.num, q.den), ⟨hni, ⟨Nat.zero_le _, hd⟩⟩, (Rat.cast_def q).symm⟩

/-- The deleted limit is zero at every real point, not just at irrational points. -/
theorem exercise18_deleted_limit (x : ℝ) :
    Tendsto exercise18Function (𝓝[≠] x) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  obtain ⟨B, hB⟩ := exists_nat_gt (|x| + 1)
  let s := {y : ℝ | ∃ q : ℚ, (q : ℝ) = y ∧ |y| ≤ B ∧ q.den ≤ N}
  have hs : s.Finite := exercise18_finite_denominators B N
  have hav : (s \ {x})ᶜ ∈ 𝓝 x :=
    hs.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  have hball : ∀ᶠ y in 𝓝[≠] x, dist y x < 1 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x (by norm_num))
  filter_upwards [nhdsWithin_le_nhds hav, self_mem_nhdsWithin, hball] with y hy hyx hxy
  have hyB : |y| ≤ B := by
    have := abs_add_le (y - x) x
    rw [sub_add_cancel] at this
    rw [Real.dist_eq] at hxy
    linarith
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = y
  · obtain ⟨q, rfl⟩ := hrat
    have hd : N < q.den := by
      by_contra! hd
      exact hy ⟨⟨q, rfl, hyB, hd⟩, hyx⟩
    rw [exercise18_rational_value, Real.dist_eq, sub_zero,
      abs_of_pos (one_div_pos.mpr (by exact_mod_cast q.den_pos))]
    exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1)
      (by exact_mod_cast hd)).trans_lt hN
  · simp [exercise18Function, hrat, hε]

theorem exercise18_irrational_continuity {x : ℝ} (hx : Irrational x) :
    ContinuousAt exercise18Function x := by
  rw [continuousAt_iff_punctured_nhds]
  rw [exercise18_irrational_value hx]
  exact exercise18_deleted_limit x

/-- Both one-sided limits at a rational are zero, while its value is strictly positive. -/
theorem exercise18_rational_simple_discontinuity (q : ℚ) :
    Tendsto exercise18Function (𝓝[<] (q : ℝ)) (𝓝 0) ∧
    Tendsto exercise18Function (𝓝[>] (q : ℝ)) (𝓝 0) ∧
    0 < exercise18Function (q : ℝ) ∧ ¬ ContinuousAt exercise18Function (q : ℝ) := by
  have hp : 0 < exercise18Function (q : ℝ) := by
    rw [exercise18_rational_value]
    exact one_div_pos.mpr (by exact_mod_cast q.den_pos)
  refine ⟨(exercise18_deleted_limit (q : ℝ)).mono_left ?_,
    (exercise18_deleted_limit (q : ℝ)).mono_left ?_, hp, ?_⟩
  · exact nhdsWithin_mono _ fun y hy => ne_of_lt hy
  · exact nhdsWithin_mono _ fun y hy => ne_of_gt hy
  · intro hc
    have he := tendsto_nhds_unique (exercise18_deleted_limit (q : ℝ))
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
    exact (ne_of_gt hp) he.symm

end Rudin.Chapter04
