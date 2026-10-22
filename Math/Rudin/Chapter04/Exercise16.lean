module

public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

@[expose] public section
namespace Rudin.Chapter04
open Set Filter Topology

/-- The source floor is regarded as a real-valued function. -/
noncomputable def exercise16Floor (x : ℝ) : ℝ := (⌊x⌋ : ℤ)

/-- The source fractional part. -/
noncomputable def exercise16Frac (x : ℝ) : ℝ := Int.fract x

/-- The endpoint inequalities in the source definition of the integer part. -/
theorem exercise16_floor_spec (x : ℝ) :
    x - 1 < exercise16Floor x ∧ exercise16Floor x ≤ x := by
  exact ⟨by have := Int.lt_floor_add_one x; dsimp [exercise16Floor]; linarith,
    Int.floor_le x⟩

theorem exercise16_frac_spec (x : ℝ) :
    exercise16Frac x = x - exercise16Floor x ∧
      0 ≤ exercise16Frac x ∧ exercise16Frac x < 1 :=
  ⟨rfl, Int.fract_nonneg x, Int.fract_lt_one x⟩

/-- A simple jump has two finite, unequal one-sided limits. -/
def exercise16Jump (f : ℝ → ℝ) (x l r : ℝ) : Prop :=
  Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r) ∧ l ≠ r

/-- At each integer the integer part has a simple jump of size one and is right-continuous. -/
theorem exercise16_floor_integer (n : ℤ) :
    exercise16Floor n = n ∧
      exercise16Jump exercise16Floor n (n - 1) n ∧
      ContinuousWithinAt exercise16Floor (Ici n) n := by
  refine ⟨by simp [exercise16Floor], ?_, ?_⟩
  · exact ⟨tendsto_floor_left' n,
      (tendsto_floor_right' n).mono_left (nhdsWithin_mono _ (Ioi_subset_Ici_self)),
      by linarith⟩
  · change Tendsto (fun x : ℝ => ((⌊x⌋ : ℤ) : ℝ)) (𝓝[≥] (n : ℝ))
      (𝓝 ((⌊(n : ℝ)⌋ : ℤ) : ℝ))
    simpa only [Int.floor_intCast] using (tendsto_floor_right' (α := ℝ) n)

/-- At each integer the fractional part has a simple downward jump and is right-continuous. -/
theorem exercise16_frac_integer (n : ℤ) :
    exercise16Frac n = 0 ∧
      exercise16Jump exercise16Frac n 1 0 ∧
      ContinuousWithinAt exercise16Frac (Ici n) n := by
  refine ⟨by simp [exercise16Frac], ?_, ?_⟩
  · exact ⟨tendsto_fract_left' n,
      (tendsto_fract_right' n).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self),
      one_ne_zero⟩
  · change Tendsto (Int.fract : ℝ → ℝ) (𝓝[≥] (n : ℝ)) (𝓝 (Int.fract (n : ℝ)))
    simpa only [Int.fract_intCast] using (tendsto_fract_right' (α := ℝ) n)

/-- A simple jump is a discontinuity, not a removable discontinuity. -/
theorem exercise16_jump_not_continuous {f : ℝ → ℝ} {x l r : ℝ}
    (h : exercise16Jump f x l r) : ¬ ContinuousAt f x := by
  intro hc
  have hl : l = f x := tendsto_nhds_unique h.1 (hc.mono_left nhdsWithin_le_nhds)
  have hr : r = f x := tendsto_nhds_unique h.2.1 (hc.mono_left nhdsWithin_le_nhds)
  exact h.2.2 (hl.trans hr.symm)

/-- Away from integers both functions are continuous. -/
theorem exercise16_noninteger {x : ℝ} (hx : ¬ ∃ n : ℤ, x = n) :
    ContinuousAt exercise16Floor x ∧ ContinuousAt exercise16Frac x := by
  have hn : x ≠ (⌊x⌋ : ℤ) := fun h => hx ⟨_, h⟩
  refine ⟨?_, continuousAt_fract hn⟩
  exact (continuousOn_floor (α := ℝ) ⌊x⌋).continuousAt
    (Ico_mem_nhds ((Int.floor_le x).lt_of_ne hn.symm) (Int.lt_floor_add_one x))

/-- Exactly the integers are discontinuities of the integer part; all are simple jumps. -/
theorem exercise16_floor_discontinuities (x : ℝ) :
    ¬ ContinuousAt exercise16Floor x ↔ ∃ n : ℤ, x = n := by
  constructor
  · exact fun h => by_contra fun hx => h (exercise16_noninteger hx).1
  · rintro ⟨n, rfl⟩
    exact exercise16_jump_not_continuous (exercise16_floor_integer n).2.1

/-- Exactly the integers are discontinuities of the fractional part; all are simple jumps. -/
theorem exercise16_fractional_discontinuities (x : ℝ) :
    ¬ ContinuousAt exercise16Frac x ↔ ∃ n : ℤ, x = n := by
  constructor
  · exact fun h => by_contra fun hx => h (exercise16_noninteger hx).2
  · rintro ⟨n, rfl⟩
    exact exercise16_jump_not_continuous (exercise16_frac_integer n).2.1

/-- At every other point both one-sided limits equal the function value. -/
theorem exercise16_noninteger_limits {x : ℝ} (hx : ¬ ∃ n : ℤ, x = n) :
    Tendsto exercise16Floor (𝓝[<] x) (𝓝 (exercise16Floor x)) ∧
    Tendsto exercise16Floor (𝓝[>] x) (𝓝 (exercise16Floor x)) ∧
    Tendsto exercise16Frac (𝓝[<] x) (𝓝 (exercise16Frac x)) ∧
    Tendsto exercise16Frac (𝓝[>] x) (𝓝 (exercise16Frac x)) := by
  obtain ⟨hf, hg⟩ := exercise16_noninteger hx
  exact ⟨hf.mono_left nhdsWithin_le_nhds, hf.mono_left nhdsWithin_le_nhds,
    hg.mono_left nhdsWithin_le_nhds, hg.mono_left nhdsWithin_le_nhds⟩

end Rudin.Chapter04
