module

public import Mathlib

/-! # Exercise 3.4: upper and lower limits of the parity recurrence.

Index zero is the source's index one. Thus `sequence (2*m+1)` is the
source's even term, and `sequence (2*m+2)` is its next odd term.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- Rudin's parity recursion, with indices shifted by one. -/
noncomputable def exercise04_sequence : ℕ → ℝ
  | 0 => 0
  | n + 1 => if n % 2 = 0 then exercise04_sequence n / 2
      else 1 / 2 + exercise04_sequence n

@[simp] theorem exercise04_initial : exercise04_sequence 0 = 0 := rfl

/-- Source rule `s_(2m) = s_(2m-1)/2`, for every positive source index. -/
theorem exercise04_even_recurrence (m : ℕ) :
    exercise04_sequence (2 * m + 1) = exercise04_sequence (2 * m) / 2 := by
  rw [exercise04_sequence]
  simp

/-- Source rule `s_(2m+1) = 1/2 + s_(2m)`. -/
theorem exercise04_odd_recurrence (m : ℕ) :
    exercise04_sequence (2 * m + 2) = 1 / 2 + exercise04_sequence (2 * m + 1) := by
  change exercise04_sequence ((2 * m + 1) + 1) = _
  rw [exercise04_sequence]
  simp [Nat.add_mod]

/-- The odd and even source terms have explicit geometric formulas. -/
theorem exercise04_formulas (m : ℕ) :
    exercise04_sequence (2 * m) = 1 - (1 / 2 : ℝ) ^ m ∧
    exercise04_sequence (2 * m + 1) = (1 - (1 / 2 : ℝ) ^ m) / 2 := by
  induction m with
  | zero => norm_num [exercise04_sequence]
  | succ m ih =>
    have he : exercise04_sequence (2 * (m + 1)) = 1 - (1 / 2 : ℝ) ^ (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, exercise04_odd_recurrence, ih.2,
        pow_succ]
      ring
    exact ⟨he, by rw [exercise04_even_recurrence, he]⟩

/-- Bounds for the whole sequence and a convergent lower comparison. -/
theorem exercise04_bounds (n : ℕ) :
    0 ≤ exercise04_sequence n ∧ exercise04_sequence n ≤ 1 ∧
      (1 - (1 / 2 : ℝ) ^ (n / 2)) / 2 ≤ exercise04_sequence n := by
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (n / 2) := by positivity
  have hq : (1 / 2 : ℝ) ^ (n / 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hf := exercise04_formulas (n / 2)
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hn : n = 2 * (n / 2) := by omega
    rw [← hn] at hf
    rw [hf.1]
    constructor
    · linarith
    constructor <;> linarith
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [← hn] at hf
    rw [hf.2]
    constructor
    · linarith
    constructor <;> linarith

/-- The source's odd terms tend to one, and its even terms tend to one half. -/
theorem exercise04_subsequence_limits :
    Tendsto (fun m => exercise04_sequence (2 * m)) atTop (𝓝 1) ∧
    Tendsto (fun m => exercise04_sequence (2 * m + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hp : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  constructor
  · simpa only [(exercise04_formulas _).1, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hp
  · simpa only [(exercise04_formulas _).2, sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).div_const 2

/-- The upper limit is one. -/
theorem exercise04_limsup : limsup exercise04_sequence atTop = 1 := by
  have hb : atTop.IsBoundedUnder (· ≤ ·) exercise04_sequence :=
    ⟨1, eventually_map.2 (Eventually.of_forall (fun n => (exercise04_bounds n).2.1))⟩
  have hl : atTop.IsBoundedUnder (· ≥ ·) exercise04_sequence :=
    ⟨0, eventually_map.2 (Eventually.of_forall (fun n => (exercise04_bounds n).1))⟩
  apply le_antisymm
  · exact limsup_le_of_le hl.isCoboundedUnder_le
      (Eventually.of_forall (fun n => (exercise04_bounds n).2.1))
  · apply le_limsup_of_le hb
    intro b h
    have he : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    exact le_of_tendsto exercise04_subsequence_limits.1 (he.eventually h)

/-- The lower limit is one half. -/
theorem exercise04_liminf : liminf exercise04_sequence atTop = (1 / 2 : ℝ) := by
  have hb : atTop.IsBoundedUnder (· ≤ ·) exercise04_sequence :=
    ⟨1, eventually_map.2 (Eventually.of_forall (fun n => (exercise04_bounds n).2.1))⟩
  have hl : atTop.IsBoundedUnder (· ≥ ·) exercise04_sequence :=
    ⟨0, eventually_map.2 (Eventually.of_forall (fun n => (exercise04_bounds n).1))⟩
  apply le_antisymm
  · apply liminf_le_of_le hl
    intro b h
    have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    exact ge_of_tendsto exercise04_subsequence_limits.2 (ho.eventually h)
  · have hd : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
      refine tendsto_atTop.2 (fun b => ?_)
      exact eventually_atTop.2 ⟨2 * b, fun n hn => by omega⟩
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n / 2)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hd
    have hc : Tendsto (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ (n / 2)) / 2)
        atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).div_const 2
    rw [← hc.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun n => (exercise04_bounds n).2.2))
      hc.isBoundedUnder_ge hb.isCoboundedUnder_ge

end Rudin.Chapter03
