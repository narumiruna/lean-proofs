module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Tactic

/-!
# Exercise 11.5
The literal alternating half-interval functions on the closed interval [0,1].
The value at the midpoint is zero in both parities.
Source: book page 332, PDF page 341. Integrals are Lebesgue integrals.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter Set

noncomputable def exercise05_g (x : ℝ) : ℝ :=
  (Ioc (1 / 2 : ℝ) 1).indicator (fun _ => 1) x

noncomputable def exercise05_f (n : ℕ) (x : ℝ) : ℝ :=
  if n % 2 = 0 then exercise05_g x else exercise05_g (1 - x)

theorem exercise05_even (k : ℕ) (x : ℝ) :
    exercise05_f (2 * k) x = exercise05_g x := by
  simp [exercise05_f]

theorem exercise05_odd (k : ℕ) (x : ℝ) :
    exercise05_f (2 * k + 1) x = exercise05_g (1 - x) := by
  simp [exercise05_f]

theorem exercise05_reflection : (fun x => exercise05_g (1 - x)) =
    (Ico (0 : ℝ) (1 / 2)).indicator (fun _ => 1) := by
  funext x
  have hx : 1 - x ∈ Ioc (1 / 2 : ℝ) 1 ↔ x ∈ Ico (0 : ℝ) (1 / 2) := by
    simp only [mem_Ioc, mem_Ico]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [exercise05_g, indicator_apply, hx]

theorem exercise05_bounds (n : ℕ) (x : ℝ) :
    0 ≤ exercise05_f n x ∧ exercise05_f n x ≤ 1 := by
  simp only [exercise05_f, exercise05_g, indicator_apply]
  split_ifs <;> norm_num

theorem exercise05_lower_limit (x : ℝ) (_hx : x ∈ Icc (0 : ℝ) 1) :
    liminf (fun n => exercise05_f n x) atTop = 0 := by
  have hlo : ∀ᶠ n in atTop, 0 ≤ exercise05_f n x :=
    .of_forall fun n => (exercise05_bounds n x).1
  have hhi : ∀ᶠ n in atTop, exercise05_f n x ≤ 1 :=
    .of_forall fun n => (exercise05_bounds n x).2
  apply le_antisymm
  · apply liminf_le_of_frequently_le _ (isBoundedUnder_of_eventually_ge hlo)
    apply frequently_atTop.mpr
    intro N
    by_cases h : x ≤ 1 / 2
    · refine ⟨2 * N, by omega, ?_⟩
      rw [exercise05_even]
      unfold exercise05_g
      rw [indicator_of_notMem (show x ∉ Ioc (1 / 2 : ℝ) 1 by
        intro hm; exact (not_lt_of_ge h) hm.1)]
    · refine ⟨2 * N + 1, by omega, ?_⟩
      rw [exercise05_odd]
      unfold exercise05_g
      rw [indicator_of_notMem (show 1 - x ∉ Ioc (1 / 2 : ℝ) 1 by
        intro hm; have := hm.1; simp only [not_le] at h; linarith)]
  · exact le_liminf_of_le (isBoundedUnder_of_eventually_le hhi).isCoboundedUnder_ge hlo

theorem exercise05_integrable (n : ℕ) :
    IntegrableOn (exercise05_f n) (Icc (0 : ℝ) 1) := by
  unfold exercise05_f
  split_ifs
  · exact (integrableOn_const (by simp [Real.volume_Icc])).indicator measurableSet_Ioc
  · rw [exercise05_reflection]
    exact (integrableOn_const (by simp [Real.volume_Icc])).indicator measurableSet_Ico

theorem exercise05_integrals (n : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, exercise05_f n x = (1 / 2 : ℝ) := by
  unfold exercise05_f
  split_ifs
  · change ∫ x in Icc (0 : ℝ) 1, (Ioc (1 / 2 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x = _
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset
      (show Ioc (1 / 2 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 by intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)]
    norm_num [integral_const, Measure.real, Real.volume_Ioc]
  · rw [exercise05_reflection]
    rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict_of_subset
      (show Ico (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)]
    norm_num [integral_const, Measure.real, Real.volume_Ico]

end Rudin.Chapter11
