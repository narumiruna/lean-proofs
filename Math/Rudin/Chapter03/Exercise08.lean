module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Filter Finset Set
open scoped Topology

namespace Rudin.Chapter03

/-- Abel's convergence test for ordinary, possibly conditional, complex series. -/
theorem exercise08_monotone_multiplier (a : ℕ → ℂ) (b : ℕ → ℝ)
    (ha : ∃ s, Tendsto (fun N => ∑ n ∈ range N, a n) atTop (𝓝 s))
    (hb : Monotone b ∨ Antitone b) (hbounded : Bornology.IsBounded (range b)) :
    ∃ s, Tendsto (fun N => ∑ n ∈ range N, a n * (b n : ℂ)) atTop (𝓝 s) := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨C, hC⟩ := hs.cauchySeq.isBounded_range.exists_norm_le
  have hlim : ∃ l, Tendsto b atTop (𝓝 l) := by
    rcases hb with hb | hb
    · exact ⟨iSup b, tendsto_atTop_ciSup hb hbounded.bddAbove⟩
    · exact ⟨iInf b, tendsto_atTop_ciInf hb hbounded.bddBelow⟩
  obtain ⟨l, hl⟩ := hlim
  have hz : Tendsto (fun n => b n - l) atTop (𝓝 0) := by
    simpa using hl.sub_const l
  have hc : CauchySeq (fun N => ∑ n ∈ range N, (b n - l) • a n) := by
    rcases hb with hb | hb
    · exact (show Monotone (fun n => b n - l) from fun _ _ h => sub_le_sub_right (hb h) l).cauchySeq_series_mul_of_tendsto_zero_of_bounded hz
        (fun n => hC _ (mem_range_self n))
    · exact (show Antitone (fun n => b n - l) from fun _ _ h => sub_le_sub_right (hb h) l).cauchySeq_series_mul_of_tendsto_zero_of_bounded hz
        (fun n => hC _ (mem_range_self n))
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨t + l • s, ?_⟩
  convert ht.add (hs.const_smul l) using 1
  ext N
  rw [smul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  simp only [Complex.real_smul, Complex.ofReal_sub]
  ring

end Rudin.Chapter03
