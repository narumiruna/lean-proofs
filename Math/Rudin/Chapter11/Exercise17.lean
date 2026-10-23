module

public import Math.Rudin.Chapter11.Exercise13
public import Mathlib.Data.Int.Interval

/-! # Chapter 11, Exercise 17

Bessel's inequality for the normalized sine classes is applied to the Lebesgue
indicator of `E`. Both positive and negative integer frequencies are included.
`NullMeasurableSet` allows every Lebesgue measurable set, not just Borel sets.
The inequality on `E` is pointwise, not merely almost everywhere.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Rudin.Chapter11

theorem exercise17_finite_frequencies {E : Set ℝ}
    (hE : NullMeasurableSet E volume) (hsub : E ⊆ Ioo (-Real.pi) Real.pi)
    (hpos : 0 < volume E) {δ : ℝ} (hδ : 0 < δ) :
    {n : ℤ | ∀ x ∈ E, δ ≤ Real.sin ((n : ℝ) * x)}.Finite := by
  have hsub' : E ⊆ Icc (-Real.pi) Real.pi := hsub.trans Ioo_subset_Icc_self
  have hfin : volume E ≠ ∞ := ne_of_lt <|
    (measure_mono hsub').trans_lt measure_Icc_lt_top
  have hmass : 0 < volume.real E := ENNReal.toReal_pos hpos.ne' hfin
  have hc : 0 < δ * volume.real E := mul_pos hδ hmass
  -- This limit is derived from `Orthonormal.inner_products_summable`, hence Bessel.
  have h := SineL2.tendsto_setIntegral_sine hE hsub'
  have hevent := h.eventually (Ioo_mem_nhds (neg_lt_zero.mpr hc) hc)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have lower (c : ℝ) (hcE : ∀ x ∈ E, δ ≤ Real.sin (c * x)) :
      δ * volume.real E ≤ ∫ x in E, Real.sin (c * x) := by
    have hi : IntegrableOn (fun x : ℝ ↦ Real.sin (c * x)) E :=
      ((by fun_prop : Continuous (fun x : ℝ ↦ Real.sin (c * x))).integrableOn_Icc).mono_set hsub'
    have hle := setIntegral_mono_on₀ (integrableOn_const hfin) hi hE hcE
    simpa [setIntegral_const, mul_comm] using hle
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro n hn
  change ∀ x ∈ E, δ ≤ Real.sin ((n : ℝ) * x) at hn
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      have hbad := lower 0 (by simpa using hn)
      simp only [zero_mul, Real.sin_zero, integral_zero] at hbad
      exact (not_le_of_gt hc hbad).elim
    | succ k =>
      have hk : k < N := by
        by_contra hnot
        have hu := (hN k (by omega)).2
        have hl := lower (k + 1 : ℕ) (by simpa using hn)
        exact (not_le_of_gt hu) hl
      change -(N : ℤ) ≤ (k + 1 : ℕ) ∧ ((k + 1 : ℕ) : ℤ) ≤ N
      constructor <;> omega
  | negSucc k =>
    have hk : k < N := by
      by_contra hnot
      have hu := (hN k (by omega)).1
      have hl := lower (-((k + 1 : ℕ) : ℝ)) (by simpa using hn)
      simp only [neg_mul, Real.sin_neg, integral_neg] at hl
      linarith
    change -(N : ℤ) ≤ Int.negSucc k ∧ Int.negSucc k ≤ N
    constructor <;> omega

end Rudin.Chapter11
