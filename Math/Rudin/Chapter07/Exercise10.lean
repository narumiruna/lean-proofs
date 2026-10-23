module

public import Mathlib
public import Math.Rudin.Support.RiemannIntegrability

/-! # Chapter 7, Exercise 10
Source: book page 167, PDF page 176. The index `n` represents the positive
integer `n + 1`. Discontinuities are exactly the rational numbers.
-/

@[expose] public section

namespace Rudin.Chapter07

open Set Filter MeasureTheory
open scoped Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.RiemannIntegrability

noncomputable def fractionalSeriesTerm (n : ℕ) (x : ℝ) : ℝ :=
  Int.fract ((n + 1 : ℕ) * x) / (n + 1 : ℕ) ^ 2

noncomputable def fractionalSeries (x : ℝ) : ℝ := ∑' n, fractionalSeriesTerm n x

theorem fractionalSeries_majorant : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℕ) ^ 2 : ℕ → ℝ) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))

theorem fractionalSeriesTerm_bound (n : ℕ) (x : ℝ) :
    ‖fractionalSeriesTerm n x‖ ≤ 1 / (n + 1 : ℕ) ^ 2 := by
  rw [Real.norm_eq_abs, fractionalSeriesTerm, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (Int.fract_lt_one _).le (sq_nonneg _)

theorem fractionalSeries_summable (x : ℝ) : Summable (fun n ↦ fractionalSeriesTerm n x) :=
  fractionalSeries_majorant.of_norm_bounded (fun n ↦ fractionalSeriesTerm_bound n x)

/-- Uniform convergence of the ordinary ordered partial sums on the whole real line. -/
theorem fractionalSeries_uniform :
    TendstoUniformly (fun N x ↦ ∑ n ∈ Finset.range N, fractionalSeriesTerm n x)
      fractionalSeries atTop :=
  tendstoUniformly_tsum_nat fractionalSeries_majorant fractionalSeriesTerm_bound

theorem fractionalSeries_continuousAt {x : ℝ} (hx : Irrational x) :
    ContinuousAt fractionalSeries x := by
  apply tendsto_tsum_of_dominated_convergence fractionalSeries_majorant
  · intro n
    exact ((continuousAt_fract ((hx.natCast_mul (Nat.succ_ne_zero n)).ne_int _)).comp
      (continuousAt_const.mul continuousAt_id)).div_const _
  · exact Eventually.of_forall fun y n ↦ fractionalSeriesTerm_bound n y

/-- The left limit of each numerator is one at an integer and its value elsewhere. -/
noncomputable def fractionalLeftTerm (n : ℕ) (x : ℝ) : ℝ :=
  (if (n + 1 : ℕ) * x = (⌊(n + 1 : ℕ) * x⌋ : ℤ) then 1
    else Int.fract ((n + 1 : ℕ) * x)) / (n + 1 : ℕ) ^ 2

theorem fractionalLeftTerm_bound (n : ℕ) (x : ℝ) :
    ‖fractionalLeftTerm n x‖ ≤ 1 / (n + 1 : ℕ) ^ 2 := by
  unfold fractionalLeftTerm
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · exact fractionalSeriesTerm_bound n x

theorem fractionalSeries_leftLimit (x : ℝ) :
    Tendsto fractionalSeries (𝓝[<] x) (𝓝 (∑' n, fractionalLeftTerm n x)) := by
  apply tendsto_tsum_of_dominated_convergence fractionalSeries_majorant
  · intro n
    unfold fractionalSeriesTerm fractionalLeftTerm
    split_ifs with h
    · apply Tendsto.div_const
      apply (tendsto_fract_left' ⌊(n + 1 : ℕ) * x⌋).comp
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · rw [← h]
        exact (continuousAt_const.mul continuousAt_id).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        change (n + 1 : ℕ) * y < (⌊(n + 1 : ℕ) * x⌋ : ℝ)
        rw [← h]
        exact mul_lt_mul_of_pos_left hy (by positivity)
    · exact (((continuousAt_fract h).comp
        (continuousAt_const.mul continuousAt_id)).div_const _).tendsto.mono_left nhdsWithin_le_nhds
  · exact Eventually.of_forall fun y n ↦ fractionalSeriesTerm_bound n y

theorem fractionalSeries_not_continuousAt_rat (q : ℚ) :
    ¬ ContinuousAt fractionalSeries (q : ℝ) := by
  have hs := fractionalSeries_majorant.of_norm_bounded
    (fun n ↦ fractionalLeftTerm_bound n (q : ℝ))
  have hle (n : ℕ) : fractionalSeriesTerm n (q : ℝ) ≤ fractionalLeftTerm n (q : ℝ) := by
    unfold fractionalSeriesTerm fractionalLeftTerm
    split_ifs
    · exact div_le_div_of_nonneg_right (Int.fract_lt_one _).le (sq_nonneg _)
    · exact le_rfl
  have hden : q.den - 1 + 1 = q.den := Nat.sub_add_cancel q.pos
  have heq : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have hint : (q.den : ℝ) * (q : ℝ) = (⌊(q.den : ℝ) * (q : ℝ)⌋ : ℝ) := by
    rw [heq, Int.floor_intCast]
  have hlt : fractionalSeriesTerm (q.den - 1) (q : ℝ) <
      fractionalLeftTerm (q.den - 1) (q : ℝ) := by
    unfold fractionalSeriesTerm fractionalLeftTerm
    rw [hden, ite_eq_left hint, heq, Int.fract_intCast]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hsum : fractionalSeries (q : ℝ) < ∑' n, fractionalLeftTerm n (q : ℝ) :=
    Summable.tsum_lt_tsum hle hlt (fractionalSeries_summable _) hs
  intro hc
  have := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (fractionalSeries_leftLimit (q : ℝ))
  exact (ne_of_lt hsum) this

/-- Complete classification, including zero and negative rational numbers. -/
theorem exercise10_discontinuities (x : ℝ) :
    ¬ ContinuousAt fractionalSeries x ↔ x ∈ Set.range (fun q : ℚ ↦ (q : ℝ)) := by
  constructor
  · intro h
    by_contra hn
    exact h (fractionalSeries_continuousAt hn)
  · rintro ⟨q, rfl⟩
    exact fractionalSeries_not_continuousAt_rat q

theorem exercise10_countability : {x | ¬ ContinuousAt fractionalSeries x}.Countable := by
  simpa only [exercise10_discontinuities, Set.ofPred_mem_eq] using Set.countable_range (fun q : ℚ ↦ (q : ℝ))

theorem exercise10_density : Dense {x | ¬ ContinuousAt fractionalSeries x} := by
  have he : {x | ¬ ContinuousAt fractionalSeries x} = Set.range (fun q : ℚ ↦ (q : ℝ)) :=
    Set.ext exercise10_discontinuities
  rw [he]
  exact Rat.denseRange_cast

/-- Actual closed-cell Darboux integrability, not merely Lebesgue integrability. -/
theorem exercise10_riemann_integrability {a b : ℝ} (hab : a ≤ b) :
    HasDarbouxRSIntegral fractionalSeries id a b (∫ x in a..b, fractionalSeries x) := by
  apply hasDarbouxRSIntegral_of_ae_continuousWithinAt hab
    (M := ∑' n : ℕ, 1 / (n + 1 : ℕ) ^ 2)
  · intro x _
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm (fractionalSeries_summable x).norm).trans
      ((fractionalSeries_summable x).norm.tsum_le_tsum (fun n ↦ fractionalSeriesTerm_bound n x)
        fractionalSeries_majorant)
  · have hc : ∀ᵐ x ∂volume, ContinuousAt fractionalSeries x := by
      rw [ae_iff]
      exact exercise10_countability.measure_zero volume
    exact (ae_restrict_of_ae hc).mono fun _ h ↦ h.continuousWithinAt

end Rudin.Chapter07
