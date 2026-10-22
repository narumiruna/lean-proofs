module

public import Math.Rudin.Chapter06.Exercise07
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# Chapter 6, Exercise 8

The integral test uses ordered natural partial sums. Nonnegativity proves the
bridge to `Summable`; unconditional summability is not an extra hypothesis.
Monotonicity supplies actual proper Riemann integrals at every truncation.
Source: book pages 138–139, PDF pages 147–148.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open Rudin.Support.StieltjesPrototype Rudin.Support.RiemannIntegrability
open scoped Topology

/-- Ordinary numerical series convergence means convergence of ordered partial sums. -/
def OrdinarySeriesConverges (u : ℕ → ℝ) : Prop :=
  ∃ s : ℝ, Tendsto (fun n ↦ ∑ i ∈ Finset.range n, u i) atTop (𝓝 s)

/-- For nonnegative terms only, ordinary convergence and summability agree. -/
theorem ordinarySeriesConverges_iff_summable_of_nonneg {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) : OrdinarySeriesConverges u ↔ Summable u := by
  constructor
  · rintro ⟨s, hs⟩
    exact (summable_iff_not_tendsto_nat_atTop_of_nonneg hu).mpr
      (not_tendsto_atTop_of_tendsto_nhds hs)
  · intro hs
    exact ⟨∑' n, u n, hs.hasSum.tendsto_sum_nat⟩

/-- The local Riemann integrability in the exercise is automatic from monotonicity.
The singleton truncation is included. -/
theorem exercise08_proper {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 1))
    {b : ℝ} (hb : 1 ≤ b) :
    HasDarbouxRSIntegral f id 1 b (∫ x in 1..b, f x) :=
  hasDarbouxRSIntegral_of_antitoneOn hb (hf.mono Icc_subset_Ici_self)

/-- **Integral test**, in both directions, for the ordinary series starting at 1. -/
theorem exercise08_integral_test {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 1))
    (hn : ∀ x ∈ Ici 1, 0 ≤ f x) :
    ImproperRiemannIntegrableTop f 1 ↔
      OrdinarySeriesConverges (fun n : ℕ ↦ f ((n : ℝ) + 1)) := by
  have hn' (n : ℕ) : 0 ≤ f ((n : ℝ) + 1) := hn _ (by simp)
  have hf' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_one] using hf
  have hn'' : ∀ x ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ f x := by
    intro x hx
    exact hn x (by simpa only [mem_Ici, Nat.cast_one] using hx.le)
  rw [ordinarySeriesConverges_iff_summable_of_nonneg hn']
  constructor
  · rintro ⟨v, hv⟩
    have hi := integrableOn_of_improperRiemannTop_nonneg hv hn
    have hs := hf'.summable_of_integrableOn_Ioi (N := 1)
      (by simpa only [Nat.cast_one] using hi) hn''
    have hshift := (summable_nat_add_iff 1).mpr hs
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  · intro hs
    have hs' : Summable (fun n : ℕ ↦ f (n + 1 : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hs
    have hi : IntegrableOn f (Ioi 1) := by
      simpa only [Nat.cast_one] using
        hf'.integrableOn_Ioi_of_summable_comp_add (N := 1) hs' hn''
    exact ⟨_, improperRiemannTop_of_integrableOn (fun _ hb ↦ exercise08_proper hf hb) hi⟩

end Rudin.Chapter06
