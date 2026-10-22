module

public import Math.Rudin.Support.RiemannIntegrability
public import Mathlib.Topology.Instances.CantorSet

/-!
# R06E06: discontinuities in the middle-thirds Cantor set

Source: Rudin, Third Edition, book page 138 (PDF 147).
The standard `cantorSet` is the intersection of the finite middle-thirds
constructions. Its self-similarity proves zero volume. The proved ordinary
Riemann criterion then gives the literal Darboux integral, not only a
Lebesgue integral or an almost-everywhere replacement of the function.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set MeasureTheory Rudin.Support.StieltjesPrototype
open Rudin.Support.RiemannIntegrability

/-- The middle-thirds Cantor set has zero volume, by its two affine copies. -/
theorem exercise06_cantor_null : volume cantorSet = 0 := by
  have hfirst : (fun x : ℝ => x / 3) '' cantorSet = (fun x : ℝ => 3 * x) ⁻¹' cantorSet := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 3 * (x / 3) ∈ cantorSet
      convert hx using 1; ring
    · intro hy
      exact ⟨3 * y, hy, by ring⟩
  have hsecond : (fun x : ℝ => (2 + x) / 3) '' cantorSet =
      (fun x : ℝ => 3 * x) ⁻¹' ((fun x : ℝ => -2 + x) ⁻¹' cantorSet) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change -2 + 3 * ((2 + x) / 3) ∈ cantorSet
      convert hx using 1; ring
    · intro hy
      refine ⟨-2 + 3 * y, hy, ?_⟩
      ring
  have hv₁ : volume ((fun x : ℝ => x / 3) '' cantorSet) =
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    rw [hfirst, Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hv₂ : volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) =
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    rw [hsecond, Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0),
      measure_preimage_add]
    norm_num
  have hle : volume cantorSet ≤ ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    calc
      volume cantorSet = volume ((fun x : ℝ => x / 3) '' cantorSet ∪
          (fun x : ℝ => (2 + x) / 3) '' cantorSet) :=
        congrArg volume cantorSet_eq_union_halves
      _ ≤ _ := (measure_union_le _ _).trans_eq (by rw [hv₁, hv₂])
  have hfin : volume cantorSet ≠ ⊤ := isCompact_cantorSet.measure_lt_top.ne
  have hterm : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hterm, hterm⟩) hle
  simp only [ENNReal.toReal_add hterm hterm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hr
  have hz : (volume cantorSet).toReal = 0 := by
    have hn : 0 ≤ (volume cantorSet).toReal := ENNReal.toReal_nonneg
    linarith
  rw [← ENNReal.ofReal_toReal hfin, hz, ENNReal.ofReal_zero]

/-- Every bounded real function continuous outside the Cantor set is Riemann
integrable. No continuity at Cantor points, including the endpoints, is added. -/
theorem exercise06 {f : ℝ → ℝ} {M : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ M)
    (hc : ∀ x ∈ Icc (0 : ℝ) 1, x ∉ cantorSet →
      ContinuousWithinAt f (Icc (0 : ℝ) 1) x) :
    HasDarbouxRSIntegral f id 0 1 (∫ x in (0 : ℝ)..1, f x) := by
  have hnull : ∀ᵐ x ∂volume, x ∉ cantorSet := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using exercise06_cantor_null
  apply hasDarbouxRSIntegral_of_ae_continuousWithinAt (by norm_num) hb
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem measurableSet_Icc] with x hx hxI
  exact hc x hxI hx

end Rudin.Chapter06
