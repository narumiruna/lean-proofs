module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-!
# R01E11: radius and unit factor

Source: Rudin, Exercise 1.11, book page 23 (PDF page 32).
The radius is always the norm. The unit factor is unique exactly when the
number is nonzero. At zero every complex number of norm one is allowed.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- An explicit unit factor, with the value `1` chosen at zero. -/
noncomputable def exercise11_unit (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- The explicit factor gives the requested decomposition, including at zero. -/
theorem exercise11 (z : ℂ) :
    0 ≤ ‖z‖ ∧ ‖exercise11_unit z‖ = 1 ∧
      z = (‖z‖ : ℂ) * exercise11_unit z := by
  refine ⟨norm_nonneg _, ?_⟩
  by_cases hz : z = 0
  · simp [exercise11_unit, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hc : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    simp only [exercise11_unit, ite_eq_right hz]
    constructor
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
      exact div_self hn
    · field_simp

/-- Every allowed radius equals the norm, even when `z = 0`. -/
theorem exercise11_radius_uniqueness {z w : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hw : ‖w‖ = 1) (hz : z = (r : ℂ) * w) :
    r = ‖z‖ := by
  rw [hz, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

/-- For nonzero `z`, every allowed unit factor is the explicit factor. -/
theorem exercise11_unit_uniqueness {z w : ℂ} {r : ℝ}
    (hz : z ≠ 0) (hr : 0 ≤ r) (hw : ‖w‖ = 1)
    (hzw : z = (r : ℂ) * w) : w = exercise11_unit z := by
  have hrz := exercise11_radius_uniqueness hr hw hzw
  subst r
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  apply mul_left_cancel₀ hn
  exact hzw.symm.trans (exercise11 z).2.2

/-- All decompositions of zero: radius zero and any unit factor. -/
theorem exercise11_zero_choices (r : ℝ) (w : ℂ) :
    (0 ≤ r ∧ ‖w‖ = 1 ∧ (0 : ℂ) = (r : ℂ) * w) ↔
      r = 0 ∧ ‖w‖ = 1 := by
  constructor
  · rintro ⟨hr, hw, hz⟩
    exact ⟨by simpa using exercise11_radius_uniqueness hr hw hz, hw⟩
  · rintro ⟨rfl, hw⟩
    simp [hw]

/-- The unit factor is unique if and only if the original number is nonzero. -/
theorem exercise11_unit_unique_iff (z : ℂ) :
    (∃! w : ℂ, ‖w‖ = 1 ∧ z = (‖z‖ : ℂ) * w) ↔ z ≠ 0 := by
  constructor
  · intro h hz
    subst z
    obtain ⟨w, _, hu⟩ := h
    have h1 : (1 : ℂ) = w := hu 1 (by simp)
    have hm : (-1 : ℂ) = w := hu (-1) (by simp)
    have : (1 : ℂ) = -1 := h1.trans hm.symm
    norm_num at this
  · intro hz
    refine ⟨exercise11_unit z, (exercise11 z).2, ?_⟩
    intro w hw
    exact exercise11_unit_uniqueness hz (norm_nonneg _) hw.1 hw.2

end Rudin.Chapter01
