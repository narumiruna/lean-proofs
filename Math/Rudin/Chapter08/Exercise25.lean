module

public import Math.Rudin.Chapter08.Exercise24

/-! # Chapter 8, Exercise 25

The proof uses the source quotient `γ₂/γ₁`. The strict bound places this
quotient in the open disk of radius one about one, inside the slit plane.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace Rudin.Chapter08

/-- The quotient curve and its explicit within derivative. -/
theorem IsC1NonzeroLoop.div {γ₁ γ₂ v₁ v₂ : ℝ → ℂ} {a b : ℝ}
    (h₂ : IsC1NonzeroLoop γ₂ v₂ a b) (h₁ : IsC1NonzeroLoop γ₁ v₁ a b) :
    IsC1NonzeroLoop (fun t ↦ γ₂ t / γ₁ t)
      (fun t ↦ (v₂ t * γ₁ t - γ₂ t * v₁ t) / (γ₁ t)^2) a b := by
  refine ⟨h₁.ordered, by rw [h₁.closed, h₂.closed],
    fun t ht ↦ (h₂.derivative t ht).div (h₁.derivative t ht) (h₁.nonzero t ht),
    ?_, fun t ht ↦ div_ne_zero (h₂.nonzero t ht) (h₁.nonzero t ht)⟩
  exact ((h₂.continuous_velocity.mul h₁.continuous).sub
    (h₂.continuous.mul h₁.continuous_velocity)).div
    (h₁.continuous.pow 2) (fun t ht ↦ pow_ne_zero _ (h₁.nonzero t ht))

/-- Logarithmic derivatives subtract under division, and so do their indices. -/
theorem curveIndex_div {γ₁ γ₂ v₁ v₂ : ℝ → ℂ} {a b : ℝ}
    (h₂ : IsC1NonzeroLoop γ₂ v₂ a b) (h₁ : IsC1NonzeroLoop γ₁ v₁ a b) :
    curveIndex (fun t ↦ γ₂ t / γ₁ t)
      (fun t ↦ (v₂ t * γ₁ t - γ₂ t * v₁ t) / (γ₁ t)^2) a b =
      curveIndex γ₂ v₂ a b - curveIndex γ₁ v₁ a b := by
  unfold curveIndex
  rw [← sub_div, ← integral_sub h₂.integrable_logDerivative h₁.integrable_logDerivative]
  congr 1
  apply integral_congr
  intro t ht
  rw [uIcc_of_le h₁.ordered] at ht
  field_simp [h₁.nonzero t ht, h₂.nonzero t ht]

/-- The pointwise strict bound puts the quotient in the slit plane. -/
theorem quotient_mem_slitPlane {z w : ℂ} (hz : z ≠ 0) (h : ‖z - w‖ < ‖z‖) :
    w / z ∈ Complex.slitPlane := by
  have he : 1 - w / z = (z - w) / z := by field_simp
  have hn : ‖1 - w / z‖ < 1 := by
    rw [he, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hz)).mpr h
  have hr := Complex.re_le_norm (1 - w / z)
  have hp : 0 < (w / z).re := by
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  exact Or.inl hp

/-- Strict pointwise perturbations on the same interval preserve the index. -/
theorem exercise25_index_stability {γ₁ γ₂ v₁ v₂ : ℝ → ℂ} {a b : ℝ}
    (h₁ : IsC1NonzeroLoop γ₁ v₁ a b) (h₂ : IsC1NonzeroLoop γ₂ v₂ a b)
    (hclose : ∀ t ∈ Icc a b, ‖γ₁ t - γ₂ t‖ < ‖γ₁ t‖) :
    curveIndex γ₁ v₁ a b = curveIndex γ₂ v₂ a b := by
  have hz := exercise24_zero_index (h₂.div h₁)
    (fun t ht ↦ quotient_mem_slitPlane (h₁.nonzero t ht) (hclose t ht))
  rw [curveIndex_div h₂ h₁, sub_eq_zero] at hz
  exact hz.symm

end Rudin.Chapter08
