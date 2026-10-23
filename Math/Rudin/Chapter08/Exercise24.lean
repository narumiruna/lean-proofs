module

public import Math.Rudin.Chapter08.Exercise23

/-! # Chapter 8, Exercise 24

The slit plane is the complex plane with zero and the negative real axis
removed. A single-valued logarithm on this set is a primitive of `γ'/γ`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace Rudin.Chapter08

/-- A closed curve in the slit plane has zero integral index. -/
theorem exercise24_zero_index {γ v : ℝ → ℂ} {a b : ℝ}
    (h : IsC1NonzeroLoop γ v a b)
    (haxis : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    curveIndex γ v a b = 0 := by
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ Complex.log (γ t))
      (v t / γ t) (Icc a b) t :=
    fun t ht ↦ (h.derivative t ht).clog_real (haxis t ht)
  have hi := integral_eq_sub_of_hasDeriv_right_of_le h.ordered
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ ((hd t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt) h.integrable_logDerivative
  rw [curveIndex, hi, h.closed, sub_self, zero_div]

end Rudin.Chapter08
