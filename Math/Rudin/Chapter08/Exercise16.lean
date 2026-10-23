module

public import Math.Rudin.Chapter08.Exercise15

/-! # Chapter 8, Exercise 16
Pointwise Fejer convergence for complex Riemann-integrable periodic functions.
Source: book page 199, PDF page 208. -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Rudin.Chapter08

/-- Pointwise Fejer convergence at every point with both one-sided limits.
No almost-everywhere qualification is present. Periodicity includes endpoint limits. -/
theorem exercise16_pointwise_fejer {f : ℝ → ℂ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x : ℝ) {left right : ℂ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 left)) (hr : Tendsto f (𝓝[>] x) (𝓝 right)) :
    Tendsto (fun N => fejerMean f N x) atTop (𝓝 ((left + right) / 2)) := by
  have hminus : Tendsto (fun t : ℝ => x - t) (𝓝[>] 0) (𝓝[<] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.sub ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_lt_self x ht
  have hplus : Tendsto (fun t : ℝ => x + t) (𝓝[>] 0) (𝓝[>] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact lt_add_of_pos_right x ht
  have hg : IntervalIntegrable (fun t => (f (x - t) + f (x + t)) / 2) volume 0 Real.pi :=
    ((fejer_reflected_integrable hp hf x 0 Real.pi).add
      (fejer_translated_integrable hp hf x 0 Real.pi)).div_const 2
  have hlim := fejerKernel_half_limit hg.1
    (((hl.comp hminus).add (hr.comp hplus)).div_const 2)
  simpa only [fejerMean_half_convolution hp hf] using hlim

end Rudin.Chapter08
