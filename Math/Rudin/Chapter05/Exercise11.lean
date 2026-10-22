module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- The symmetric second difference. The first derivative exists on a
neighborhood; only its derivative at the specified point is assumed. -/
theorem exercise11_second_difference_of_hasDerivAt {f d : ℝ → ℝ} {x D : ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, HasDerivAt f (d y) y)
    (hsecond : HasDerivAt d D x) :
    Tendsto (fun h => (f (x + h) + f (x - h) - 2 * f x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 D) := by
  have hp : HasDerivAt (fun h => d (x + h)) D 0 := by
    simpa [Function.comp_def] using hsecond.comp_of_eq 0 ((hasDerivAt_id 0).const_add x) (by simp)
  have hm : HasDerivAt (fun h => d (x - h)) (-D) 0 := by
    simpa [Function.comp_def] using hsecond.comp_of_eq 0 ((hasDerivAt_id 0).const_sub x) (by simp)
  have hD : HasDerivAt (fun h => d (x + h) - d (x - h)) (2 * D) 0 := by
    convert hp.sub hm using 1
    ring
  have hs : Tendsto (fun h => (d (x + h) - d (x - h)) / (2 * h))
      (𝓝[≠] 0) (𝓝 D) := by
    have h := hD.tendsto_slope.div_const 2
    convert h using 1
    · ext h
      simp [slope_def_field]
      ring
    · congr 1
      ring
  have hplus : Tendsto (fun h : ℝ => x + h) (𝓝[≠] 0) (𝓝 x) := by
    have hc : ContinuousAt (fun h : ℝ => x + h) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hminus : Tendsto (fun h : ℝ => x - h) (𝓝[≠] 0) (𝓝 x) := by
    have hc : ContinuousAt (fun h : ℝ => x - h) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hnum : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      HasDerivAt (fun h => f (x + h) + f (x - h) - 2 * f x)
        (d (x + h) - d (x - h)) h := by
    filter_upwards [hplus.eventually hfirst, hminus.eventually hfirst] with h hp hm
    convert ((hp.comp h ((hasDerivAt_id h).const_add x)).add
      (hm.comp h ((hasDerivAt_id h).const_sub x))).sub_const (2 * f x) using 1 <;>
      simp [Function.comp_def, sub_eq_add_neg]
  have hfcont := (hfirst.self_of_nhds).continuousAt
  have hn : Tendsto (fun h => f (x + h) + f (x - h) - 2 * f x)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    convert ((hfcont.tendsto.comp hplus).add (hfcont.tendsto.comp hminus)).sub_const
      (2 * f x) using 1 <;> simp
    ring
  apply HasDerivAt.lhopital_zero_nhdsNE hnum
    (Eventually.of_forall (fun h => by simpa using (hasDerivAt_pow 2 h)))
    ?_ hn ?_ hs
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero (by norm_num) hh
  · simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2 :
      Tendsto (fun h : ℝ => h ^ 2) (𝓝[≠] 0) (𝓝 ((0 : ℝ) ^ 2)))

/-- The usual notation `f''(x)`, with genuine local first derivatives. -/
theorem exercise11_second_difference {f : ℝ → ℝ} {x D : ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hsecond : HasDerivAt (deriv f) D x) :
    Tendsto (fun h => (f (x + h) + f (x - h) - 2 * f x) / h ^ 2)
      (𝓝[≠] 0) (𝓝 D) :=
  exercise11_second_difference_of_hasDerivAt (hfirst.mono (fun _ h => h.hasDerivAt)) hsecond

/-- A differentiable counterexample to the converse. -/
theorem exercise11_counterexample_first (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * |t|) (2 * |x|) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := 0) (g := fun t : ℝ => 2 * |t|)
  · intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · convert (hasDerivAt_id y).mul (hasDerivAt_abs_neg hy) using 1 <;> try rfl
      simp only [id_eq, abs_of_neg hy]
      ring
    · convert (hasDerivAt_id y).mul (hasDerivAt_abs_pos hy) using 1 <;> try rfl
      simp only [id_eq, abs_of_pos hy]
      ring
  · fun_prop
  · fun_prop

/-- The symmetric difference can vanish identically even when the genuine
second derivative fails to exist. -/
theorem exercise11_converse_counterexample :
    Tendsto (fun h : ℝ => ((0 + h) * |0 + h| + (0 - h) * |0 - h| -
      2 * ((0 : ℝ) * |0|)) / h ^ 2) (𝓝[≠] 0) (𝓝 0) ∧
    ¬ DifferentiableAt ℝ (deriv (fun t : ℝ => t * |t|)) 0 := by
  constructor
  · have he : (fun h : ℝ => ((0 + h) * |0 + h| + (0 - h) * |0 - h| -
        2 * ((0 : ℝ) * |0|)) / h ^ 2) = (fun _ => 0) := by
      ext h
      simp
    rw [he]
    exact tendsto_const_nhds
  · have he : deriv (fun t : ℝ => t * |t|) = (fun t => 2 * |t|) :=
      funext (fun t => (exercise11_counterexample_first t).deriv)
    rw [he]
    intro h
    have ha := h.const_mul (1 / 2 : ℝ)
    have he' : (fun t : ℝ => (1 / 2 : ℝ) * (2 * |t|)) = abs := by ext t; ring
    rw [he'] at ha
    exact not_differentiableAt_abs_zero ha

end Rudin.Chapter05
