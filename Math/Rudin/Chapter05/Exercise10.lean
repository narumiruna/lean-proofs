module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- Extend a function by zero at the endpoint. A finite limit of the genuine
interior derivatives gives the one-sided derivative, hence the scaled limit. -/
theorem exercise10_scaled_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : ℝ → E} {A : E}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (d x) x)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hl : Tendsto d (𝓝[>] 0) (𝓝 A)) :
    Tendsto (fun x : ℝ => x⁻¹ • f x) (𝓝[>] 0) (𝓝 A) := by
  classical
  let F := Function.update f 0 0
  have he (x : ℝ) (hx : x ≠ 0) : F =ᶠ[𝓝 x] f := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [F, Function.update_of_ne hy]
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (d x) x :=
    fun x hx => (hd x hx).congr_of_eventuallyEq (he x (ne_of_gt hx.1))
  have hfc : ContinuousWithinAt F (Ioo (0 : ℝ) 1) 0 := by
    change Tendsto F (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 (F 0))
    simp only [F, Function.update_self]
    apply (hf.mono_left (nhdsWithin_mono 0 Ioo_subset_Ioi_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [Function.update_of_ne (ne_of_gt hx.1)]
  have hder : Tendsto (deriv F) (𝓝[>] 0) (𝓝 A) := by
    apply hl.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hF x hx).deriv.symm
  have h := hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun x hx => (hF x hx).differentiableAt.differentiableWithinAt) hfc
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) hder
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp h
  have heq : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor <;> intro h <;> grind
  rw [heq] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [slope_def_module, F, Function.update_of_ne (ne_of_gt hx)]

/-- The complex quotient limit at the left endpoint. Both derivatives have
separate finite limits, with a nonzero denominator limit. -/
theorem exercise10_endpoint_quotient {f g d e : ℝ → ℂ} {A B : ℂ}
    (hdf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (d x) x)
    (hdg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (e x) x)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) (hg : Tendsto g (𝓝[>] 0) (𝓝 0))
    (hd : Tendsto d (𝓝[>] 0) (𝓝 A)) (he : Tendsto e (𝓝[>] 0) (𝓝 B)) (hB : B ≠ 0) :
    (∀ᶠ x in 𝓝[>] (0 : ℝ), g x ≠ 0) ∧
    Tendsto (fun x => f x / g x) (𝓝[>] 0) (𝓝 (A / B)) := by
  have hf' := exercise10_scaled_limit hdf hf hd
  have hg' := exercise10_scaled_limit hdg hg he
  constructor
  · filter_upwards [hg'.eventually (eventually_ne_nhds hB)] with x hx hn
    exact hx (by simp [hn])
  · apply (hf'.div hg' hB).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change (x⁻¹ • f x) / (x⁻¹ • g x) = f x / g x
    simp only [Algebra.smul_def]
    exact mul_div_mul_left _ _ ((map_ne_zero (algebraMap ℝ ℂ)).mpr
      (inv_ne_zero (ne_of_gt hx)))

/-- The denominator in Rudin's Example 5.18. -/
noncomputable def exercise10_example_g (x : ℝ) : ℂ :=
  (x : ℂ) + (x : ℂ) ^ 2 * Complex.exp (((x : ℂ) ^ 2)⁻¹ * Complex.I)

/-- Its actual derivative, not a value of `deriv` supplied by a default. -/
theorem exercise10_example_derivative {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt exercise10_example_g
      (1 + (2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)) *
        Complex.exp (((x : ℂ) ^ 2)⁻¹ * Complex.I)) x := by
  have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hh := (hasDerivAt_id (x : ℂ)).add
    (((hasDerivAt_id (x : ℂ)).pow 2).mul
      (((((hasDerivAt_id (x : ℂ)).pow 2).inv (pow_ne_zero 2 hz)).mul_const
        Complex.I).cexp))
  have hc : HasDerivAt (fun z : ℂ => z + z ^ 2 * Complex.exp ((z ^ 2)⁻¹ * Complex.I))
      (1 + (2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)) *
        Complex.exp (((x : ℂ) ^ 2)⁻¹ * Complex.I)) (x : ℂ) := by
    convert hh using 1
    · ext z
      simp
    · simp only [Pi.pow_apply, Pi.inv_apply, id_eq, Nat.cast_ofNat,
        show 2 - 1 = (1 : ℕ) from rfl, pow_one, mul_one]
      field_simp
      ring
  exact hc.comp_ofReal

/-- The derivative in Example 5.18 is unbounded near the endpoint. -/
theorem exercise10_example_derivative_bound {x : ℝ} (hx : 0 < x) :
    2 / x - 2 * x - 1 ≤ ‖deriv exercise10_example_g x‖ := by
  rw [(exercise10_example_derivative (ne_of_gt hx)).deriv]
  let z : ℂ := 2 * (x : ℂ) - 2 * Complex.I / (x : ℂ)
  let w : ℂ := Complex.exp (((x : ℂ) ^ 2)⁻¹ * Complex.I)
  have hw : ‖w‖ = 1 := by
    simpa only [w, ← Complex.ofReal_pow, ← Complex.ofReal_inv] using
      Complex.norm_exp_ofReal_mul_I ((x ^ 2)⁻¹)
  have h1 := norm_sub_norm_le (2 * Complex.I / (x : ℂ)) (2 * (x : ℂ))
  have h2 := norm_sub_norm_le (z * w) (-1)
  have hn1 : ‖2 * Complex.I / (x : ℂ)‖ = 2 / x := by
    simp [Complex.norm_I, Complex.norm_real, abs_of_pos hx]
  have hn2 : ‖2 * (x : ℂ)‖ = 2 * x := by
    simp [Complex.norm_real, abs_of_pos hx]
  rw [hn1, hn2, norm_sub_rev] at h1
  have hn : ‖z * w - (-1 : ℂ)‖ = ‖1 + z * w‖ := by congr 1; ring
  rw [norm_mul, hw, mul_one, norm_neg, norm_one, hn] at h2
  change 2 / x - 2 * x - 1 ≤ ‖1 + z * w‖
  linarith

/-- Comparison with Example 5.18: its denominator derivative has no finite
limit at all. The exercise assumes separate finite derivative limits, not
only convergence of the derivative quotient as in that example. -/
theorem exercise10_comparison (B : ℂ) :
    ¬ Tendsto (deriv exercise10_example_g) (𝓝[>] 0) (𝓝 B) := by
  intro h
  have hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖deriv exercise10_example_g x‖ < ‖B‖ + 1 :=
    h.norm.eventually (eventually_lt_nhds (show ‖B‖ < ‖B‖ + 1 by linarith))
  have hi : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖B‖ + 4 < x⁻¹ :=
    tendsto_inv_nhdsGT_zero.eventually (eventually_gt_atTop (‖B‖ + 4))
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < 1 ∧
      ‖deriv exercise10_example_g x‖ < ‖B‖ + 1 ∧ ‖B‖ + 4 < x⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hb, hi] with x hx hb hi
    exact ⟨hx.1, hx.2, hb, hi⟩
  obtain ⟨x, hx, hsmall, hbound, hinv⟩ := hev.exists
  have he := exercise10_example_derivative_bound hx
  rw [div_eq_mul_inv] at he
  have hn := norm_nonneg B
  linarith

end Rudin.Chapter05
