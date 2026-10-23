module

public import Math.Rudin.Chapter08.Exercise26
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Chapter 8, Exercise 27 -/

@[expose] public section

open Set Filter
open scoped Topology Real

namespace Rudin.Chapter08

/-- Index continuity for a continuous family of nonzero closed curves.
The compact parameter interval includes both endpoints. -/
theorem continuous_family_index {X : Type*} [TopologicalSpace X]
    (H : X → ℝ → ℂ) (hH : Continuous (fun p : X × Icc (0 : ℝ) (2 * Real.pi) ↦
      H p.1 p.2)) (hloop : ∀ x, IsContinuousNonzeroLoop (H x)) :
    Continuous (fun x ↦ continuousCurveIndex (H x) (hloop x)) := by
  let F : X → C(Icc (0 : ℝ) (2 * Real.pi), ℂ) :=
    fun x ↦ ⟨fun t ↦ H x t, (hloop x).continuous.domRestrict⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hH
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨δ, hδ, hl⟩ := (hloop x).lower_bound
  have he : ∀ᶠ y in 𝓝 x, continuousCurveIndex (H y) (hloop y) =
      continuousCurveIndex (H x) (hloop x) := by
    filter_upwards [(hF.continuousAt.eventually (Metric.ball_mem_nhds (F x) hδ))] with y hy
    symm
    apply exercise26_perturbation_extension
    intro t ht
    have hb : dist (F y) (F x) < δ := hy
    have hp := ContinuousMap.dist_apply_le_dist (f := F y) (g := F x) ⟨t, ht⟩
    change dist (H y t) (H x t) ≤ dist (F y) (F x) at hp
    have hp' : ‖H x t - H y t‖ < δ := by
      simpa only [dist_eq_norm, norm_sub_rev] using hp.trans_lt hb
    exact hp'.trans (hl t ht)
  exact continuousAt_const.congr_of_eventuallyEq he

/-- The constant curve has index zero, even if its value lies on the negative axis. -/
theorem continuousCurveIndex_const (c : ℂ) (hc : c ≠ 0)
    (h : IsContinuousNonzeroLoop (fun _ : ℝ ↦ c)) :
    continuousCurveIndex (fun _ : ℝ ↦ c) h = 0 := by
  have hs : IsC1NonzeroLoop (fun _ : ℝ ↦ c) (fun _ ↦ 0) 0 (2 * Real.pi) :=
    ⟨by positivity, rfl, fun t _ ↦ (hasDerivAt_const t c).hasDerivWithinAt,
      continuous_const.continuousOn, fun _ _ ↦ hc⟩
  have hi := exercise26_smooth_agreement h hs
  simp only [curveIndex, zero_div, intervalIntegral.integral_zero] at hi
  exact_mod_cast hi

noncomputable def radialCurve (f : ℂ → ℂ) (r t : ℝ) : ℂ :=
  f (r * Complex.exp (Complex.I * t))

theorem radialCurve_loop {f : ℂ → ℂ} (hf : Continuous f) (hz : ∀ z, f z ≠ 0)
    (r : ℝ) : IsContinuousNonzeroLoop (radialCurve f r) := by
  refine ⟨?_, ?_, fun _ _ ↦ hz _⟩
  · unfold radialCurve
    exact (hf.comp (by fun_prop)).continuousOn
  · unfold radialCurve
    congr 2
    simpa using (exercise23_circle 1).1.closed

/-- The source limit, written in its epsilon-radius form. The norm is the
complex (Euclidean) norm, and the power is the integer power `z⁻ⁿ`. -/
def HasPositiveAsymptoticDegree (f : ℂ → ℂ) (n : ℕ) (c : ℂ) : Prop :=
  0 < n ∧ c ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
    R < ‖z‖ → ‖z ^ (-(n : ℤ)) * f z - c‖ < ε

/-- The epsilon-radius contract is exactly the source limit as `|z| → ∞`. -/
theorem hasPositiveAsymptoticDegree_iff {f : ℂ → ℂ} {n : ℕ} {c : ℂ} :
    HasPositiveAsymptoticDegree f n c ↔ 0 < n ∧ c ≠ 0 ∧
      Tendsto (fun z : ℂ ↦ z ^ (-(n : ℤ)) * f z)
        (Filter.comap norm atTop) (𝓝 c) := by
  unfold HasPositiveAsymptoticDegree
  rw [Metric.tendsto_nhds]
  simp only [dist_eq_norm]
  apply and_congr_right
  intro hn
  apply and_congr_right
  intro hc
  constructor
  · intro h ε hε
    obtain ⟨R, hR⟩ := h ε hε
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨R + 1, fun r hr z hz ↦ hR z ?_⟩
    rw [hz]
    linarith
  · intro h ε hε
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp (h ε hε))
    exact ⟨R, fun z hz ↦ hR ‖z‖ hz.le z rfl⟩

/-- Exercise 27(a), under the hypothetical absence of zeros. -/
theorem exercise27_a {f : ℂ → ℂ} (hf : Continuous f) (hz : ∀ z, f z ≠ 0) :
    continuousCurveIndex (radialCurve f 0) (radialCurve_loop hf hz 0) = 0 := by
  have he : radialCurve f 0 = fun _ ↦ f 0 := by funext t; simp [radialCurve]
  simp only [he]
  apply continuousCurveIndex_const _ (hz 0)

/-- Exercise 27(c). In fact the family is continuous on the whole real line,
so in particular on the source domain `[0,∞)`. -/
theorem exercise27_c {f : ℂ → ℂ} (hf : Continuous f) (hz : ∀ z, f z ≠ 0) :
    ContinuousOn (fun r ↦ continuousCurveIndex (radialCurve f r)
      (radialCurve_loop hf hz r)) (Ici 0) := by
  apply Continuous.continuousOn
  apply continuous_family_index
  unfold radialCurve
  exact hf.comp (by fun_prop)

/-- Multiplication of an integer-speed circle by a nonzero constant leaves
its integral index equal to that integer. -/
theorem scaled_circle_index (a : ℂ) (ha : a ≠ 0) (n : ℤ) :
    ∃ h : IsContinuousNonzeroLoop (fun t : ℝ ↦ a * Complex.exp (Complex.I * n * t)),
      continuousCurveIndex _ h = n := by
  let γ : ℝ → ℂ := fun t ↦ a * Complex.exp (Complex.I * n * t)
  let v : ℝ → ℂ := fun t ↦ a * (Complex.exp (Complex.I * n * t) * (Complex.I * n))
  have hs : IsC1NonzeroLoop γ v 0 (2 * Real.pi) := by
    refine ⟨by positivity, congrArg (a * ·) (exercise23_circle n).1.closed,
      fun t ht ↦ ((exercise23_circle n).1.derivative t ht).const_mul a,
      ?_, fun t _ ↦ mul_ne_zero ha (Complex.exp_ne_zero _)⟩
    exact continuous_const.continuousOn.mul (exercise23_circle n).1.continuous_velocity
  let h : IsContinuousNonzeroLoop γ := ⟨hs.continuous, hs.closed, hs.nonzero⟩
  refine ⟨h, ?_⟩
  have hi := exercise26_smooth_agreement h hs
  have he : curveIndex γ v 0 (2 * Real.pi) = n := by
    rw [← (exercise23_circle n).2]
    unfold curveIndex
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [γ, v]
    exact mul_div_mul_left _ _ ha
  exact_mod_cast hi.trans he

/-- Exercise 27(b), proved directly from the asymptotic estimate and index
stability, while retaining the hypothetical nowhere-zero assumption. -/
theorem exercise27_b {f : ℂ → ℂ} (hf : Continuous f) (hz : ∀ z, f z ≠ 0)
    {n : ℕ} {c : ℂ} (hasym : HasPositiveAsymptoticDegree f n c) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R < r →
      continuousCurveIndex (radialCurve f r) (radialCurve_loop hf hz r) = n := by
  obtain ⟨R, hR⟩ := hasym.2.2 ‖c‖ (norm_pos_iff.mpr hasym.2.1)
  refine ⟨max R 0, le_max_right _ _, fun r hr ↦ ?_⟩
  have hr0 : 0 < r := (le_max_right R 0).trans_lt hr
  have hrR : R < r := (le_max_left R 0).trans_lt hr
  have ha : c * (r : ℂ) ^ n ≠ 0 :=
    mul_ne_zero hasym.2.1 (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr0.ne'))
  obtain ⟨hs, hsi⟩ := scaled_circle_index (c * (r : ℂ) ^ n) ha (n : ℤ)
  have hid (t : ℝ) : c * (r : ℂ) ^ n * Complex.exp (Complex.I * (n : ℤ) * t) =
      c * ((r : ℂ) * Complex.exp (Complex.I * t)) ^ n := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    rw [← mul_assoc]
    congr 2
    ring
  have hclose : ∀ t ∈ Icc 0 (2 * Real.pi),
      ‖c * (r : ℂ) ^ n * Complex.exp (Complex.I * (n : ℤ) * t) - radialCurve f r t‖ <
      ‖c * (r : ℂ) ^ n * Complex.exp (Complex.I * (n : ℤ) * t)‖ := by
    intro t ht
    rw [hid]
    let z : ℂ := r * Complex.exp (Complex.I * t)
    have hnz : ‖z‖ = r := by
      simp [z, Complex.norm_exp_I_mul_ofReal, abs_of_pos hr0]
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hnz ▸ hr0)
    have he := hR z (hnz ▸ hrR)
    have halg : f z - c * z ^ n = z ^ n * (z ^ (-(n : ℤ)) * f z - c) := by
      simp only [zpow_neg, zpow_natCast]
      field_simp
    change ‖c * z ^ n - f z‖ < ‖c * z ^ n‖
    rw [norm_sub_rev, halg, norm_mul, norm_mul, mul_comm ‖c‖]
    exact mul_lt_mul_of_pos_left he (norm_pos_iff.mpr (pow_ne_zero _ hz0))
  exact (exercise26_perturbation_extension hs (radialCurve_loop hf hz r) hclose).symm.trans hsi

/-- All three source index facts under the same hypothetical nowhere-zero
and positive-asymptotic-degree assumptions. Each fact is proved above without
using the zero-existence contradiction. -/
theorem exercise27_index_facts {f : ℂ → ℂ} (hf : Continuous f)
    (hz : ∀ z, f z ≠ 0) {n : ℕ} {c : ℂ}
    (hasym : HasPositiveAsymptoticDegree f n c) :
    continuousCurveIndex (radialCurve f 0) (radialCurve_loop hf hz 0) = 0 ∧
    (∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R < r →
      continuousCurveIndex (radialCurve f r) (radialCurve_loop hf hz r) = n) ∧
    ContinuousOn (fun r ↦ continuousCurveIndex (radialCurve f r)
      (radialCurve_loop hf hz r)) (Ici 0) :=
  ⟨exercise27_a hf hz, exercise27_b hf hz hasym, exercise27_c hf hz⟩

/-- The three index facts contradict positive asymptotic degree. -/
theorem exercise27_zero_existence {f : ℂ → ℂ} (hf : Continuous f)
    {n : ℕ} {c : ℂ} (hasym : HasPositiveAsymptoticDegree f n c) :
    ∃ z : ℂ, f z = 0 := by
  by_contra h
  have hz : ∀ z, f z ≠ 0 := by simpa only [not_exists] using h
  obtain ⟨R, hR, hlarge⟩ := exercise27_b hf hz hasym
  have hi := isPreconnected_Ici.constant (exercise27_c hf hz)
    (show (0 : ℝ) ∈ Ici 0 from le_rfl)
    (show R + 1 ∈ Ici 0 by simp only [mem_Ici]; linarith)
  rw [exercise27_a hf hz, hlarge (R + 1) (by linarith)] at hi
  have : n = 0 := by exact_mod_cast hi.symm
  exact (Nat.ne_of_gt hasym.1) this

/-- The zero-existence conclusion with the source limit in filter notation. -/
theorem exercise27_zero_of_tendsto {f : ℂ → ℂ} (hf : Continuous f)
    {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun z : ℂ ↦ z ^ (-(n : ℤ)) * f z)
      (Filter.comap norm atTop) (𝓝 c)) : ∃ z : ℂ, f z = 0 :=
  exercise27_zero_existence hf (hasPositiveAsymptoticDegree_iff.mpr ⟨hn, hc, hlim⟩)

end Rudin.Chapter08
