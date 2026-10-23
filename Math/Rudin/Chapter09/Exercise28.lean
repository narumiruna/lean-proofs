module

public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-! # R09E28: differentiation does not commute with a parameter integral
Book pages 242–243, PDF pages 251–252. The min/max profile is proved equal
to all three literal source pieces, including their shared endpoints.
-/
@[expose] public section
namespace Rudin.Chapter09
open Filter Topology Set MeasureTheory

noncomputable def exercise28Tent (x r : ℝ) : ℝ := max 0 (min x (2*r-x))
noncomputable def exercise28Phi (x t : ℝ) : ℝ :=
  if t < 0 then -exercise28Tent x (Real.sqrt |t|) else exercise28Tent x (Real.sqrt |t|)

/-- The increasing closed piece. -/
theorem exercise28_tent_left {x r : ℝ} (hx : 0 ≤ x) (hxr : x ≤ r) :
    exercise28Tent x r = x := by
  unfold exercise28Tent
  rw [min_eq_left (by linarith), max_eq_right hx]

/-- The decreasing closed piece; at x=r both formulas agree. -/
theorem exercise28_tent_right {x r : ℝ} (hx : r ≤ x) (hxr : x ≤ 2*r) :
    exercise28Tent x r = -x+2*r := by
  unfold exercise28Tent
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  ring

theorem exercise28_tent_outside {x r : ℝ} (hx : x ≤ 0 ∨ 2*r ≤ x) :
    exercise28Tent x r = 0 := by
  unfold exercise28Tent
  rw [max_eq_left]
  rcases hx with hx | hx
  · exact (min_le_left _ _).trans hx
  · exact (min_le_right _ _).trans (by linarith)

theorem exercise28_source_nonnegative {x t : ℝ} (ht : 0 ≤ t) :
    (0 ≤ x ∧ x ≤ Real.sqrt t → exercise28Phi x t = x) ∧
    (Real.sqrt t ≤ x ∧ x ≤ 2*Real.sqrt t → exercise28Phi x t = -x+2*Real.sqrt t) ∧
    ((¬ (0 ≤ x ∧ x ≤ Real.sqrt t)) ∧
      (¬ (Real.sqrt t ≤ x ∧ x ≤ 2*Real.sqrt t)) → exercise28Phi x t = 0) := by
  simp only [exercise28Phi, not_lt.mpr ht, ite_false, abs_of_nonneg ht]
  refine ⟨fun h => exercise28_tent_left h.1 h.2,
    fun h => exercise28_tent_right h.1 h.2, ?_⟩
  intro h
  apply exercise28_tent_outside
  by_cases hx : 0 ≤ x
  · right
    have hx' : Real.sqrt t < x := lt_of_not_ge (fun hh => h.1 ⟨hx,hh⟩)
    exact le_of_not_gt (fun hh => h.2 ⟨hx'.le,hh.le⟩)
  · exact Or.inl (le_of_not_ge hx)

theorem exercise28_source_negative {x t : ℝ} (ht : t < 0) :
    exercise28Phi x t = -exercise28Phi x |t| := by
  simp [exercise28Phi, ht, not_lt.mpr (abs_nonneg t), abs_abs]

@[simp] theorem exercise28_tent_zero (x : ℝ) : exercise28Tent x 0 = 0 := by
  apply exercise28_tent_outside
  rcases le_total x 0 with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

@[simp] theorem exercise28_phi_zero (x : ℝ) : exercise28Phi x 0 = 0 := by
  simp [exercise28Phi]

theorem exercise28_tent_bound {x r : ℝ} (hr : 0 ≤ r) :
    0 ≤ exercise28Tent x r ∧ exercise28Tent x r ≤ r := by
  refine ⟨le_max_left _ _, max_le hr ?_⟩
  rcases le_total x r with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem exercise28_phi_bound (x t : ℝ) : |exercise28Phi x t| ≤ Real.sqrt |t| := by
  obtain ⟨hn,hb⟩ := exercise28_tent_bound (x := x) (Real.sqrt_nonneg |t|)
  unfold exercise28Phi
  split_ifs <;> simpa [abs_of_nonneg hn] using hb

theorem exercise28_tent_continuous : Continuous (fun p : ℝ × ℝ => exercise28Tent p.1 p.2) := by
  unfold exercise28Tent
  fun_prop

/-- Joint continuity, including every point of the entire t=0 axis. -/
theorem exercise28_continuous : Continuous (fun p : ℝ × ℝ => exercise28Phi p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hc : Continuous (fun q : ℝ × ℝ => exercise28Tent q.1 (Real.sqrt |q.2|)) := by
    unfold exercise28Tent
    fun_prop
  by_cases ht : p.2 = 0
  · change Tendsto _ _ (𝓝 (exercise28Phi p.1 p.2))
    rw [ht, exercise28_phi_zero]
    apply squeeze_zero_norm (fun q : ℝ × ℝ => exercise28_phi_bound q.1 q.2)
    convert (Real.continuous_sqrt.comp
      (continuous_snd : Continuous (fun q : ℝ × ℝ => q.2)).abs).continuousAt.tendsto (x := p) using 1
    · rfl
    · simp [ht]
  · by_cases hn : p.2 < 0
    · apply hc.continuousAt.neg.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (gt_mem_nhds hn)] with q hq
      simp [exercise28Phi, hq]
    · have hp : 0 < p.2 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm ht)
      apply hc.continuousAt.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds hp)] with q hq
      simp [exercise28Phi, not_lt.mpr hq.le]

/-- For a fixed positive x, the moving support is eventually to its left. -/
theorem exercise28_eventually_zero (x : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), exercise28Phi x t = 0 := by
  by_cases hx : x ≤ 0
  · exact Filter.Eventually.of_forall (fun t => by
      have h := exercise28_tent_outside (r := Real.sqrt |t|) (Or.inl hx)
      simp [exercise28Phi, h])
  · have hx : 0 < x := lt_of_not_ge hx
    have hc : ContinuousAt (fun t : ℝ => 2 * Real.sqrt |t|) 0 := by fun_prop
    have he : ∀ᶠ t in 𝓝 (0 : ℝ), 2 * Real.sqrt |t| < x :=
      hc.eventually (gt_mem_nhds (by simpa using hx))
    filter_upwards [he] with t ht
    have h := exercise28_tent_outside (x := x) (Or.inr ht.le)
    simp [exercise28Phi, h]

/-- This is an actual derivative, not a value assigned by total `deriv`. -/
theorem exercise28_parameter_partial (x : ℝ) : HasDerivAt (fun t => exercise28Phi x t) 0 0 := by
  exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (exercise28_eventually_zero x)

theorem exercise28_slice_continuous (t : ℝ) : Continuous (fun x => exercise28Phi x t) :=
  exercise28_continuous.comp (continuous_id.prodMk continuous_const)

theorem exercise28_slice_integrable (t a b : ℝ) :
    IntervalIntegrable (fun x => exercise28Phi x t) volume a b :=
  (exercise28_slice_continuous t).intervalIntegrable a b

/-- The area of the literal triangular profile, with ordered real endpoints. -/
theorem exercise28_tent_integral {r : ℝ} (hr : 0 ≤ r) (hr1 : 2*r ≤ 1) :
    (∫ x in (-1 : ℝ)..(1 : ℝ), exercise28Tent x r) = r^2 := by
  have hc : Continuous (fun x => exercise28Tent x r) :=
    exercise28_tent_continuous.comp (continuous_id.prodMk continuous_const)
  have hi (a b : ℝ) := hc.intervalIntegrable (μ := volume) a b
  have h0 : (∫ x in (-1 : ℝ)..(0 : ℝ), exercise28Tent x r) = 0 := by
    calc
      _ = ∫ _ in (-1 : ℝ)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact exercise28_tent_outside (Or.inl hx.2)
      _ = 0 := by simp
  have h1 : (∫ x in (0 : ℝ)..r, exercise28Tent x r) = r^2/2 := by
    calc
      _ = ∫ x in (0 : ℝ)..r, x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hr] at hx
        exact exercise28_tent_left hx.1 hx.2
      _ = _ := by rw [integral_id]; ring
  have h2 : (∫ x in r..(2*r), exercise28Tent x r) = r^2/2 := by
    calc
      _ = ∫ x in r..(2*r), (2*r-x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : r ≤ 2*r)] at hx
        change exercise28Tent x r = 2*r-x
        rw [exercise28_tent_right hx.1 hx.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun _ => 2*r) (g := fun x => x)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        ring
  have h3 : (∫ x in (2*r)..(1 : ℝ), exercise28Tent x r) = 0 := by
    calc
      _ = ∫ _ in (2*r)..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hr1] at hx
        exact exercise28_tent_outside (Or.inr hx.1)
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1), h0,
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r 1), h1,
    ← intervalIntegral.integral_add_adjacent_intervals (hi r (2*r)) (hi (2*r) 1), h2, h3]
  ring

theorem exercise28_interval_value {t : ℝ} (ht : |t| < 1/4) :
    (∫ x in (-1 : ℝ)..(1 : ℝ), exercise28Phi x t) = t := by
  have hr : 2 * Real.sqrt |t| ≤ 1 := by
    have hs : Real.sqrt |t| < (1/2 : ℝ) :=
      (Real.sqrt_lt (abs_nonneg t) (by norm_num)).mpr (by norm_num; exact ht)
    linarith
  have he := exercise28_tent_integral (Real.sqrt_nonneg |t|) hr
  rw [Real.sq_sqrt (abs_nonneg t)] at he
  by_cases hn : t < 0
  · simp only [exercise28Phi, hn, ite_true, intervalIntegral.integral_neg, he]
    rw [abs_of_neg hn, neg_neg]
  · simp only [exercise28Phi, hn, ite_false]
    rw [he, abs_of_nonneg (le_of_not_gt hn)]

open Rudin.Support.StieltjesPrototype

/-- The source integral is defined by the supremum of the actual lower sums.
The partition endpoints are the ordered real numbers -1 and 1. -/
noncomputable def exercise28Integral (t : ℝ) : ℝ :=
  sSup (Set.range fun p : Partition (-1 : ℝ) (1 : ℝ) =>
    lowerSum p (fun x => exercise28Phi x t) id)

/-- Literal closed-cell Darboux bridge, not merely Bochner integrability. -/
theorem exercise28_darboux_bridge (t : ℝ) :
    HasDarbouxRSIntegral (fun x => exercise28Phi x t) id (-1 : ℝ) (1 : ℝ)
      (∫ x in (-1 : ℝ)..(1 : ℝ), exercise28Phi x t) := by
  simpa only [← Real.volume_eq_stieltjes_id,
    show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl] using
    Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
      (show (-1 : ℝ) ≤ 1 by norm_num) (exercise28_slice_continuous t).continuousOn

theorem exercise28_integral_bridge (t : ℝ) :
    exercise28Integral t = ∫ x in (-1 : ℝ)..(1 : ℝ), exercise28Phi x t :=
  (exercise28_darboux_bridge t).2.2.1

theorem exercise28_source_integral (t : ℝ) :
    HasDarbouxRSIntegral (fun x => exercise28Phi x t) id (-1 : ℝ) (1 : ℝ)
      (exercise28Integral t) ∧
    HasRSIntegral (fun x => exercise28Phi x t) id (-1 : ℝ) (1 : ℝ)
      (exercise28Integral t) := by
  rw [exercise28_integral_bridge]
  exact ⟨exercise28_darboux_bridge t,
    Rudin.Support.StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral
      (by norm_num) (exercise28_darboux_bridge t)⟩

theorem exercise28_integral_value {t : ℝ} (ht : |t| < 1/4) : exercise28Integral t = t := by
  rw [exercise28_integral_bridge, exercise28_interval_value ht]

theorem exercise28_integral_derivative : HasDerivAt exercise28Integral 1 0 := by
  apply (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq
  have he : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1/4 :=
    (continuous_abs.continuousAt).eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1/4))
  filter_upwards [he] with t ht
  exact exercise28_integral_value ht

/-- The integral of the actual parameter partial has literal Darboux value zero. -/
theorem exercise28_partial_integral :
    HasDarbouxRSIntegral (fun x => deriv (fun t => exercise28Phi x t) 0)
      id (-1 : ℝ) (1 : ℝ) 0 := by
  simp_rw [(exercise28_parameter_partial _).deriv]
  simpa only [← Real.volume_eq_stieltjes_id,
    show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl, intervalIntegral.integral_zero] using
    Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
      (show (-1 : ℝ) ≤ 1 by norm_num) (continuous_const (y := (0 : ℝ))).continuousOn

/-- Both sides are genuine: derivative of the source integral is 1; the
source Riemann integral of the parameter derivative is 0. -/
theorem exercise28_failed_interchange :
    HasDerivAt exercise28Integral 1 0 ∧
    HasDarbouxRSIntegral (fun x => deriv (fun t => exercise28Phi x t) 0)
      id (-1 : ℝ) (1 : ℝ) 0 ∧
    deriv exercise28Integral 0 ≠
      sSup (Set.range fun p : Partition (-1 : ℝ) (1 : ℝ) =>
        lowerSum p (fun x => deriv (fun t => exercise28Phi x t) 0) id) := by
  refine ⟨exercise28_integral_derivative, exercise28_partial_integral, ?_⟩
  rw [exercise28_integral_derivative.deriv, exercise28_partial_integral.2.2.1]
  norm_num

/-- Equality with the source piecewise definition. The closed pieces overlap
only where the displayed values agree; `exercise28_source_nonnegative` proves
both formulas at every shared endpoint. -/
theorem exercise28_piecewise {x t : ℝ} (ht : 0 ≤ t) :
    exercise28Phi x t =
      if 0 ≤ x ∧ x ≤ Real.sqrt t then x
      else if Real.sqrt t ≤ x ∧ x ≤ 2*Real.sqrt t then -x+2*Real.sqrt t
      else 0 := by
  obtain ⟨h₁,h₂,h₃⟩ := exercise28_source_nonnegative (x := x) ht
  split_ifs with ha hb
  · exact h₁ ha
  · exact h₂ hb
  · exact h₃ ⟨ha,hb⟩

/-- The usual interval-integral notation gives the same failed interchange,
with explicit integrability of the integrand on both sides. -/
theorem exercise28_failed_interchange_interval :
    (∀ t, IntervalIntegrable (fun x => exercise28Phi x t) volume (-1 : ℝ) (1 : ℝ)) ∧
    IntervalIntegrable (fun x => deriv (fun t => exercise28Phi x t) 0)
      volume (-1 : ℝ) (1 : ℝ) ∧
    deriv exercise28Integral 0 ≠
      ∫ x in (-1 : ℝ)..(1 : ℝ), deriv (fun t => exercise28Phi x t) 0 := by
  refine ⟨fun t => exercise28_slice_integrable t (-1) 1, ?_, ?_⟩
  · simp_rw [(exercise28_parameter_partial _).deriv]
    exact intervalIntegrable_const
  · simp_rw [(exercise28_parameter_partial _).deriv]
    rw [exercise28_integral_derivative.deriv, intervalIntegral.integral_zero]
    norm_num

end Rudin.Chapter09
