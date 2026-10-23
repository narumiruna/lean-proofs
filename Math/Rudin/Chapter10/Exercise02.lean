module

public import Math.Rudin.Support.StieltjesComplex
public import Math.Rudin.Support.MultivariateRiemann
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Chapter 10, Exercise 2

The source index `i ≥ 1` is represented by `n = i - 1`. The series is pointwise
finite and locally finite off the origin. Its continuous compactly supported
sections have literal Darboux and complex tagged-sum integrals. The two orders
have values zero and one. Disjoint dyadic supports give unbounded diagonal
values without positivity or global two-dimensional integrability.

Source: Rudin, third edition, book page 288, primary PDF page 297.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise02

open Set Filter Topology MeasureTheory
open Rudin.Support StieltjesPrototype StieltjesRefinement StieltjesEquivalence StieltjesComplex

/-- Index `n` denotes the source function `φ_(n+1)`. -/
def radius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- No sign or reality condition is imposed on the functions. -/
structure Family where
  phi : ℕ → ℝ → ℂ
  continuous : ∀ n, Continuous (phi n)
  support : ∀ n, Function.support (phi n) ⊆ Ioo (radius (n+1)) (radius n)
  integral : ∀ n, (∫ x, phi n x) = 1

@[simp] theorem radius_zero : radius 0 = 1 := by simp [radius]
theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
theorem radius_antitone : Antitone radius :=
  pow_right_anti₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
theorem radius_le_one (n : ℕ) : radius n ≤ 1 := by
  simpa using radius_antitone (Nat.zero_le n)
theorem radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Exact agreement with the source dyadic endpoints. -/
theorem radius_source (n : ℕ) : radius n = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [radius, zpow_neg, zpow_natCast, one_div, inv_pow]

namespace Family

def term (Φ : Family) (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (Φ.phi n p.1 - Φ.phi (n+1) p.1) * Φ.phi n p.2

/-- The displayed series, not a substitute function. -/
def f (Φ : Family) (p : ℝ × ℝ) : ℂ := ∑' n, term Φ n p

theorem phi_mem (Φ : Family) {n : ℕ} {x : ℝ} (hx : Φ.phi n x ≠ 0) :
    x ∈ Ioo (radius (n+1)) (radius n) := Φ.support n hx

theorem phi_zero_of_nonpos (Φ : Family) (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    Φ.phi n x = 0 := by
  by_contra h
  have := (Φ.phi_mem h).1
  linarith [radius_pos (n+1)]

@[simp] theorem phi_zero (Φ : Family) (n : ℕ) : Φ.phi n 0 = 0 :=
  Φ.phi_zero_of_nonpos n le_rfl

theorem phi_zero_of_abs (Φ : Family) {n : ℕ} {x : ℝ} (hx : radius n ≤ |x|) :
    Φ.phi n x = 0 := by
  by_contra h
  have hm := Φ.phi_mem h
  have hp : 0 < x := (radius_pos _).trans hm.1
  rw [abs_of_pos hp] at hx
  exact (not_lt_of_ge hx) hm.2

/-- Every fixed coordinate kills a tail, including the coordinate zero. -/
theorem phi_tail (Φ : Family) (x : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, Φ.phi n x = 0 := by
  by_cases hx : x = 0
  · subst x; exact ⟨0, fun n _ => Φ.phi_zero n⟩
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (radius_tendsto.eventually
    (gt_mem_nhds (abs_pos.mpr hx))))
  exact ⟨N, fun n hn => Φ.phi_zero_of_abs (hN n hn).le⟩

/-- Away from zero, the same tail vanishes on a whole neighborhood. -/
theorem phi_tail_near (Φ : Family) {x : ℝ} (hx : x ≠ 0) :
    ∃ N : ℕ, ∀ᶠ z in 𝓝 x, ∀ n ≥ N, Φ.phi n z = 0 := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (radius_tendsto.eventually
    (gt_mem_nhds (abs_pos.mpr hx))))
  refine ⟨N, ?_⟩
  filter_upwards [(continuous_abs.continuousAt.eventually
    (lt_mem_nhds (hN N le_rfl)))] with z hz
  intro n hn
  exact Φ.phi_zero_of_abs ((radius_antitone hn).trans hz.le)

/-- The series is a finite sum at each point, so its value is not a default. -/
theorem well_defined (Φ : Family) (p : ℝ × ℝ) :
    ∃ N : ℕ, (∀ n ≥ N, term Φ n p = 0) ∧
      HasSum (fun n => term Φ n p) (∑ n ∈ Finset.range N, term Φ n p) := by
  obtain ⟨N, hN⟩ := Φ.phi_tail p.2
  have ht : ∀ n ≥ N, term Φ n p = 0 := by
    intro n hn; simp [term, hN n hn]
  exact ⟨N, ht, hasSum_sum_of_ne_finset_zero (fun n hn => ht n (by simpa using hn))⟩

/-- Ordered natural partial sums converge to the displayed function. -/
theorem ordered_convergence (Φ : Family) (p : ℝ × ℝ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, term Φ n p) atTop (𝓝 (f Φ p)) := by
  obtain ⟨_, _, h⟩ := Φ.well_defined p
  exact h.summable.hasSum.tendsto_sum_nat

theorem f_eq_sum (Φ : Family) (p : ℝ × ℝ) (N : ℕ)
    (hN : ∀ n ≥ N, term Φ n p = 0) :
    f Φ p = ∑ n ∈ Finset.range N, term Φ n p := by
  exact tsum_eq_sum (fun n hn => hN n (by simpa using hn))

theorem phi_support_unit (Φ : Family) (n : ℕ) :
    Function.support (Φ.phi n) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  have h := Φ.phi_mem hx
  exact ⟨(radius_pos _).le.trans h.1.le, h.2.le.trans (radius_le_one n)⟩

theorem phi_compact (Φ : Family) (n : ℕ) : HasCompactSupport (Φ.phi n) :=
  HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
    (fun x hx => by by_contra h; exact hx (Φ.phi_support_unit n h))

theorem phi_integrable (Φ : Family) (n : ℕ) : Integrable (Φ.phi n) :=
  (Φ.continuous n).integrable_of_hasCompactSupport (Φ.phi_compact n)

theorem f_zero_outside (Φ : Family) {p : ℝ × ℝ}
    (hp : p ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) : f Φ p = 0 := by
  change (∑' n, term Φ n p) = 0
  suffices h : ∀ n, term Φ n p = 0 by simp [h]
  intro n
  by_cases hx : p.1 ∈ Icc (0 : ℝ) 1
  · have hy : p.2 ∉ Icc (0 : ℝ) 1 := fun hy => hp ⟨hx, hy⟩
    have hz : Φ.phi n p.2 = 0 := by
      by_contra h; exact hy (Φ.phi_support_unit n h)
    simp [term, hz]
  · have hz (k) : Φ.phi k p.1 = 0 := by
      by_contra h; exact hx (Φ.phi_support_unit k h)
    simp [term, hz]

/-- The closure of the actual nonzero locus is compact. -/
theorem compact_support (Φ : Family) : IsCompact (tsupport (f Φ)) := by
  apply HasCompactSupport.intro
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  exact fun p hp => Φ.f_zero_outside hp

theorem term_continuous (Φ : Family) (n : ℕ) : Continuous (term Φ n) :=
  (((Φ.continuous n).comp continuous_fst).sub
    ((Φ.continuous (n+1)).comp continuous_fst)).mul
      ((Φ.continuous n).comp continuous_snd)

/-- Local finiteness holds off the origin; it is not claimed at the origin. -/
theorem locally_finite_off_origin (Φ : Family) {p : ℝ × ℝ} (hp : p ≠ 0) :
    ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n ≥ N, term Φ n q = 0 := by
  by_cases hx : p.1 = 0
  · have hy : p.2 ≠ 0 := by intro hy; exact hp (Prod.ext hx hy)
    obtain ⟨N, hN⟩ := Φ.phi_tail_near hy
    refine ⟨N, ?_⟩
    filter_upwards [continuous_snd.continuousAt hN] with q hq
    intro n hn
    simp [term, hq n hn]
  · obtain ⟨N, hN⟩ := Φ.phi_tail_near hx
    refine ⟨N, ?_⟩
    filter_upwards [continuous_fst.continuousAt hN] with q hq
    intro n hn
    simp [term, hq n hn, hq (n+1) (by omega)]

theorem continuous_off_origin (Φ : Family) {p : ℝ × ℝ} (hp : p ≠ 0) :
    ContinuousAt (f Φ) p := by
  obtain ⟨N, hN⟩ := Φ.locally_finite_off_origin hp
  have hc : Continuous (fun q => ∑ n ∈ Finset.range N, term Φ n q) :=
    continuous_finsetSum _ (fun n _ => Φ.term_continuous n)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hN] with q hq
  exact Φ.f_eq_sum q N hq

/-- Each section is globally a finite sum of continuous compactly supported functions. -/
theorem section_x_finite (Φ : Family) (y : ℝ) :
    ∃ N, (fun x => f Φ (x,y)) = fun x => ∑ n ∈ Finset.range N, term Φ n (x,y) := by
  obtain ⟨N, hN⟩ := Φ.phi_tail y
  refine ⟨N, funext fun x => Φ.f_eq_sum (x,y) N ?_⟩
  intro n hn
  simp [term, hN n hn]

theorem section_y_finite (Φ : Family) (x : ℝ) :
    ∃ N, Φ.phi N x = 0 ∧
      (fun y => f Φ (x,y)) = fun y => ∑ n ∈ Finset.range N, term Φ n (x,y) := by
  obtain ⟨N, hN⟩ := Φ.phi_tail x
  refine ⟨N, hN N le_rfl, funext fun y => Φ.f_eq_sum (x,y) N ?_⟩
  intro n hn
  simp [term, hN n hn, hN (n+1) (by omega)]

theorem section_x_continuous (Φ : Family) (y : ℝ) : Continuous (fun x => f Φ (x,y)) := by
  obtain ⟨N, hN⟩ := Φ.section_x_finite y
  rw [hN]
  exact continuous_finsetSum _ (fun n _ => (Φ.term_continuous n).comp
    (continuous_id.prodMk continuous_const))

theorem section_y_continuous (Φ : Family) (x : ℝ) : Continuous (fun y => f Φ (x,y)) := by
  obtain ⟨N, _, hN⟩ := Φ.section_y_finite x
  rw [hN]
  exact continuous_finsetSum _ (fun n _ => (Φ.term_continuous n).comp
    (continuous_const.prodMk continuous_id))

theorem section_x_support (Φ : Family) (y : ℝ) :
    Function.support (fun x => f Φ (x,y)) ⊆ Ioc (0 : ℝ) 1 := by
  intro x hx
  by_contra h
  have hz (n) : Φ.phi n x = 0 := by
    by_contra hn
    have hm := Φ.phi_mem hn
    exact h ⟨(radius_pos _).trans hm.1, hm.2.le.trans (radius_le_one n)⟩
  have : f Φ (x,y) = 0 := by simp [f, term, hz]
  exact hx this

theorem section_y_support (Φ : Family) (x : ℝ) :
    Function.support (fun y => f Φ (x,y)) ⊆ Ioc (0 : ℝ) 1 := by
  intro y hy
  by_contra h
  have hz (n) : Φ.phi n y = 0 := by
    by_contra hn
    have hm := Φ.phi_mem hn
    exact h ⟨(radius_pos _).trans hm.1, hm.2.le.trans (radius_le_one n)⟩
  have : f Φ (x,y) = 0 := by simp [f, term, hz]
  exact hy this

theorem section_x_compact (Φ : Family) (y : ℝ) :
    HasCompactSupport (fun x => f Φ (x,y)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro x hx
  by_contra h
  exact hx (Ioc_subset_Icc_self (Φ.section_x_support y h))

theorem section_y_compact (Φ : Family) (x : ℝ) :
    HasCompactSupport (fun y => f Φ (x,y)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro y hy
  by_contra h
  exact hy (Ioc_subset_Icc_self (Φ.section_y_support x h))

theorem section_x_integrable (Φ : Family) (y : ℝ) : Integrable (fun x => f Φ (x,y)) :=
  (Φ.section_x_continuous y).integrable_of_hasCompactSupport (Φ.section_x_compact y)

theorem section_y_integrable (Φ : Family) (x : ℝ) : Integrable (fun y => f Φ (x,y)) :=
  (Φ.section_y_continuous x).integrable_of_hasCompactSupport (Φ.section_y_compact x)

theorem inner_x (Φ : Family) (y : ℝ) : (∫ x, f Φ (x,y)) = 0 := by
  obtain ⟨N, hN⟩ := Φ.section_x_finite y
  rw [hN, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro n _
    simp only [term, integral_mul_const,
      integral_sub (Φ.phi_integrable n) (Φ.phi_integrable (n+1)), Φ.integral,
      sub_self, zero_mul]
  · intro n _
    exact ((Φ.phi_integrable n).sub (Φ.phi_integrable (n+1))).mul_const (Φ.phi n y)

theorem inner_y (Φ : Family) (x : ℝ) : (∫ y, f Φ (x,y)) = Φ.phi 0 x := by
  obtain ⟨N, hz, hN⟩ := Φ.section_y_finite x
  rw [hN, integral_finsetSum]
  · simp only [term, integral_const_mul, Φ.integral, mul_one]
    rw [Finset.sum_range_sub', hz, sub_zero]
  · intro n _
    exact (Φ.phi_integrable n).const_mul (Φ.phi n x - Φ.phi (n+1) x)

end Family

/-- Source existence records both actual real Darboux integrals and the actual
complex tagged-sum integral. This predicate is not defined by Bochner values. -/
def HasSource (g : ℝ → ℂ) (z : ℂ) : Prop :=
  HasDarbouxRSIntegral (fun x => (g x).re) id 0 1 z.re ∧
  HasDarbouxRSIntegral (fun x => (g x).im) id 0 1 z.im ∧
  HasComplexRSIntegral g id 0 1 z

/-- Continuous sections have the literal one-dimensional source integral.
The component bridges use the existing Darboux API. -/
theorem continuous_source {g : ℝ → ℂ} (hc : Continuous g)
    (hs : Function.support g ⊆ Ioc (0 : ℝ) 1) : HasSource g (∫ x, g x) := by
  have hr := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by norm_num : (0 : ℝ) ≤ 1) (Complex.continuous_re.comp hc).continuousOn
  have hi := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by norm_num : (0 : ℝ) ≤ 1) (Complex.continuous_im.comp hc).continuousOn
  have he := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hs
  have hri := intervalIntegral.intervalIntegral_re (hc.intervalIntegrable (μ := volume) 0 1)
  have hii := intervalIntegral.intervalIntegral_im (hc.intervalIntegrable (μ := volume) 0 1)
  simp only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] at hr hi
  change HasDarbouxRSIntegral _ id 0 1 (∫ x in 0..1, (g x).re) at hr
  change HasDarbouxRSIntegral _ id 0 1 (∫ x in 0..1, (g x).im) at hi
  change (∫ x in 0..1, (g x).re) = (∫ x in 0..1, g x).re at hri
  change (∫ x in 0..1, (g x).im) = (∫ x in 0..1, g x).im at hii
  rw [hri, he] at hr
  rw [hii, he] at hi
  exact ⟨hr, hi, hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hr,
      hasRSIntegral_of_hasDarbouxRSIntegral (by norm_num) hi⟩⟩

namespace Family

theorem phi_source (Φ : Family) (n : ℕ) : HasSource (Φ.phi n) 1 := by
  rw [← Φ.integral n]
  apply continuous_source (Φ.continuous n)
  intro x hx
  have hm := Φ.phi_mem hx
  exact ⟨(radius_pos _).trans hm.1, hm.2.le.trans (radius_le_one n)⟩

/-- All inner integrals exist, and the outer integral is the source integral of
zero. No integrability of the two-dimensional function is assumed. -/
theorem x_then_y (Φ : Family) :
    (∀ y, Integrable (fun x => f Φ (x,y)) ∧ HasSource (fun x => f Φ (x,y)) 0) ∧
    Integrable (fun y => ∫ x, f Φ (x,y)) ∧
    HasSource (fun y => ∫ x, f Φ (x,y)) 0 ∧
    (∫ y, ∫ x, f Φ (x,y)) = 0 := by
  have hz : (fun y => ∫ x, f Φ (x,y)) = fun _ => (0 : ℂ) := funext Φ.inner_x
  constructor
  · intro y
    refine ⟨Φ.section_x_integrable y, ?_⟩
    rw [← Φ.inner_x y]
    exact continuous_source (Φ.section_x_continuous y) (Φ.section_x_support y)
  · rw [hz]
    refine ⟨integrable_zero _ _ _, ?_, integral_zero _ _⟩
    simpa using continuous_source (g := fun _ => (0 : ℂ)) continuous_const (by simp)

/-- Every inner integral exists and equals `φ₁`; its outer source integral is one. -/
theorem y_then_x (Φ : Family) :
    (∀ x, Integrable (fun y => f Φ (x,y)) ∧
      HasSource (fun y => f Φ (x,y)) (Φ.phi 0 x)) ∧
    Integrable (fun x => ∫ y, f Φ (x,y)) ∧
    HasSource (fun x => ∫ y, f Φ (x,y)) 1 ∧
    (∫ x, ∫ y, f Φ (x,y)) = 1 := by
  have hz : (fun x => ∫ y, f Φ (x,y)) = Φ.phi 0 := funext Φ.inner_y
  constructor
  · intro x
    refine ⟨Φ.section_y_integrable x, ?_⟩
    rw [← Φ.inner_y x]
    exact continuous_source (Φ.section_y_continuous x) (Φ.section_y_support x)
  · rw [hz]
    exact ⟨Φ.phi_integrable 0, Φ.phi_source 0, Φ.integral 0⟩

/-- Distinct dyadic open intervals do not overlap. Endpoints are excluded. -/
theorem phi_index_unique (Φ : Family) {n m : ℕ} {x : ℝ}
    (hn : Φ.phi n x ≠ 0) (hm : Φ.phi m x ≠ 0) : n = m := by
  have hnx := Φ.phi_mem hn
  have hmx := Φ.phi_mem hm
  rcases lt_trichotomy n m with h | h | h
  · have hr := radius_antitone (show n+1 ≤ m by omega)
    linarith [hnx.1, hmx.2]
  · exact h
  · have hr := radius_antitone (show m+1 ≤ n by omega)
    linarith [hmx.1, hnx.2]

theorem phi_other_zero (Φ : Family) {n m : ℕ} {x : ℝ}
    (hn : Φ.phi n x ≠ 0) (hm : m ≠ n) : Φ.phi m x = 0 := by
  by_contra h
  exact hm (Φ.phi_index_unique h hn)

/-- On the diagonal there is no cancellation, even for complex functions:
the value is a complex square and its norm is the square of the norm. -/
theorem diagonal (Φ : Family) {n : ℕ} {x : ℝ} (hx : Φ.phi n x ≠ 0) :
    f Φ (x,x) = (Φ.phi n x) ^ 2 := by
  have hn : Φ.phi (n+1) x = 0 := Φ.phi_other_zero hx (by omega)
  calc
    f Φ (x,x) = term Φ n (x,x) := by
      apply tsum_eq_single n
      intro m hm
      simp [term, Φ.phi_other_zero hx hm]
    _ = _ := by simp [term, hn, pow_two]

/-- Integral one on a shrinking interval forces arbitrarily large values.
This estimate uses only a norm bound, not positivity of the integrand. -/
theorem exists_large_phi (Φ : Family) (n : ℕ) {M : ℝ} (hM : 0 < M)
    (hsmall : M * radius n < 1) :
    ∃ x ∈ Ioo (radius (n+1)) (radius n), M < ‖Φ.phi n x‖ := by
  by_contra h
  have hb : ∀ x ∈ Ioc (0 : ℝ) (radius n), ‖Φ.phi n x‖ ≤ M := by
    intro x _
    by_cases hx : Φ.phi n x = 0
    · simpa [hx] using hM.le
    · exact le_of_not_gt (fun hh => h ⟨x, Φ.phi_mem hx, hh⟩)
  have hi : (∫ x in 0..radius n, Φ.phi n x) = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset, Φ.integral]
    intro x hx
    have hm := Φ.phi_mem hx
    exact ⟨(radius_pos _).trans hm.1, hm.2.le⟩
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := radius n) (f := Φ.phi n) (C := M) (by
      simpa only [uIoc_of_le (radius_pos n).le] using hb)
  rw [hi, norm_one, sub_zero, abs_of_pos (radius_pos n)] at hn
  linarith

/-- Every origin neighborhood contains values with norm exceeding any prescribed
real bound. The proof does not invoke a two-dimensional measure integral. -/
theorem unbounded_every_neighborhood (Φ : Family) {U : Set (ℝ × ℝ)}
    (hU : U ∈ 𝓝 (0 : ℝ × ℝ)) (B : ℝ) : ∃ p ∈ U, B < ‖f Φ p‖ := by
  have hd : Continuous (fun x : ℝ => (x,x)) := continuous_id.prodMk continuous_id
  have hu : (fun x : ℝ => (x,x)) ⁻¹' U ∈ 𝓝 0 := hd.continuousAt hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu
  let M : ℝ := max B 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; linarith [le_max_right B 0]
  have hBM : B < M := by dsimp [M]; linarith [le_max_left B 0]
  have hp : 0 < min δ (1 / M) := lt_min hδ (one_div_pos.mpr hM)
  obtain ⟨n, hn⟩ := (radius_tendsto.eventually (gt_mem_nhds hp)).exists
  have hrδ := lt_of_lt_of_le hn (min_le_left _ _)
  have hrM := lt_of_lt_of_le hn (min_le_right _ _)
  have hsmall : M * radius n < 1 := by
    have := (lt_div_iff₀ hM).mp hrM
    simpa [mul_comm] using this
  obtain ⟨x, hx, hlarge⟩ := Φ.exists_large_phi n hM hsmall
  have hx0 : 0 < x := (radius_pos _).trans hx.1
  have hnonzero : Φ.phi n x ≠ 0 := by
    intro hz; simp only [hz, norm_zero] at hlarge; linarith
  refine ⟨(x,x), hball ?_, ?_⟩
  · simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hx0] using hx.2.trans hrδ
  · rw [Φ.diagonal hnonzero, norm_pow]
    nlinarith [norm_nonneg (Φ.phi n x)]

@[simp] theorem f_origin (Φ : Family) : f Φ 0 = 0 := by simp [f, term]

theorem discontinuous_origin (Φ : Family) : ¬ ContinuousAt (f Φ) 0 := by
  intro hc
  have hn : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), ‖f Φ p‖ < 1 := by
    have h := hc.norm.eventually (gt_mem_nhds (by simp : ‖f Φ 0‖ < 1))
    exact h
  obtain ⟨p, hp, hb⟩ := Φ.unbounded_every_neighborhood hn 1
  exact (not_lt_of_ge hp.le) hb

/-- Fubini cannot be applied globally: this function is not integrable. -/
theorem not_integrable (Φ : Family) : ¬ Integrable (f Φ) := by
  intro h
  have hp : Integrable (fun p : ℝ × ℝ => f Φ (p.1,p.2)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using h
  have he := integral_integral_swap (f := fun x y => f Φ (x,y)) hp
  simp only [Φ.inner_y, Φ.inner_x, Φ.integral, integral_zero] at he
  exact one_ne_zero he

end Family

/-- A literal source normalization supplies the normalization in `Family`.
Continuity and support prove the comparison before uniqueness is used. -/
def familyOfSource (φ : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (φ n))
    (hs : ∀ n, Function.support (φ n) ⊆ Ioo (radius (n+1)) (radius n))
    (hi : ∀ n, HasComplexRSIntegral (φ n) id 0 1 1) : Family where
  phi := φ
  continuous := hc
  support := hs
  integral n := by
    have hb := continuous_source (hc n) (show Function.support (φ n) ⊆ Ioc (0 : ℝ) 1 from
      fun x hx => ⟨(radius_pos _).trans (hs n hx).1,
        (hs n hx).2.le.trans (radius_le_one n)⟩)
    exact hasComplexRSIntegral_unique hb.2.2 (hi n)

/-- Arbitrary real functions are included, without a positivity assumption. -/
structure RealFamily where
  phi : ℕ → ℝ → ℝ
  continuous : ∀ n, Continuous (phi n)
  support : ∀ n, Function.support (phi n) ⊆ Ioo (radius (n+1)) (radius n)
  integral : ∀ n, (∫ x, phi n x) = 1

namespace RealFamily

def complex (Φ : RealFamily) : Family where
  phi n x := (Φ.phi n x : ℂ)
  continuous n := Complex.continuous_ofReal.comp (Φ.continuous n)
  support n := by simpa using Φ.support n
  integral n := by simp [integral_complex_ofReal, Φ.integral]

def f (Φ : RealFamily) (p : ℝ × ℝ) : ℝ :=
  ∑' n, (Φ.phi n p.1 - Φ.phi (n+1) p.1) * Φ.phi n p.2

/-- The reduction preserves the actual series, not just its integral. -/
theorem complex_f (Φ : RealFamily) (p : ℝ × ℝ) :
    Φ.complex.f p = (Φ.f p : ℂ) := by
  simp [Family.f, Family.term, f, complex, Complex.ofReal_tsum]

theorem real_part (Φ : RealFamily) : (fun p => (Φ.complex.f p).re) = Φ.f := by
  funext p
  simp [Φ.complex_f]

theorem inner_x (Φ : RealFamily) (y : ℝ) : (∫ x, Φ.f (x,y)) = 0 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [← Φ.complex_f, Complex.ofReal_zero] using Φ.complex.inner_x y

theorem inner_y (Φ : RealFamily) (x : ℝ) : (∫ y, Φ.f (x,y)) = Φ.phi 0 x := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h := Φ.complex.inner_y x
  change (∫ y, Φ.complex.f (x,y)) = (Φ.phi 0 x : ℂ) at h
  simpa only [Φ.complex_f] using h

theorem section_x_source (Φ : RealFamily) (y : ℝ) :
    HasDarbouxRSIntegral (fun x => Φ.f (x,y)) id 0 1 0 := by
  simpa only [Φ.complex_f, Complex.ofReal_re, Complex.zero_re] using
    (Φ.complex.x_then_y.1 y).2.1

theorem section_y_source (Φ : RealFamily) (x : ℝ) :
    HasDarbouxRSIntegral (fun y => Φ.f (x,y)) id 0 1 (Φ.phi 0 x) := by
  have h := (Φ.complex.y_then_x.1 x).2.1
  change HasDarbouxRSIntegral (fun y => (Φ.complex.f (x,y)).re) id 0 1 (Φ.phi 0 x) at h
  simpa only [Φ.complex_f, Complex.ofReal_re] using h

/-- All six conclusions transfer to the literal real series. -/
theorem real_case (Φ : RealFamily) :
    (∀ p : ℝ × ℝ, Summable (fun n => (Φ.phi n p.1 - Φ.phi (n+1) p.1) * Φ.phi n p.2)) ∧
    IsCompact (tsupport Φ.f) ∧
    (∀ p ≠ 0, ContinuousAt Φ.f p) ∧
    (∀ y, Integrable (fun x => Φ.f (x,y)) ∧
      HasDarbouxRSIntegral (fun x => Φ.f (x,y)) id 0 1 0) ∧
    (∀ x, Integrable (fun y => Φ.f (x,y)) ∧
      HasDarbouxRSIntegral (fun y => Φ.f (x,y)) id 0 1 (Φ.phi 0 x)) ∧
    (Integrable (fun y => ∫ x, Φ.f (x,y)) ∧
      HasDarbouxRSIntegral (fun y => ∫ x, Φ.f (x,y)) id 0 1 0 ∧
      (∫ y, ∫ x, Φ.f (x,y)) = 0) ∧
    (Integrable (fun x => ∫ y, Φ.f (x,y)) ∧
      HasDarbouxRSIntegral (fun x => ∫ y, Φ.f (x,y)) id 0 1 1 ∧
      (∫ x, ∫ y, Φ.f (x,y)) = 1) ∧
    (∀ U ∈ 𝓝 (0 : ℝ × ℝ), ∀ B : ℝ, ∃ p ∈ U, B < |Φ.f p|) ∧
    ¬ ContinuousAt Φ.f 0 := by
  have hs (p) := Φ.complex.well_defined p
  have hnorm (p) : ‖Φ.complex.f p‖ = |Φ.f p| := by simp [Φ.complex_f]
  have hxint (y) : Integrable (fun x => Φ.f (x,y)) := by
    simpa only [Φ.complex_f, RCLike.re_to_complex, Complex.ofReal_re] using
      (Φ.complex.section_x_integrable y).re
  have hyint (x) : Integrable (fun y => Φ.f (x,y)) := by
    simpa only [Φ.complex_f, RCLike.re_to_complex, Complex.ofReal_re] using
      (Φ.complex.section_y_integrable x).re
  refine ⟨?_, ?_, ?_, fun y => ⟨hxint y, Φ.section_x_source y⟩,
    fun x => ⟨hyint x, Φ.section_y_source x⟩, ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨N, hN, _⟩ := hs p
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hz := hN n (by simpa using hn)
    change ((Φ.phi n p.1 : ℂ) - (Φ.phi (n+1) p.1 : ℂ)) *
      (Φ.phi n p.2 : ℂ) = 0 at hz
    exact_mod_cast hz
  · have he : Function.support Φ.complex.f = Function.support Φ.f := by
      ext p; simp [Function.mem_support, Φ.complex_f]
    simpa only [tsupport, he] using Φ.complex.compact_support
  · intro p hp
    rw [← Φ.real_part]
    exact Complex.continuous_re.continuousAt.comp (Φ.complex.continuous_off_origin hp)
  · simp only [Φ.inner_x]
    refine ⟨integrable_zero _ _ _, ?_, integral_zero _ _⟩
    have h := continuous_source (g := fun _ => (0 : ℂ)) continuous_const (by simp)
    simpa using h.1
  · simp only [Φ.inner_y]
    have hi := (Φ.complex.phi_integrable 0).re
    have hd := (Φ.complex.phi_source 0).1
    exact ⟨by simpa [complex] using hi, by simpa [complex] using hd, Φ.integral 0⟩
  · intro U hU B
    simpa only [hnorm] using Φ.complex.unbounded_every_neighborhood hU B
  · intro hc
    apply Φ.complex.discontinuous_origin
    have he : Φ.complex.f = fun p => (Φ.f p : ℂ) := funext Φ.complex_f
    rw [he]
    exact Complex.continuous_ofReal.continuousAt.comp hc

end RealFamily

/-- A two-coordinate witness in the frozen recursive source API. Only the
one-dimensional stages are used; no global integrability is required. -/
theorem pair_source {g : (ℝ × ℝ) → ℝ} {h : ℝ → ℝ} {v : ℝ}
    (hi : ∀ y, HasDarbouxRSIntegral (fun x => g (x,y)) id 0 1 (h y))
    (he : ∀ y, (∫ x in 0..1, g (x,y)) = h y)
    (ho : HasDarbouxRSIntegral h id 0 1 v) (hv : (∫ y in 0..1, h y) = v) :
    MultivariateRiemann.HasSourceIntegral 2 0 1 (fun p => g (p 0,p 1)) v := by
  constructor
  · intro x _
    change HasDarbouxRSIntegral (fun t => g (t,x 0)) id 0 1
      (∫ t in 0..1, g (t,x 0))
    rw [he]
    exact hi (x 0)
  · constructor
    · intro x _
      change HasDarbouxRSIntegral (fun t => ∫ s in 0..1, g (s,t)) id 0 1
        (∫ t in 0..1, ∫ s in 0..1, g (s,t))
      simp_rw [he]
      rw [hv]
      exact ho
    · change (∫ t in 0..1, ∫ s in 0..1, g (s,t)) = v
      simp_rw [he]
      exact hv

/-- Both real integration orders use the actual multivariate source predicate. -/
theorem RealFamily.source_orders (Φ : RealFamily) :
    MultivariateRiemann.HasSourceIntegral 2 0 1 (fun p => Φ.f (p 0,p 1)) 0 ∧
    MultivariateRiemann.HasSourceIntegral 2 0 1 (fun p => Φ.f (p 1,p 0)) 1 := by
  have hx (y) : (∫ x in 0..1, Φ.f (x,y)) = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset, Φ.inner_x]
    intro x hx
    apply Φ.complex.section_x_support y
    simpa [Function.mem_support, Φ.complex_f] using hx
  have hy (x) : (∫ y in 0..1, Φ.f (x,y)) = Φ.phi 0 x := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset, Φ.inner_y]
    intro y hy
    apply Φ.complex.section_y_support x
    simpa [Function.mem_support, Φ.complex_f] using hy
  have hp : HasDarbouxRSIntegral (Φ.phi 0) id 0 1 1 := by
    simpa [RealFamily.complex] using (Φ.complex.phi_source 0).1
  have hv : (∫ x in 0..1, Φ.phi 0 x) = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset, Φ.integral]
    intro x hx
    have hm := Φ.support 0 hx
    exact ⟨(radius_pos _).trans hm.1, by simpa using hm.2.le⟩
  refine ⟨pair_source Φ.section_x_source hx ?_ (by simp),
    pair_source (g := fun p => Φ.f (p.2,p.1)) Φ.section_y_source hy hp hv⟩
  have hz := continuous_source (g := fun _ => (0 : ℂ)) continuous_const (by simp)
  simpa using hz.1

namespace Family

/-- The same function in the actual Euclidean coordinate plane. -/
def euclideanF (Φ : Family) (u : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  Φ.f (MultivariateRiemann.pairCoordinates u)

theorem euclidean_conclusions (Φ : Family) :
    IsCompact (tsupport Φ.euclideanF) ∧
    (∀ u ≠ 0, ContinuousAt Φ.euclideanF u) ∧
    (∀ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)), ∀ B : ℝ,
      ∃ u ∈ U, B < ‖Φ.euclideanF u‖) ∧
    ¬ ContinuousAt Φ.euclideanF 0 := by
  let e := MultivariateRiemann.pairCoordinates
  have hc : HasCompactSupport Φ.euclideanF := by
    change HasCompactSupport (Φ.f ∘ e)
    exact (show HasCompactSupport Φ.f from Φ.compact_support).comp_homeomorph e.toHomeomorph
  have hu : ∀ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)), ∀ B : ℝ,
      ∃ u ∈ U, B < ‖Φ.euclideanF u‖ := by
    intro U hU B
    have hn : e.symm ⁻¹' U ∈ 𝓝 (0 : ℝ × ℝ) := by
      have ht := e.symm.continuous.continuousAt (x := (0 : ℝ × ℝ))
      apply ht
      simpa using hU
    obtain ⟨p, hp, hb⟩ := Φ.unbounded_every_neighborhood hn B
    refine ⟨e.symm p, hp, ?_⟩
    simpa [euclideanF, e] using hb
  refine ⟨hc, ?_, hu, ?_⟩
  · intro u hu
    exact (Φ.continuous_off_origin (by simpa using hu)).comp e.continuous.continuousAt
  · intro ht
    apply Φ.discontinuous_origin
    have ht' : ContinuousAt Φ.euclideanF (e.symm (0 : ℝ × ℝ)) := by simpa using ht
    have hcomp := ht'.comp (e.symm.continuous.continuousAt (x := (0 : ℝ × ℝ)))
    simpa [euclideanF, e, Function.comp_def] using hcomp

end Family
end Rudin.Chapter10.Exercise02
