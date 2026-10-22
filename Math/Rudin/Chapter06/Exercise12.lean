module

public import Math.Rudin.Chapter06.Exercise11
public import Math.Rudin.Support.StieltjesMeasureBridge

/-!
# Chapter 6, Exercise 12

Source: Rudin, page 140 (PDF page 149), including the polygonal interpolation
hint. The construction uses raw closed-cell Darboux gaps. It applies to every
monotone integrator, including jumps and zero total increment. No comparison
with a measure integral of a discontinuous function is used.
-/

@[expose] public section

noncomputable section

namespace Rudin.Chapter06

open Set
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
open Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesIntegralLaws
open Rudin.Support.StieltjesComposition Rudin.Support.StieltjesComplex

/-- A continuous clipped affine ramp. Division by zero is harmless: the
corresponding repeated-node difference in the polygon is zero. -/
def interpolationRamp (l u t : ℝ) : ℝ := min 1 (max 0 ((t - l) / (u - l)))

theorem interpolationRamp_continuous (l u : ℝ) : Continuous (interpolationRamp l u) := by
  unfold interpolationRamp
  fun_prop

theorem interpolationRamp_bounds (l u t : ℝ) :
    0 ≤ interpolationRamp l u t ∧ interpolationRamp l u t ≤ 1 := by
  unfold interpolationRamp
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem interpolationRamp_zero {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) :
    interpolationRamp l u t = 0 := by
  have h : (t - l) / (u - l) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu)
  simp only [interpolationRamp, max_eq_left h, min_eq_right zero_le_one]

theorem interpolationRamp_one {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) :
    interpolationRamp l u t = 1 := by
  have h : 1 ≤ (t - l) / (u - l) :=
    (le_div_iff₀ (sub_pos.mpr hlu)).mpr (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))

/-- The sum of ramps is the continuous piecewise-affine interpolant through
all partition values. It is defined on the whole real line. -/
def partitionPolygon {a b : ℝ} (p : Partition a b) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f a + ∑ j ∈ Finset.range p.n,
    interpolationRamp (p.x j) (p.x (j + 1)) t * (f (p.x (j + 1)) - f (p.x j))

theorem partitionPolygon_continuous {a b : ℝ} (p : Partition a b) (f : ℝ → ℝ) :
    Continuous (partitionPolygon p f) := by
  exact continuous_const.add (continuous_finsetSum _ (fun j _ =>
    (interpolationRamp_continuous _ _).mul continuous_const))

/-- On each closed cell, the polygon is the convex combination in Rudin's
hint. Repeated cells retain the common endpoint value. -/
theorem partitionPolygon_cell {a b t : ℝ} (p : Partition a b) (f : ℝ → ℝ)
    {i : ℕ} (hi : i < p.n) (ht : t ∈ Icc (p.x i) (p.x (i + 1))) :
    partitionPolygon p f t = f (p.x i) +
      interpolationRamp (p.x i) (p.x (i + 1)) t * (f (p.x (i + 1)) - f (p.x i)) := by
  let term := fun j => interpolationRamp (p.x j) (p.x (j + 1)) t *
    (f (p.x (j + 1)) - f (p.x j))
  have hbefore (j : ℕ) (hj : j < i) : term j = f (p.x (j + 1)) - f (p.x j) := by
    have hjn : j < p.n := hj.trans hi
    have hle : p.x j ≤ p.x (j + 1) := (left_isTag p j hjn).2
    by_cases heq : p.x (j + 1) = p.x j
    · simp [term, heq]
    · have hlt : p.x j < p.x (j + 1) := lt_of_le_of_ne hle (Ne.symm heq)
      have hleft : p.x (j + 1) ≤ t :=
        (p.increasing (show j + 1 ≤ p.n by omega) hi.le (by omega)).trans ht.1
      simp only [term, interpolationRamp_one hlt hleft, one_mul]
  have hafter (j : ℕ) (hij : i < j) (hjn : j < p.n) : term j = 0 := by
    have hle : p.x j ≤ p.x (j + 1) := (left_isTag p j hjn).2
    have hright : t ≤ p.x j := ht.2.trans (p.increasing (show i + 1 ≤ p.n by omega) hjn.le (by omega))
    simp only [term, interpolationRamp_zero hle hright, zero_mul]
  have hsum : (∑ j ∈ Finset.range p.n, term j) =
      (∑ j ∈ Finset.range i, term j) + term i := by
    rw [← Finset.sum_range_succ]
    symm
    apply Finset.sum_subset (Finset.range_mono (show i + 1 ≤ p.n by omega))
    intro j hj hji
    have hji' : i + 1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hji
    exact hafter j (by omega) (Finset.mem_range.mp hj)
  have hprefix : (∑ j ∈ Finset.range i, term j) = f (p.x i) - f a := by
    rw [Finset.sum_congr rfl (fun j hj => hbefore j (Finset.mem_range.mp hj)),
      Finset.sum_range_sub (fun j => f (p.x j)), p.first]
  dsimp only [partitionPolygon]
  change f a + (∑ j ∈ Finset.range p.n, term j) = _
  rw [hsum, hprefix]
  dsimp [term]
  ring

/-- On a positive-length cell this is exactly the formula in the source hint. -/
theorem partitionPolygon_cell_affine {a b t : ℝ} (p : Partition a b) (f : ℝ → ℝ)
    {i : ℕ} (hi : i < p.n) (hlen : p.x i < p.x (i + 1))
    (ht : t ∈ Icc (p.x i) (p.x (i + 1))) :
    partitionPolygon p f t =
      (p.x (i + 1) - t) / (p.x (i + 1) - p.x i) * f (p.x i) +
      (t - p.x i) / (p.x (i + 1) - p.x i) * f (p.x (i + 1)) := by
  have hd := sub_pos.mpr hlen
  have hr₀ : 0 ≤ (t - p.x i) / (p.x (i + 1) - p.x i) :=
    div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hr₁ : (t - p.x i) / (p.x (i + 1) - p.x i) ≤ 1 :=
    (div_le_iff₀ hd).mpr (by linarith [ht.2])
  rw [partitionPolygon_cell p f hi ht, interpolationRamp, max_eq_right hr₀, min_eq_right hr₁]
  field_simp
  ring

/-- Closed-cell extrema bound the actual polygon error. -/
theorem partitionPolygon_error_bound {a b M : ℝ} {f : ℝ → ℝ}
    (p : Partition a b) (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    {i : ℕ} (hi : i < p.n) {t : ℝ} (ht : t ∈ Icc (p.x i) (p.x (i + 1))) :
    (f t - partitionPolygon p f t) ^ 2 ≤
      2 * M * (sSup (f '' Icc (p.x i) (p.x (i + 1))) -
        sInf (f '' Icc (p.x i) (p.x (i + 1)))) := by
  let s := Icc (p.x i) (p.x (i + 1))
  let L := sInf (f '' s)
  let U := sSup (f '' s)
  have hs : s.Nonempty := ⟨p.x i, left_isTag p i hi⟩
  have hb : BddBelow (f '' s) := ⟨-M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi hx))).1⟩
  have ha : BddAbove (f '' s) := ⟨M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi hx))).2⟩
  have hvalues (x) (hx : x ∈ s) : L ≤ f x ∧ f x ≤ U :=
    ⟨csInf_le hb (mem_image_of_mem f hx), le_csSup ha (mem_image_of_mem f hx)⟩
  have hL : -M ≤ L := le_csInf (hs.image f) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi hx))).1)
  have hU : U ≤ M := csSup_le (hs.image f) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset p hi hx))).2)
  let r := interpolationRamp (p.x i) (p.x (i + 1)) t
  have hr := interpolationRamp_bounds (p.x i) (p.x (i + 1)) t
  have hleft := hvalues (p.x i) (left_isTag p i hi)
  have hright := hvalues (p.x (i + 1)) ⟨(left_isTag p i hi).2, le_rfl⟩
  have hpoly : L ≤ partitionPolygon p f t ∧ partitionPolygon p f t ≤ U := by
    rw [partitionPolygon_cell p f hi ht]
    change L ≤ f (p.x i) + r * (f (p.x (i + 1)) - f (p.x i)) ∧
      f (p.x i) + r * (f (p.x (i + 1)) - f (p.x i)) ≤ U
    change 0 ≤ r ∧ r ≤ 1 at hr
    constructor <;> nlinarith
  have hft := hvalues t ht
  have herr : |f t - partitionPolygon p f t| ≤ U - L :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have herr' : |f t - partitionPolygon p f t| ≤ 2 * M := by linarith
  have hn := abs_nonneg (f t - partitionPolygon p f t)
  change _ ≤ 2 * M * (U - L)
  nlinarith [mul_le_mul herr' herr hn (by linarith : 0 ≤ 2 * M), sq_abs (f t - partitionPolygon p f t)]

/-- A polygon's weighted squared error is controlled by the original raw
Darboux gap, with the actual endpoint increments of the integrator. -/
theorem partitionPolygon_upper_error_le {a b M : ℝ} {f α : ℝ → ℝ}
    (p : Partition a b) (hα : MonotoneOn α (Icc a b))
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) :
    upperSum p (fun x => (f x - partitionPolygon p f x) ^ 2) α ≤
      2 * M * (upperSum p f α - lowerSum p f α) := by
  unfold upperSum lowerSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hc : sSup ((fun x => (f x - partitionPolygon p f x) ^ 2) ''
      Icc (p.x i) (p.x (i + 1))) ≤
      2 * M * (sSup (f '' Icc (p.x i) (p.x (i + 1))) -
        sInf (f '' Icc (p.x i) (p.x (i + 1)))) := by
    apply csSup_le ⟨_, mem_image_of_mem _ (left_isTag p i hi')⟩
    rintro _ ⟨x, hx, rfl⟩
    exact partitionPolygon_error_bound p hM hi' hx
  have h := mul_le_mul_of_nonneg_right hc (increment_nonneg p hα hi')
  nlinarith only [h]

/-- A raw integral lies below every one of its actual upper sums. -/
theorem rs_value_le_upperSum {a b E : ℝ} {f α : ℝ → ℝ}
    (p : Partition a b) (hf : HasRSIntegral f α a b E) : E ≤ upperSum p f α := by
  have hd := hasDarbouxRSIntegral_of_hasRSIntegral (endpoints_le p) hf
  rw [← hd.2.2.2]
  obtain ⟨M, hM⟩ := hf.2.1
  exact csInf_le (upperSum_range_bounded hf.1 hM).1 ⟨p, rfl⟩

/-- The real construction, with an arbitrarily small squared error integral.
Continuity and existence of the error integral are proved, not assumed. -/
theorem exists_continuous_real_sq_error {a b v δ : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f α a b v) (hδ : 0 < δ) :
    ∃ (g : ℝ → ℝ) (E : ℝ), Continuous g ∧
      HasRSIntegral (fun x => (f x - g x) ^ 2) α a b E ∧ 0 ≤ E ∧ E < δ := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hM₀ : 0 ≤ M := (abs_nonneg (f a)).trans (hM a ⟨le_rfl, hab⟩)
  obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums hf
    (show 0 < (δ / (2 * M + 1)) / 2 by positivity)
  let g := partitionPolygon p f
  have hgc : Continuous g := partitionPolygon_continuous p f
  obtain ⟨G, hG⟩ := Rudin.Support.StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab hf.1
    hgc.continuousOn
  have hG' := hasRSIntegral_of_hasDarbouxRSIntegral hab hG
  obtain ⟨E, hE⟩ := exists_tagged_square hab (hasRSIntegral_sub hf hG')
  refine ⟨g, E, hgc, hE, hasRSIntegral_nonneg hE (fun _ _ => sq_nonneg _), ?_⟩
  have hgap₀ := lowerSum_le_upperSum p hf.1 hM
  have hgap : upperSum p f α - lowerSum p f α < δ / (2 * M + 1) := by linarith
  have hsmall := (lt_div_iff₀ (show 0 < 2 * M + 1 by positivity)).mp hgap
  have hbound := (rs_value_le_upperSum p hE).trans (partitionPolygon_upper_error_le p hf.1 hM)
  nlinarith

/-- Continuous complex functions have raw integrals for arbitrary monotone
integrators, by the proved real continuous-existence result. -/
theorem exists_continuous_complex_rs {a b : ℝ} {α : ℝ → ℝ} {g : ℝ → ℂ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    ∃ z, HasComplexRSIntegral g α a b z := by
  obtain ⟨R, hR⟩ := Rudin.Support.StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab hα
    (Complex.continuous_re.comp_continuousOn hg)
  obtain ⟨I, hI⟩ := Rudin.Support.StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab hα
    (Complex.continuous_im.comp_continuousOn hg)
  exact ⟨⟨R, I⟩, hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_of_hasDarbouxRSIntegral hab hR, hasRSIntegral_of_hasDarbouxRSIntegral hab hI⟩⟩

/-- Exercise 12 for complex functions: construct a continuous function and an
actual weighted squared-error integral. All closed-interval cases are included. -/
theorem continuous_approximation_complex {a b ε : ℝ} {f : ℝ → ℂ}
    {α : ℝ → ℝ} {v : ℂ} (hab : a ≤ b)
    (hf : HasComplexRSIntegral f α a b v) (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (z : ℂ) (E : ℝ), Continuous g ∧
      HasComplexRSIntegral g α a b z ∧
      HasRSIntegral (fun x => ‖f x - g x‖ ^ 2) α a b E ∧
      0 ≤ E ∧ E < ε ^ 2 ∧ rsL2Norm α a b (fun x => f x - g x) < ε := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  obtain ⟨gr, Er, hgr, hEr, hEr₀, hErε⟩ :=
    exists_continuous_real_sq_error hab hr (show 0 < ε ^ 2 / 2 by positivity)
  obtain ⟨gi, Ei, hgi, hEi, hEi₀, hEiε⟩ :=
    exists_continuous_real_sq_error hab hi (show 0 < ε ^ 2 / 2 by positivity)
  let g : ℝ → ℂ := fun x => ⟨gr x, gi x⟩
  have hgc : Continuous g := by
    simp only [g, Complex.mk_eq_add_mul_I]
    fun_prop
  obtain ⟨z, hz⟩ := exists_continuous_complex_rs hab hf.1 hgc.continuousOn
  have hE : HasRSIntegral (fun x => ‖f x - g x‖ ^ 2) α a b (Er + Ei) := by
    apply hasRSIntegral_congr (hasRSIntegral_add hEr hEi)
    intro x _
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, g]
    ring
  have hsmall : Er + Ei < ε ^ 2 := by linarith
  refine ⟨g, z, Er + Ei, hgc, hz, hE, add_nonneg hEr₀ hEi₀, hsmall, ?_⟩
  rw [rsL2Norm_eq hE]
  exact (Real.sqrt_lt' hε).mpr hsmall

/-- Exercise 12 for real functions: the approximant remains real. The norm is
the same seminorm as Exercise 11 after the canonical embedding into `ℂ`. -/
theorem continuous_approximation_real {a b ε v : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f α a b v) (hε : 0 < ε) :
    ∃ (g : ℝ → ℝ) (z E : ℝ), Continuous g ∧ HasRSIntegral g α a b z ∧
      HasRSIntegral (fun x => (f x - g x) ^ 2) α a b E ∧
      0 ≤ E ∧ E < ε ^ 2 ∧
      rsL2Norm α a b (fun x => ((f x - g x : ℝ) : ℂ)) < ε := by
  obtain ⟨g, E, hgc, hE, hE₀, hsmall⟩ :=
    exists_continuous_real_sq_error hab hf (show 0 < ε ^ 2 by positivity)
  obtain ⟨z, hz⟩ := Rudin.Support.StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab hf.1
    hgc.continuousOn
  refine ⟨g, z, E, hgc, hasRSIntegral_of_hasDarbouxRSIntegral hab hz, hE, hE₀, hsmall, ?_⟩
  have hE' : HasRSIntegral (fun x => ‖((f x - g x : ℝ) : ℂ)‖ ^ 2) α a b E := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hE
  rw [rsL2Norm_eq hE']
  exact (Real.sqrt_lt' hε).mpr hsmall

end Rudin.Chapter06
