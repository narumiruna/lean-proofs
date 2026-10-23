module

public import Math.Rudin.Chapter08.Exercise16
public import Math.Rudin.Chapter06.Exercise17
public import Math.Rudin.Chapter03.Exercise14
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Chapter 8, Exercise 17

Source: Rudin, Third Edition, book page 200 (PDF page 209).
The coefficient bound uses the actual Chapter 6 Stieltjes integration-by-parts
identity. Pointwise convergence uses Fejer means and Chapter 3 Exercise 14(e).
Local monotonicity is handled by a bounded monotone replacement and localization.
Both monotonicity directions, the half-open endpoint, and all periodic joins
are included. One-sided limits are proved to exist.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Rudin.Support.StieltjesComplex Rudin.Support.StieltjesEquivalence
open Rudin.Support.StieltjesIntegralLaws Rudin.Support.RiemannIntegrability
namespace Rudin.Chapter08

lemma e17_monomial_norm (n : ℤ) (x : ℝ) : ‖fourierMonomial n x‖ = 1 := by
  rw [fourierMonomial, Complex.norm_exp]
  simp

lemma e17_monomial_deriv (n : ℤ) (x : ℝ) :
    HasDerivAt (fourierMonomial n) (Complex.I * n * fourierMonomial n x) x := by
  convert ((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * n)).cexp using 1
  · rfl
  · simp [fourierMonomial]
    ring

lemma e17_complex_norm_bound {a b M : ℝ} {α : ℝ → ℝ} {G : ℝ → ℂ} {B : ℂ}
    (hab : a ≤ b) (hB : HasComplexRSIntegral G α a b B)
    (hG : ∀ x ∈ Icc a b, ‖G x‖ ≤ M) : ‖B‖ ≤ M * (α b - α a) := by
  obtain ⟨v, hv, hb⟩ := exists_norm_bound hab hB
  exact hb.trans (hasRSIntegral_mono hv (hasRSIntegral_constant hab hB.1 M) hG)

/-- The coefficient estimate uses the literal Chapter 6 integration-by-parts theorem. -/
lemma e17_coefficient_closed {f : ℝ → ℝ} {M : ℝ}
    (hf : MonotoneOn f (Icc (-Real.pi) Real.pi))
    (hM : ∀ x ∈ Icc (-Real.pi) Real.pi, |f x| ≤ M) (n : ℤ) :
    ‖(n : ℂ) * fourierCoefficient (-Real.pi) (fun x => (f x : ℂ)) n‖ ≤ 2 * M / Real.pi := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let G := fourierMonomial (-n)
  let g := fun x => (Complex.I * (-n : ℤ)) * G x
  have hg : Continuous g := by dsimp [g, G, fourierMonomial]; fun_prop
  obtain ⟨A, B, hA, hB, he⟩ := Rudin.Chapter06.exercise17_stieltjes_parts_complex hab hf
    hg.continuousOn (fun x _ => (e17_monomial_deriv (-n) x).hasDerivWithinAt)
  have hbn : ‖B‖ ≤ f Real.pi - f (-Real.pi) := by
    simpa using e17_complex_norm_bound hab hB (M := 1)
      (fun x _ => le_of_eq (e17_monomial_norm (-n) x))
  have hAn : ‖A‖ ≤ 4 * M := by
    rw [he]
    have h := (norm_sub_le (f Real.pi • G Real.pi - f (-Real.pi) • G (-Real.pi)) B).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    simp only [norm_smul, Real.norm_eq_abs, G, e17_monomial_norm, mul_one] at h
    have h1 := hM Real.pi ⟨hab, le_rfl⟩
    have h0 := hM (-Real.pi) ⟨le_rfl, hab⟩
    linarith [le_abs_self (f Real.pi), neg_abs_le (f (-Real.pi))]
  have hAi := (complex_riemann_bridge hab hA).2
  have hrewrite : (fun x => f x • g x) =
      fun x => (Complex.I * (-n : ℤ)) * (fourierMonomial (-n) x * (f x : ℂ)) := by
    ext x
    simp only [g, G, Complex.real_smul]
    ring
  rw [hrewrite, intervalIntegral.integral_const_mul] at hAi
  have hnorm : ‖A‖ = ‖(n : ℂ) * ∫ x in -Real.pi..Real.pi,
      fourierMonomial (-n) x * (f x : ℂ)‖ := by
    rw [← hAi, mul_assoc, norm_mul, Complex.norm_I, one_mul]
    simp
  rw [fourierCoefficient, show -Real.pi + 2 * Real.pi = Real.pi by ring]
  simp only [Complex.real_smul]
  rw [show (n : ℂ) * ((↑(1 / (2 * Real.pi)) : ℂ) *
      ∫ x in -Real.pi..Real.pi, fourierMonomial (-n) x * (f x : ℂ)) =
      (↑(1 / (2 * Real.pi)) : ℂ) * ((n : ℂ) *
        ∫ x in -Real.pi..Real.pi, fourierMonomial (-n) x * (f x : ℂ)) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← hnorm]
  have h := mul_le_mul_of_nonneg_left hAn (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  convert h using 1
  ring

lemma e17_coefficient_congr {f g : ℝ → ℂ}
    (hfg : EqOn f g (Ioo (-Real.pi) Real.pi)) (n : ℤ) :
    fourierCoefficient (-Real.pi) f n = fourierCoefficient (-Real.pi) g n := by
  unfold fourierCoefficient
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  congr 1
  exact intervalIntegral.integral_congr_Ioo_of_le (by linarith [Real.pi_pos])
    (fun x hx => by rw [hfg hx])

lemma e17_coefficient_halfopen {f : ℝ → ℝ} {M : ℝ}
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi))
    (hM : ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) (n : ℤ) :
    ‖(n : ℂ) * fourierCoefficient (-Real.pi) (fun x => (f x : ℂ)) n‖ ≤ 2 * M / Real.pi := by
  let F := fun x => if x = Real.pi then M else f x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (-Real.pi) ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  have hF : MonotoneOn F (Icc (-Real.pi) Real.pi) := by
    intro x hx y hy hxy
    by_cases hxπ : x = Real.pi
    · have hyπ : y = Real.pi := by linarith [hy.2]
      simp [F, hxπ, hyπ]
    · by_cases hyπ : y = Real.pi
      · simp only [F, ite_eq_right hxπ, ite_eq_left hyπ]
        exact (le_abs_self _).trans (hM x ⟨hx.1, lt_of_le_of_ne hx.2 hxπ⟩)
      · simp only [F, ite_eq_right hxπ, ite_eq_right hyπ]
        exact hf ⟨hx.1, lt_of_le_of_ne hx.2 hxπ⟩ ⟨hy.1, lt_of_le_of_ne hy.2 hyπ⟩ hxy
  have hb : ∀ x ∈ Icc (-Real.pi) Real.pi, |F x| ≤ M := by
    intro x hx
    dsimp [F]
    split_ifs with h
    · exact (abs_of_nonneg hM0).le
    · exact hM x ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
  have he := e17_coefficient_congr (f := fun x => (f x : ℂ)) (g := fun x => (F x : ℂ))
    (fun x hx => by simp [F, hx.2.ne]) n
  rw [he]
  exact e17_coefficient_closed hF hb n

lemma e17_coefficient_neg (f : ℝ → ℂ) (n : ℤ) :
    fourierCoefficient (-Real.pi) (fun x => -f x) n = -fourierCoefficient (-Real.pi) f n := by
  simp only [fourierCoefficient, mul_neg, intervalIntegral.integral_neg, smul_neg]

/-- Both directions of monotonicity on the source half-open interval. -/
theorem exercise17_coefficient_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hM : ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) (n : ℤ) :
    ‖(n : ℂ) * fourierCoefficient (-Real.pi) (fun x => (f x : ℂ)) n‖ ≤ 2 * M / Real.pi := by
  rcases hf with hf | hf
  · exact e17_coefficient_halfopen hf hM n
  · have hn : MonotoneOn (fun x => -f x) (Ico (-Real.pi) Real.pi) :=
      fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
    have h := e17_coefficient_halfopen hn (fun x hx => by simpa using hM x hx) n
    simpa only [Complex.ofReal_neg, e17_coefficient_neg, mul_neg, norm_neg] using h

/-- Boundedness of the full integer-indexed sequence, not only positive modes. -/
theorem exercise17_bounded_coefficients {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hb : ∃ M : ℝ, ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) :
    ∃ C : ℝ, ∀ n : ℤ,
      ‖(n : ℂ) * fourierCoefficient (-Real.pi) (fun x => (f x : ℂ)) n‖ ≤ C := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨2 * M / Real.pi, exercise17_coefficient_bound hf hM⟩

lemma e17_tauberian {f : ℝ → ℂ} {C : ℝ}
    (hC : ∀ n : ℤ, ‖(n : ℂ) * fourierCoefficient (-Real.pi) f n‖ ≤ C)
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : RiemannIntegrableComplex f (-Real.pi) Real.pi) (x : ℝ) {left right : ℂ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 left)) (hr : Tendsto f (𝓝[>] x) (𝓝 right)) :
    Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 ((left + right) / 2)) := by
  apply Rudin.Chapter03.exercise14_e_convergence (M := 2 * C)
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hd : Rudin.Chapter03.exercise14_diff (fun N => fourierPartialSum f N x) (j + 1) =
        fourierCoefficient (-Real.pi) f (j + 1) * fourierMonomial (j + 1) x +
        fourierCoefficient (-Real.pi) f (-(j + 1)) * fourierMonomial (-(j + 1)) x := by
      simp [Rudin.Chapter03.exercise14_diff, fourierPartialSum, Finset.sum_range_succ]
    rw [hd, mul_add]
    have h1 : ‖(↑(j + 1 : ℕ) : ℂ) *
        (fourierCoefficient (-Real.pi) f (j + 1) * fourierMonomial (j + 1) x)‖ ≤ C := by
      rw [← mul_assoc, norm_mul, e17_monomial_norm, mul_one]
      simpa using hC (j + 1)
    have h2 : ‖(↑(j + 1 : ℕ) : ℂ) *
        (fourierCoefficient (-Real.pi) f (-(j + 1)) * fourierMonomial (-(j + 1)) x)‖ ≤ C := by
      rw [← mul_assoc, norm_mul, e17_monomial_norm, mul_one]
      simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one, neg_mul, norm_neg] using hC (-(j + 1))
    exact (norm_add_le _ _).trans (by linarith)
  · have hm := exercise16_pointwise_fejer hp hf x hl hr
    convert hm using 1
    ext N
    simp [Rudin.Chapter03.exercise14_mean, fejerMean, Complex.real_smul]

lemma e17_riemann_monotone {a b M : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))
    (hb : ∀ x ∈ Icc a b, |f x| ≤ M) :
    RiemannIntegrableComplex (fun x => (f x : ℂ)) a b := by
  have hcount : Set.Countable {x ∈ Ioo a b | ¬ContinuousWithinAt f (Ioo a b) x} := by
    rcases hf with hf | hf
    · exact hf.countable_not_continuousWithinAt
    · exact hf.countable_not_continuousWithinAt
  have hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hcount.ae_notMem volume, volume.ae_ne a, volume.ae_ne b] with x hx hxa hxb hmem
    have hi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxa), lt_of_le_of_ne hmem.2 hxb⟩
    have hcont : ContinuousWithinAt f (Ioo a b) x := by simpa [hi] using hx
    exact (hcont.continuousAt (Ioo_mem_nhds hi.1 hi.2)).continuousWithinAt
  have hr := Rudin.Support.StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral hab
    (hasDarbouxRSIntegral_of_ae_continuousWithinAt hab hb hc)
  refine ⟨((∫ x in a..b, f x : ℝ) : ℂ), hasComplexRSIntegral_iff.mpr ⟨?_, ?_⟩⟩
  · simpa using hr
  · simpa using hasRSIntegral_constant hab
      (show MonotoneOn id (Icc a b) from fun _ _ _ _ h => h) 0

/-- Part (b), for the periodic extension, with its one-sided limits identified. -/
theorem exercise17_fourier_limit {f : ℝ → ℝ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hb : ∃ M : ℝ, ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M)
    (x : ℝ) {left right : ℝ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 left)) (hr : Tendsto f (𝓝[>] x) (𝓝 right)) :
    Tendsto (fun N => fourierPartialSum (fun t => (f t : ℂ)) N x) atTop
      (𝓝 (((left : ℂ) + (right : ℂ)) / 2)) := by
  obtain ⟨C, hC⟩ := exercise17_bounded_coefficients hf hb
  obtain ⟨M, hM⟩ := hb
  have hi := e17_riemann_monotone (f := f) (M := M) (by linarith [Real.pi_pos])
    (hf.imp (fun h => h.mono Ioo_subset_Ico_self) (fun h => h.mono Ioo_subset_Ico_self))
    (fun t ht => ?_)
  · exact e17_tauberian hC (fun t => by simp only [hp t]) hi x
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hl)
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr)
  · by_cases htπ : t = Real.pi
    · subst t
      have he : f Real.pi = f (-Real.pi) := by convert hp (-Real.pi) using 1; congr 1; ring
      rw [he]
      exact hM _ ⟨le_rfl, by linarith [Real.pi_pos]⟩
    · exact hM _ ⟨ht.1, lt_of_le_of_ne ht.2 htπ⟩

lemma e17_interval_limits {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))
    (hb : ∃ M : ℝ, ∀ x ∈ Ioo a b, |f x| ≤ M) :
    (∃ l : ℝ, Tendsto f (𝓝[<] b) (𝓝 l)) ∧
      ∃ r : ℝ, Tendsto f (𝓝[>] a) (𝓝 r) := by
  obtain ⟨M, hM⟩ := hb
  have hu : BddAbove (f '' Ioo a b) := ⟨M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hM x hx)⟩
  have hl : BddBelow (f '' Ioo a b) := ⟨-M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x hx)).1⟩
  rcases hf with hf | hf
  · exact ⟨⟨_, hf.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hab) hu⟩,
      ⟨_, hf.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hab) hl⟩⟩
  · exact ⟨⟨_, hf.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hab) hl⟩,
      ⟨_, hf.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hab) hu⟩⟩

lemma e17_periodic_left {f : ℝ → ℝ} {p x l : ℝ}
    (hp : Function.Periodic f p) (hl : Tendsto f (𝓝[<] x) (𝓝 l)) :
    Tendsto f (𝓝[<] (x + p)) (𝓝 l) := by
  have ht : Tendsto (fun t : ℝ => t - p) (𝓝[<] (x + p)) (𝓝[<] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => t - p) := by fun_prop
      simpa only [add_sub_cancel_right] using
        (hc.tendsto (x + p)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t < x + p at ht
      change t - p < x
      linarith
  simpa only [Function.comp_def, hp.sub_eq] using hl.comp ht

lemma e17_periodic_right {f : ℝ → ℝ} {p x r : ℝ}
    (hp : Function.Periodic f p) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    Tendsto f (𝓝[>] (x + p)) (𝓝 r) := by
  have ht : Tendsto (fun t : ℝ => t - p) (𝓝[>] (x + p)) (𝓝[>] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => t - p) := by fun_prop
      simpa only [add_sub_cancel_right] using
        (hc.tendsto (x + p)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change x + p < t at ht
      change x < t - p
      linarith
  simpa only [Function.comp_def, hp.sub_eq] using hr.comp ht

/-- Periodicity also supplies both limits at the joined endpoints. -/
theorem exercise17_one_sided_limits {f : ℝ → ℝ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hb : ∃ M : ℝ, ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) (x : ℝ) :
    (∃ l : ℝ, Tendsto f (𝓝[<] x) (𝓝 l)) ∧
      ∃ r : ℝ, Tendsto f (𝓝[>] x) (𝓝 r) := by
  have hP : 0 < 2 * Real.pi := by positivity
  let y := toIcoMod hP (-Real.pi) x
  have hy : y ∈ Ico (-Real.pi) Real.pi := by
    convert toIcoMod_mem_Ico hP (-Real.pi) x using 1
    congr 1
    ring
  have hi (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ Ico (-Real.pi) Real.pi) :=
    e17_interval_limits hab
      (hf.imp (fun h => h.mono hsub) (fun h => h.mono hsub))
      (hb.imp (fun M hM t ht => hM t (hsub ht)))
  have hyl : (∃ l : ℝ, Tendsto f (𝓝[<] y) (𝓝 l)) := by
    by_cases he : y = -Real.pi
    · obtain ⟨l, hl⟩ := (hi (-Real.pi) Real.pi (by linarith [Real.pi_pos]) Ioo_subset_Ico_self).1
      refine ⟨l, ?_⟩
      have h := e17_periodic_left hp.neg hl
      simpa only [he, show Real.pi + -(2 * Real.pi) = -Real.pi by ring] using h
    · exact (hi (-Real.pi) y (lt_of_le_of_ne hy.1 (Ne.symm he))
        (fun t ht => ⟨ht.1.le, ht.2.trans hy.2⟩)).1
  have hyr := (hi y Real.pi hy.2 (fun t ht => ⟨hy.1.trans ht.1.le, ht.2⟩)).2
  have hp' : Function.Periodic f (x - y) := by
    rw [show x - y = toIcoDiv hP (-Real.pi) x • (2 * Real.pi) from
      self_sub_toIcoMod hP (-Real.pi) x]
    exact hp.zsmul _
  obtain ⟨l, hl⟩ := hyl
  obtain ⟨r, hr⟩ := hyr
  exact ⟨⟨l, by simpa using e17_periodic_left hp' hl⟩,
    ⟨r, by simpa using e17_periodic_right hp' hr⟩⟩

/-- No one-sided-limit existence is an assumption in this form of part (b). -/
theorem exercise17_pointwise {f : ℝ → ℝ}
    (hp : Function.Periodic f (2 * Real.pi))
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hb : ∃ M : ℝ, ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun N => fourierPartialSum (fun t => (f t : ℂ)) N x) atTop
      (𝓝 ((((Function.leftLim f x : ℝ) : ℂ) + ((Function.rightLim f x : ℝ) : ℂ)) / 2)) := by
  obtain ⟨hl, hr⟩ := exercise17_one_sided_limits hp hf hb x
  exact exercise17_fourier_limit hp hf hb x
    (tendsto_leftLim_of_tendsto hl) (tendsto_rightLim_of_tendsto hr)

/-- The periodic extension uses the source half-open fundamental interval. -/
def exercise17Periodic (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.liftIco (2 * Real.pi) (-Real.pi) f (x : AddCircle (2 * Real.pi))

lemma e17_periodic (f : ℝ → ℝ) : Function.Periodic (exercise17Periodic f) (2 * Real.pi) := by
  intro x
  simp [exercise17Periodic]

lemma e17_periodic_eq (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ico (-Real.pi) Real.pi) :
    exercise17Periodic f x = f x := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  apply AddCircle.liftIco_coe_apply
  convert hx using 1
  congr 1
  ring

lemma e17_partialSum_congr {f g : ℝ → ℂ} (hfg : EqOn f g (Ioo (-Real.pi) Real.pi))
    (N : ℕ) (x : ℝ) : fourierPartialSum f N x = fourierPartialSum g N x := by
  simp only [fourierPartialSum, e17_coefficient_congr hfg]

/-- Part (b) for original half-open data; the extension and both limits are constructed. -/
theorem exercise17_periodic_extension_limit {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ico (-Real.pi) Real.pi) ∨ AntitoneOn f (Ico (-Real.pi) Real.pi))
    (hb : ∃ M : ℝ, ∀ x ∈ Ico (-Real.pi) Real.pi, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun N => fourierPartialSum (fun t => (f t : ℂ)) N x) atTop
      (𝓝 ((((Function.leftLim (exercise17Periodic f) x : ℝ) : ℂ) +
        ((Function.rightLim (exercise17Periodic f) x : ℝ) : ℂ)) / 2)) := by
  have hf' : MonotoneOn (exercise17Periodic f) (Ico (-Real.pi) Real.pi) ∨
      AntitoneOn (exercise17Periodic f) (Ico (-Real.pi) Real.pi) := by
    rcases hf with hf | hf
    · exact Or.inl (fun s hs t ht hst => by
        simpa only [e17_periodic_eq f hs, e17_periodic_eq f ht] using hf hs ht hst)
    · exact Or.inr (fun s hs t ht hst => by
        simpa only [e17_periodic_eq f hs, e17_periodic_eq f ht] using hf hs ht hst)
  have hb' : ∃ M : ℝ, ∀ t ∈ Ico (-Real.pi) Real.pi, |exercise17Periodic f t| ≤ M := hb.imp (fun M hM t ht => by simpa only [e17_periodic_eq f ht] using hM t ht)
  have h := exercise17_pointwise (e17_periodic f) hf' hb' x
  have he (N : ℕ) : fourierPartialSum (fun t => (f t : ℂ)) N x =
      fourierPartialSum (fun t => (exercise17Periodic f t : ℂ)) N x := by
    apply e17_partialSum_congr
    intro t ht
    simp only [e17_periodic_eq f (Ioo_subset_Ico_self ht)]
  simpa only [← he] using h

lemma e17_bounded_of_monotone {g : ℝ → ℝ} (hg : Monotone g ∨ Antitone g) :
    ∃ M : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi, |g t| ≤ M := by
  refine ⟨|g (-Real.pi)| + |g Real.pi|, ?_⟩
  intro t ht
  rcases hg with hg | hg
  · have hl := hg ht.1
    have hu := hg ht.2
    exact abs_le.mpr ⟨by linarith [neg_abs_le (g (-Real.pi)), abs_nonneg (g Real.pi)],
      by linarith [le_abs_self (g Real.pi), abs_nonneg (g (-Real.pi))]⟩
  · have hu := hg ht.1
    have hl := hg ht.2
    exact abs_le.mpr ⟨by linarith [neg_abs_le (g Real.pi), abs_nonneg (g (-Real.pi))],
      by linarith [le_abs_self (g (-Real.pi)), abs_nonneg (g Real.pi)]⟩

/-- Clamp strictly inside the monotonicity interval, not at possibly singular endpoints. -/
lemma e17_local_replacement {f : ℝ → ℝ} {a b x : ℝ}
    (hf : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) (hx : x ∈ Ioo a b) :
    ∃ g : ℝ → ℝ, (Monotone g ∨ Antitone g) ∧
      (∃ M : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi, |g t| ≤ M) ∧
      ∃ δ > (0 : ℝ), ∀ t : ℝ, |t - x| < δ → g t = f t := by
  let c := (a + x) / 2
  let d := (x + b) / 2
  have hac : a < c := by dsimp [c]; linarith [hx.1]
  have hcx : c < x := by dsimp [c]; linarith [hx.1]
  have hxd : x < d := by dsimp [d]; linarith [hx.2]
  have hdb : d < b := by dsimp [d]; linarith [hx.2]
  let g := fun t => f (max c (min d t))
  have hrange (t : ℝ) : max c (min d t) ∈ Ioo a b :=
    ⟨hac.trans_le (le_max_left _ _),
      (max_le (hcx.trans hxd).le (min_le_left _ _)).trans_lt hdb⟩
  have hmono : Monotone g ∨ Antitone g := by
    rcases hf with hf | hf
    · exact Or.inl (fun s t hst => hf (hrange s) (hrange t)
        (max_le_max le_rfl (min_le_min le_rfl hst)))
    · exact Or.inr (fun s t hst => hf (hrange s) (hrange t)
        (max_le_max le_rfl (min_le_min le_rfl hst)))
  refine ⟨g, hmono, e17_bounded_of_monotone hmono,
    min (x - c) (d - x), lt_min (sub_pos.mpr hcx) (sub_pos.mpr hxd), ?_⟩
  intro t ht
  have hl := (abs_lt.mp (ht.trans_le (min_le_left _ _))).1
  have hu := (abs_lt.mp (ht.trans_le (min_le_right _ _))).2
  dsimp [g]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

lemma e17_mode_integral (f : ℝ → ℂ) (n : ℤ) (x : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, fourierMonomial n (x - t) * f t) =
      fourierCoefficient (-Real.pi) f n * fourierMonomial n x := by
  simp_rw [fourierMonomial_sub, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  simp only [fourierCoefficient, Complex.real_smul,
    show -Real.pi + 2 * Real.pi = Real.pi by ring]
  ring

lemma e17_partial_integral {f : ℝ → ℂ}
    (hi : IntervalIntegrable f volume (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, (dirichletKernel N (x - t) : ℂ) * f t) := by
  have hm (n : ℤ) : IntervalIntegrable
      (fun t => fourierMonomial n (x - t) * f t) volume (-Real.pi) Real.pi :=
    hi.continuousOn_mul (by unfold fourierMonomial; fun_prop)
  simp_rw [dirichletKernel_complex, add_mul, one_mul, Finset.sum_mul, add_mul]
  have hs : IntervalIntegrable (fun t => ∑ k ∈ Finset.range N,
      (fourierMonomial (k + 1) (x - t) * f t + fourierMonomial (-(k + 1)) (x - t) * f t))
      volume (-Real.pi) Real.pi := by
    convert IntervalIntegrable.sum (Finset.range N)
      (fun k _ => (hm (k + 1)).add (hm (-(k + 1)))) using 1
    ext t
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_add hi hs,
    intervalIntegral.integral_finsetSum (s := Finset.range N)
      (fun (k : ℕ) _ => (hm (k + 1)).add (hm (-(k + 1))))]
  simp_rw [intervalIntegral.integral_add (hm _) (hm _)]
  simp only [smul_add, Finset.smul_sum]
  simp_rw [e17_mode_integral]
  unfold fourierPartialSum
  congr 1
  have h := e17_mode_integral f 0 x
  simpa [fourierMonomial] using h.symm

lemma e17_mode_limit {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (x : ℝ)
    (j : ℕ → ℤ) (hj : Function.Injective j) :
    Tendsto (fun n => fourierCoefficient (-Real.pi) f (j n) * fourierMonomial (j n) x)
      atTop (𝓝 0) := by
  have hh : MemLp f 2 (volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hf
  have hsum := ((source_parseval (-Real.pi) hh).summable.comp_injective hj).tendsto_atTop_zero
  have hn : Tendsto (fun n => ‖fourierCoefficient (-Real.pi) f (j n)‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul, e17_monomial_norm, mul_one] using hn

lemma e17_cos_integral (f : ℝ → ℂ)
    (hi : IntervalIntegrable f volume (-Real.pi) Real.pi) (n : ℕ) (x : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, (Real.cos ((n : ℝ) * (x - t)) : ℂ) * f t) =
      (fourierCoefficient (-Real.pi) f n * fourierMonomial n x +
        fourierCoefficient (-Real.pi) f (-n) * fourierMonomial (-n) x) / 2 := by
  have he (t : ℝ) : (Real.cos ((n : ℝ) * (x - t)) : ℂ) * f t =
      (fourierMonomial n (x - t) * f t + fourierMonomial (-n) (x - t) * f t) / 2 := by
    simp only [fourierMonomial_trig, Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_neg]
    ring
  have hm (k : ℤ) : IntervalIntegrable
      (fun t => fourierMonomial k (x - t) * f t) volume (-Real.pi) Real.pi :=
    hi.continuousOn_mul (by unfold fourierMonomial; fun_prop)
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hm _) (hm _)]
  change (1 / (2 * Real.pi) : ℝ) • ((_ + _) / (2 : ℂ)) = _
  rw [← smul_div_assoc, smul_add, e17_mode_integral, e17_mode_integral]

lemma e17_cos_limit {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (x : ℝ) :
    Tendsto (fun n : ℕ => (1 / (2 * Real.pi) : ℝ) •
      (∫ t in -Real.pi..Real.pi, (Real.cos ((n : ℝ) * (x - t)) : ℂ) * f t)) atTop (𝓝 0) := by
  have hi : IntervalIntegrable f volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mpr
      (hf.integrable (by norm_num))
  have hp := e17_mode_limit hf x (fun n => (n : ℤ)) Nat.cast_injective
  have hn := e17_mode_limit hf x (fun n => -(n : ℤ)) (neg_injective.comp Nat.cast_injective)
  simpa only [e17_cos_integral f hi, add_zero, zero_div] using (hp.add hn).div_const 2

lemma e17_local_quotient {f g : ℝ → ℂ} {x δ M : ℝ}
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hδ : 0 < δ)
    (hfg : ∀ t : ℝ, |t - x| < δ → f t = g t)
    (hM : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖f t - g t‖ ≤ M) :
    ∃ h : ℝ → ℂ, MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      ∀ t ∈ Icc (-Real.pi) Real.pi,
        ((1 - Real.cos (x - t) : ℝ) : ℂ) * h t = f t - g t := by
  let K := Icc (-Real.pi) Real.pi \ Metric.ball x δ
  have hK : IsCompact K := isCompact_Icc.diff Metric.isOpen_ball
  let w := fun t => (((1 - Real.cos (x - t) : ℝ) : ℂ))⁻¹
  have hne (t : ℝ) (ht : t ∈ K) : 1 - Real.cos (x - t) ≠ 0 := by
    intro he
    have hc : Real.cos (x - t) = 1 := by linarith
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [ht.1.2, hx.1]) (by linarith [ht.1.1, hx.2])).mp hc
    have htx : t = x := by linarith
    exact ht.2 (by simpa [htx] using hδ)
  have hw : ContinuousOn w K := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    exact_mod_cast hne t ht
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hdiff : IntegrableOn (fun t => f t - g t) (Icc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hf.sub hg)
  have hprod := IntegrableOn.continuousOn_mul hw (hdiff.mono_set (fun _ ht => ht.1)) hK
  let h := K.indicator (fun t => w t * (f t - g t))
  have hhi : Integrable h := (integrable_indicator_iff hK.measurableSet).mpr hprod
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hw
  have hbound (t : ℝ) : ‖h t‖ ≤ |C| * |M| := by
    by_cases ht : t ∈ K
    · simp only [h, indicator_of_mem ht, norm_mul]
      exact mul_le_mul ((hC t ht).trans (le_abs_self _)) ((hM t ht.1).trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _)
    · simp only [h, indicator_of_notMem ht, norm_zero]
      positivity
  refine ⟨h, MemLp.of_bound (hhi.restrict.aestronglyMeasurable) (|C| * |M|)
    (ae_of_all _ hbound), ?_⟩
  intro t ht
  by_cases htK : t ∈ K
  · simp only [h, indicator_of_mem htK, w]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hne t htK), one_mul]
  · have hnear : |t - x| < δ := by
      have : t ∈ Metric.ball x δ := by simpa only [K, Set.mem_sdiff, ht, true_and, not_not] using htK
      simpa only [Metric.mem_ball, Real.dist_eq] using this
    simp only [h, indicator_of_notMem htK, mul_zero, hfg t hnear, sub_self]

/-- Localization for the actual symmetric Fourier sums at an interior point.
The auxiliary Fourier coefficients tend to zero by the proved Parseval identity. -/
lemma exercise17_localization {f g : ℝ → ℂ} {x δ M : ℝ}
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hδ : 0 < δ)
    (hfg : ∀ t : ℝ, |t - x| < δ → f t = g t)
    (hM : ∀ t ∈ Icc (-Real.pi) Real.pi, ‖f t - g t‖ ≤ M) :
    Tendsto (fun N => fourierPartialSum f N x - fourierPartialSum g N x) atTop (𝓝 0) := by
  obtain ⟨h, hh, he⟩ := e17_local_quotient hf hg hx hδ hfg hM
  have hi : IntervalIntegrable h volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mpr
      (hh.integrable (by norm_num))
  have hD (N : ℕ) : Continuous (fun t : ℝ => (dirichletKernel N (x - t) : ℂ)) := by
    unfold dirichletKernel
    fun_prop
  have hcos (N : ℕ) : IntervalIntegrable
      (fun t => (Real.cos ((N : ℝ) * (x - t)) : ℂ) * h t) volume (-Real.pi) Real.pi :=
    hi.continuousOn_mul (by fun_prop)
  have hid (N : ℕ) : fourierPartialSum f N x - fourierPartialSum g N x =
      (1 / (2 * Real.pi) : ℝ) •
        (∫ t in -Real.pi..Real.pi, (Real.cos ((N : ℝ) * (x - t)) : ℂ) * h t) -
      (1 / (2 * Real.pi) : ℝ) •
        (∫ t in -Real.pi..Real.pi, (Real.cos (((N + 1 : ℕ) : ℝ) * (x - t)) : ℂ) * h t) := by
    rw [e17_partial_integral hf, e17_partial_integral hg, ← smul_sub,
      ← intervalIntegral.integral_sub (hf.continuousOn_mul (hD N).continuousOn)
        (hg.continuousOn_mul (hD N).continuousOn), ← smul_sub,
      ← intervalIntegral.integral_sub (hcos N) (hcos (N + 1))]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-Real.pi) Real.pi := by
      simpa only [uIcc_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])] using ht
    dsimp only
    rw [← mul_sub, ← he t ht']
    have hk := congrArg Complex.ofReal (dirichletKernel_telescope N (x - t))
    simp only [Complex.ofReal_mul, Complex.ofReal_sub] at hk
    calc
      _ = (((1 - Real.cos (x - t) : ℝ) : ℂ) * (dirichletKernel N (x - t) : ℂ)) * h t := by ring
      _ = _ := by
        rw [Complex.ofReal_sub, hk]
        ring
  have hz := (e17_cos_limit hh x).sub ((e17_cos_limit hh x).comp (tendsto_add_atTop_nat 1))
  simpa only [Function.comp_def, ← hid, sub_self] using hz

/-- Part (c): local monotonicity suffices, by localization and a bounded monotone replacement. -/
theorem exercise17_local_monotone {f : ℝ → ℝ}
    (hf : RiemannIntegrableComplex (fun t => (f t : ℂ)) (-Real.pi) Real.pi)
    {a b x : ℝ} (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi)
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) (hx : x ∈ Ioo a b) :
    Tendsto (fun N => fourierPartialSum (fun t => (f t : ℂ)) N x) atTop
      (𝓝 ((((Function.leftLim f x : ℝ) : ℂ) + ((Function.rightLim f x : ℝ) : ℂ)) / 2)) := by
  have hxπ : x ∈ Ioo (-Real.pi) Real.pi := ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  obtain ⟨g, hgm, ⟨Mg, hMg⟩, δ, hδ, hnear⟩ := e17_local_replacement hm hx
  have hmhalf : MonotoneOn g (Ico (-Real.pi) Real.pi) ∨
      AntitoneOn g (Ico (-Real.pi) Real.pi) :=
    hgm.imp (fun h => h.monotoneOn _) (fun h => h.antitoneOn _)
  have hbhalf : ∃ M : ℝ, ∀ t ∈ Ico (-Real.pi) Real.pi, |g t| ≤ M :=
    ⟨Mg, fun t ht => hMg t (Ico_subset_Icc_self ht)⟩
  have hg_limit := exercise17_periodic_extension_limit hmhalf hbhalf x
  have eg : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.ball_mem_nhds x hδ] with t ht
    exact hnear t (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)
  have ep : exercise17Periodic g =ᶠ[𝓝 x] g := by
    filter_upwards [Ioo_mem_nhds hxπ.1 hxπ.2] with t ht
    exact e17_periodic_eq g (Ioo_subset_Ico_self ht)
  have hgl : Tendsto g (𝓝[<] x) (𝓝 (Function.leftLim g x)) := by
    rcases hgm with hgm | hgm <;> exact hgm.tendsto_leftLim x
  have hgr : Tendsto g (𝓝[>] x) (𝓝 (Function.rightLim g x)) := by
    rcases hgm with hgm | hgm <;> exact hgm.tendsto_rightLim x
  have hlf := hgl.congr' (eg.filter_mono nhdsWithin_le_nhds)
  have hrf := hgr.congr' (eg.filter_mono nhdsWithin_le_nhds)
  have hlp := hgl.congr' (ep.symm.filter_mono nhdsWithin_le_nhds)
  have hrp := hgr.congr' (ep.symm.filter_mono nhdsWithin_le_nhds)
  have hel : Function.leftLim (exercise17Periodic g) x = Function.leftLim f x :=
    (leftLim_eq_of_tendsto hlp).trans (leftLim_eq_of_tendsto hlf).symm
  have her : Function.rightLim (exercise17Periodic g) x = Function.rightLim f x :=
    (rightLim_eq_of_tendsto hrp).trans (rightLim_eq_of_tendsto hrf).symm
  rw [hel, her] at hg_limit
  obtain ⟨z, hz⟩ := hf
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hfi := (complex_riemann_bridge hab hz).1
  obtain ⟨Mf, hMf⟩ := hz.2.1
  have hgri := e17_riemann_monotone hab
    (hgm.imp (fun h => h.monotoneOn _) (fun h => h.antitoneOn _)) hMg
  obtain ⟨w, hw⟩ := hgri
  have hgi := (complex_riemann_bridge hab hw).1
  have hloc := exercise17_localization hfi hgi hxπ hδ
    (fun t ht => by simp only [hnear t ht])
    (M := Mf + Mg) (fun t ht => (norm_sub_le _ _).trans (add_le_add (hMf t ht)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hMg t ht)))
  simpa only [sub_add_cancel, zero_add] using hloc.add hg_limit

/-- The one-sided limits in part (c) exist; the limit functions have no fallback values. -/
theorem exercise17_local_one_sided_limits {f : ℝ → ℝ} {a b x : ℝ}
    (hm : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) (hx : x ∈ Ioo a b) :
    Tendsto f (𝓝[<] x) (𝓝 (Function.leftLim f x)) ∧
      Tendsto f (𝓝[>] x) (𝓝 (Function.rightLim f x)) := by
  obtain ⟨g, hgm, _, δ, hδ, hnear⟩ := e17_local_replacement hm hx
  have eg : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.ball_mem_nhds x hδ] with t ht
    exact hnear t (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)
  have hgl : Tendsto g (𝓝[<] x) (𝓝 (Function.leftLim g x)) := by
    rcases hgm with hgm | hgm <;> exact hgm.tendsto_leftLim x
  have hgr : Tendsto g (𝓝[>] x) (𝓝 (Function.rightLim g x)) := by
    rcases hgm with hgm | hgm <;> exact hgm.tendsto_rightLim x
  exact ⟨tendsto_leftLim_of_tendsto ⟨_, hgl.congr' (eg.filter_mono nhdsWithin_le_nhds)⟩,
    tendsto_rightLim_of_tendsto ⟨_, hgr.congr' (eg.filter_mono nhdsWithin_le_nhds)⟩⟩

end Rudin.Chapter08
