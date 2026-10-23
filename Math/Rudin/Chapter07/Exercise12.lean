module

public import Mathlib
public import Math.Rudin.Chapter06.Exercise07
public import Math.Rudin.Support.StieltjesComplex

/-! # Chapter 7, Exercise 12
Source: book page 167, PDF page 176. Improper integrals are the sum of the
two endpoint limits, split at 1. Every finite truncation has an actual
closed-cell Darboux integral. Measurability and absolute integrability are
conclusions derived from the source assumptions.
-/

@[expose] public section

namespace Rudin.Chapter07

open Set Filter MeasureTheory
open scoped Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesEquivalence Rudin.Support.StieltjesIntegralLaws
  Rudin.Support.RiemannIntegrability Rudin.Chapter06

/-- Proper Riemann integrability on every compact interval in the positive ray.
Singleton intervals are included; their integrability is automatic. -/
def LocallyRiemannPositive (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b →
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x)

/-- The improper integral on `(0,∞)` uses separate limits at both ends. -/
def HasPositiveImproperRiemannIntegral (f : ℝ → ℝ) (v : ℝ) : Prop :=
  ∃ l r : ℝ, HasImproperRiemannIntegralLeft f 0 1 l ∧
    HasImproperRiemannIntegralTop f 1 r ∧ v = l + r

private theorem positive_cut_tendsto :
    Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n ↦ (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)⟩

private theorem positive_cover :
    AECover (volume.restrict (Ioi (0 : ℝ))) atTop
      (fun n : ℕ ↦ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
  refine ⟨?_, fun _ ↦ measurableSet_Icc⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hx),
    ht.eventually (eventually_ge_atTop x)] with n hn hn'
  exact ⟨hn.le, hn'⟩

/-- Local Riemann data imply measurability on the whole open ray. -/
theorem LocallyRiemannPositive.aestronglyMeasurable {f : ℝ → ℝ}
    (hf : LocallyRiemannPositive f) : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  apply positive_cover.aestronglyMeasurable
  intro n
  have hle : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr
    (show Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ⊆ Ioi 0 from
      fun x hx ↦ lt_of_lt_of_le (by positivity) hx.1)]
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp
    (intervalIntegrable_and_integral_eq hle (hf _ _ (by positivity) hle)).1).aestronglyMeasurable

/-- A finite nonnegative improper Riemann integral gives genuine Lebesgue
integrability; this bridge is proved from the two endpoint limits. -/
theorem positive_integrable_of_improper_nonneg {g : ℝ → ℝ} {v : ℝ}
    (hg : HasPositiveImproperRiemannIntegral g v) (hn : ∀ x > 0, 0 ≤ g x) :
    IntegrableOn g (Ioi 0) := by
  obtain ⟨l, r, hl, hr, _⟩ := hg
  have htop : IntegrableOn g (Ioi 1) :=
    integrableOn_of_improperRiemannTop_nonneg hr (fun x hx ↦ hn x (lt_of_lt_of_le zero_lt_one hx))
  have hcut (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hloc (n : ℕ) : IntegrableOn g (Ioc (1 / ((n : ℝ) + 1)) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hcut n)).mp
      (intervalIntegrable_and_integral_eq (hcut n) (hl.2.1 _ (by positivity) (hcut n))).1
  have hlim : Tendsto (fun n : ℕ ↦ ∫ x in Ioc (1 / ((n : ℝ) + 1)) 1, ‖g x‖)
      atTop (𝓝 l) := by
    convert hl.2.2.comp positive_cut_tendsto using 1
    ext n
    simp only [Function.comp_apply]
    rw [intervalIntegral.integral_of_le (hcut n)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact Real.norm_of_nonneg (hn x (lt_trans (by positivity) hx.1))
  obtain ⟨M, hM⟩ := hlim.isBoundedUnder_le
  have hleft : IntegrableOn g (Ioc 0 1) :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hloc
      tendsto_one_div_add_atTop_nhds_zero_nat hM
  have he : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← he]
  exact hleft.union htop

/-- Absolute integrability supplies both endpoint limits only after all
proper Riemann witnesses have been proved. -/
theorem positive_improper_of_integrable {f : ℝ → ℝ}
    (hp : LocallyRiemannPositive f) (hi : IntegrableOn f (Ioi 0)) :
    HasPositiveImproperRiemannIntegral f (∫ x in Ioi 0, f x) := by
  have hl : IntegrableOn f (Ioc 0 1) := hi.mono_set Ioc_subset_Ioi_self
  have hr : IntegrableOn f (Ioi 1) := hi.mono_set (Ioi_subset_Ioi (by norm_num))
  refine ⟨∫ x in Ioc 0 1, f x, ∫ x in Ioi 1, f x, ?_,
    improperRiemannTop_of_integrableOn (fun b hb ↦ hp 1 b (by norm_num) hb) hr, ?_⟩
  · refine ⟨by norm_num, fun c hc hcb ↦ hp c 1 hc hcb, ?_⟩
    have hc := (aecover_Ioc_of_Ioc (μ := volume)
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0))
      (tendsto_const_nhds (x := (1 : ℝ)))).integral_tendsto_of_countably_generated hl
    apply hc.congr'
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with c hc
    simp only [id_eq]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc_left hc.1.le), intervalIntegral.integral_of_le hc.2]
  · have he : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
      ext x
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        by_cases h : x ≤ 1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (lt_of_not_ge h)
    rw [← he]
    apply setIntegral_union
    · exact Set.disjoint_left.mpr fun x hx hy ↦ (not_lt_of_ge hx.2) hy
    · exact measurableSet_Ioi
    · exact hl
    · exact hr

/-- Taking absolute values preserves every proper Riemann integral. -/
theorem LocallyRiemannPositive.abs {f : ℝ → ℝ} (hf : LocallyRiemannPositive f) :
    LocallyRiemannPositive (fun x ↦ |f x|) := by
  intro a b ha hab
  obtain ⟨v, hv⟩ := exists_hasDarbouxRSIntegral_abs hab (hf a b ha hab)
  rw [(intervalIntegrable_and_integral_eq hab hv).2]
  exact hv

/-- A uniform limit with convergent integral values has a literal Riemann
integral. This step uses tagged sums, not a Lebesgue-only conclusion. -/
private theorem properRiemann_uniform_limit {a b M : ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b)
    (hp : ∀ n, HasDarbouxRSIntegral (F n) id a b (∫ x in a..b, F n x))
    (hb : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hu : TendstoUniformlyOn F f atTop (Icc a b))
    (hi : Tendsto (fun n ↦ ∫ x in a..b, F n x) atTop (𝓝 (∫ x in a..b, f x))) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  apply hasDarbouxRSIntegral_of_hasRSIntegral hab
  refine ⟨fun _ _ _ _ h ↦ h, ⟨M, hb⟩, ?_⟩
  intro ε hε
  let δ := ε / (3 * (b - a + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : δ * (b - a) < ε / 3 := by
    have he : δ * (3 * (b - a + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨n, hn, hn'⟩ := ((Metric.tendstoUniformlyOn_iff.mp hu) δ hδ).and
    (Metric.tendsto_nhds.mp hi (ε / 3) (by positivity)) |>.exists
  obtain ⟨p, hp'⟩ := (hasRSIntegral_of_hasDarbouxRSIntegral hab (hp n)).2.2
    (ε / 3) (by positivity)
  refine ⟨p, fun q hq tag ht ↦ ?_⟩
  have hd : |taggedSum q f id tag - taggedSum q (F n) id tag| ≤ δ * (b - a) := by
    have he : taggedSum q (fun x ↦ f x - F n x) id tag =
        taggedSum q f id tag - taggedSum q (F n) id tag := by
      simp only [taggedSum, sub_mul, Finset.sum_sub_distrib]
    rw [← he]
    exact abs_taggedSum_le q (fun _ _ _ _ h ↦ h) (fun x hx ↦ by
      simpa only [Real.dist_eq] using (hn x hx).le) ht
  have hmid := hp' q hq tag ht
  have hend : |(∫ x in a..b, F n x) - ∫ x in a..b, f x| < ε / 3 := by
    simpa only [Real.dist_eq] using hn'
  have htri := abs_add_le (taggedSum q f id tag - taggedSum q (F n) id tag)
    (taggedSum q (F n) id tag - ∫ x in a..b, F n x)
  have htri' := abs_add_le
    ((taggedSum q f id tag - taggedSum q (F n) id tag) +
      (taggedSum q (F n) id tag - ∫ x in a..b, F n x))
    ((∫ x in a..b, F n x) - ∫ x in a..b, f x)
  simp only [sub_add_sub_cancel] at htri htri'
  linarith

/-- The strict-interval formulation in the source implies the local predicate;
no assumption at singleton intervals is needed. -/
theorem locallyRiemannPositive_of_strict {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, 0 < a → a < b → ∃ v, HasDarbouxRSIntegral f id a b v) :
    LocallyRiemannPositive f := by
  intro a b ha hab
  rcases hab.eq_or_lt with he | he
  · subst b
    simpa using hasDarbouxRSIntegral_self f id a
  · obtain ⟨v, hv⟩ := hf a b ha he
    rw [(intervalIntegrable_and_integral_eq hab hv).2]
    exact hv

/-- All measure-theoretic input needed below is derived from the source
Riemann hypotheses. Local uniform convergence proves the Riemann property
of the limit, using `properRiemann_uniform_limit`. -/
theorem exercise12_bridges {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hg : LocallyRiemannPositive g) (hF : ∀ n, LocallyRiemannPositive (F n))
    (hdom : ∀ n x, 0 < x → |F n x| ≤ g x)
    (hu : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 → TendstoUniformlyOn F f atTop K)
    (hgi : ∃ v, HasPositiveImproperRiemannIntegral g v) :
    LocallyRiemannPositive f ∧ (∀ n, IntegrableOn (F n) (Ioi 0)) ∧
      IntegrableOn f (Ioi 0) ∧
      Tendsto (fun n ↦ ∫ x in Ioi 0, F n x) atTop (𝓝 (∫ x in Ioi 0, f x)) := by
  have hp (x : ℝ) (hx : 0 < x) : Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)) :=
    (hu {x} isCompact_singleton (by simpa using hx)).tendsto_at (by simp)
  have hgn (x : ℝ) (hx : 0 < x) : 0 ≤ g x := (abs_nonneg _).trans (hdom 0 x hx)
  have hgb : IntegrableOn g (Ioi 0) :=
    positive_integrable_of_improper_nonneg hgi.choose_spec hgn
  have hm (n : ℕ) := (hF n).aestronglyMeasurable
  have hpae : ∀ᵐ x ∂volume.restrict (Ioi 0), Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hp x hx
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hm hpae
  have hfb (x : ℝ) (hx : 0 < x) : |f x| ≤ g x :=
    le_of_tendsto (hp x hx).abs (Eventually.of_forall fun n ↦ hdom n x hx)
  have hFn (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    hgb.mono' (hm n) ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hdom n x hx)
  have hfi : IntegrableOn f (Ioi 0) :=
    hgb.mono' hfm ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hfb x hx)
  have hlimit := tendsto_integral_of_dominated_convergence g hm hgb
    (fun n ↦ (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hdom n x hx) hpae
  refine ⟨?_, hFn, hfi, hlimit⟩
  intro a b ha hab
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx ↦ ha.trans_le hx.1
  have hsub' : Ioc a b ⊆ Ioi 0 := Ioc_subset_Icc_self.trans hsub
  obtain ⟨M, hM⟩ := (hg a b ha hab).2.1
  apply properRiemann_uniform_limit hab (fun n ↦ hF n a b ha hab)
    (fun x hx ↦ (hfb x (hsub hx)).trans ((le_abs_self _).trans (hM x hx)))
    (hu (Icc a b) isCompact_Icc hsub)
  simp only [intervalIntegral.integral_of_le hab]
  exact tendsto_integral_of_dominated_convergence g
    (fun n ↦ (hFn n |>.mono_set hsub').aestronglyMeasurable) (hgb.mono_set hsub')
    (fun n ↦ (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ by
      simpa only [Real.norm_eq_abs] using hdom n x (hsub' hx))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ hp x (hsub' hx))

/-- R07E12.improper_existence: the functions and their absolute values have
improper Riemann integrals. The limit is locally Riemann integrable. -/
theorem exercise12_improper_existence {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hg : LocallyRiemannPositive g) (hF : ∀ n, LocallyRiemannPositive (F n))
    (hdom : ∀ n x, 0 < x → |F n x| ≤ g x)
    (hu : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 → TendstoUniformlyOn F f atTop K)
    (hgi : ∃ v, HasPositiveImproperRiemannIntegral g v) :
    LocallyRiemannPositive f ∧
    (∀ n, HasPositiveImproperRiemannIntegral (F n) (∫ x in Ioi 0, F n x)) ∧
    HasPositiveImproperRiemannIntegral f (∫ x in Ioi 0, f x) ∧
    (∀ n, HasPositiveImproperRiemannIntegral (fun x ↦ |F n x|) (∫ x in Ioi 0, |F n x|)) ∧
    HasPositiveImproperRiemannIntegral (fun x ↦ |f x|) (∫ x in Ioi 0, |f x|) := by
  obtain ⟨hp, hi, hfi, _⟩ := exercise12_bridges hg hF hdom hu hgi
  exact ⟨hp, fun n ↦ positive_improper_of_integrable (hF n) (hi n),
    positive_improper_of_integrable hp hfi,
    fun n ↦ positive_improper_of_integrable (hF n).abs (hi n).abs,
    positive_improper_of_integrable hp.abs hfi.abs⟩

/-- R07E12.integral_limit: the converging values are actual improper Riemann
integral values. The local hypotheses use the source's strict intervals. -/
theorem exercise12_integral_limit {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hg : ∀ a b : ℝ, 0 < a → a < b → ∃ v, HasDarbouxRSIntegral g id a b v)
    (hF : ∀ n a b, 0 < a → a < b → ∃ v, HasDarbouxRSIntegral (F n) id a b v)
    (hdom : ∀ n x, 0 < x → |F n x| ≤ g x)
    (hu : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 → TendstoUniformlyOn F f atTop K)
    (hgi : ∃ v, HasPositiveImproperRiemannIntegral g v) :
    ∃ (I : ℕ → ℝ) (J : ℝ),
      (∀ n, HasPositiveImproperRiemannIntegral (F n) (I n)) ∧
      HasPositiveImproperRiemannIntegral f J ∧ Tendsto I atTop (𝓝 J) := by
  have hg' := locallyRiemannPositive_of_strict hg
  have hF' := fun n ↦ locallyRiemannPositive_of_strict (hF n)
  have he := exercise12_improper_existence hg' hF' hdom hu hgi
  exact ⟨fun n ↦ ∫ x in Ioi 0, F n x, ∫ x in Ioi 0, f x, he.2.1, he.2.2.1,
    (exercise12_bridges hg' hF' hdom hu hgi).2.2.2⟩

/-- Complex proper integrals use actual complex tagged sums. -/
def LocallyComplexRiemannPositive (f : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b →
    Rudin.Support.StieltjesComplex.HasComplexRSIntegral f id a b (∫ x in a..b, f x)

/-- Complex improper integrability includes proper Riemann witnesses and two
complex endpoint limits. -/
def HasPositiveComplexImproperRiemannIntegral (f : ℝ → ℂ) (v : ℂ) : Prop :=
  LocallyComplexRiemannPositive f ∧ ∃ l r : ℂ,
    Tendsto (fun a ↦ ∫ x in a..1, f x) (𝓝[>] 0) (𝓝 l) ∧
    Tendsto (fun b ↦ ∫ x in 1..b, f x) atTop (𝓝 r) ∧ v = l + r

open Rudin.Support.StieltjesComplex

/-- The real/imaginary reduction produces the actual complex Riemann integral,
including its equality to the interval integral. -/
theorem locallyComplexRiemannPositive_of_components {f : ℝ → ℂ}
    (hr : LocallyRiemannPositive (fun x ↦ (f x).re))
    (hi : LocallyRiemannPositive (fun x ↦ (f x).im)) :
    LocallyComplexRiemannPositive f := by
  intro a b ha hab
  have hr' := (intervalIntegrable_and_integral_eq hab (hr a b ha hab)).1
  have hi' := (intervalIntegrable_and_integral_eq hab (hi a b ha hab)).1
  have hfi : IntegrableOn f (Ioc a b) := Integrable.re_im_iff.mp
    ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hr',
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi'⟩
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · convert hasRSIntegral_of_hasDarbouxRSIntegral hab (hr a b ha hab) using 1
    simp only [intervalIntegral.integral_of_le hab]
    exact (integral_re hfi).symm
  · convert hasRSIntegral_of_hasDarbouxRSIntegral hab (hi a b ha hab) using 1
    simp only [intervalIntegral.integral_of_le hab]
    exact (integral_im hfi).symm

/-- The norm of every locally complex Riemann integrable function is locally
Riemann integrable in the literal real sense. -/
theorem LocallyComplexRiemannPositive.norm {f : ℝ → ℂ}
    (hf : LocallyComplexRiemannPositive f) : LocallyRiemannPositive (fun x ↦ ‖f x‖) := by
  intro a b ha hab
  obtain ⟨v, hv⟩ := exists_norm hab (hf a b ha hab)
  have hd := hasDarbouxRSIntegral_of_hasRSIntegral hab hv
  rw [(intervalIntegrable_and_integral_eq hab hd).2]
  exact hd

/-- The complex bridge retains raw complex endpoint limits and actual tagged
integrals on every positive compact interval. -/
theorem positive_complex_improper_of_integrable {f : ℝ → ℂ}
    (hp : LocallyComplexRiemannPositive f) (hi : IntegrableOn f (Ioi 0)) :
    HasPositiveComplexImproperRiemannIntegral f (∫ x in Ioi 0, f x) := by
  have hl : IntegrableOn f (Ioc 0 1) := hi.mono_set Ioc_subset_Ioi_self
  have hr : IntegrableOn f (Ioi 1) := hi.mono_set (Ioi_subset_Ioi (by norm_num))
  refine ⟨hp, ∫ x in Ioc 0 1, f x, ∫ x in Ioi 1, f x, ?_,
    intervalIntegral_tendsto_integral_Ioi 1 hr tendsto_id, ?_⟩
  · have hc := (aecover_Ioc_of_Ioc (μ := volume)
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0))
      (tendsto_const_nhds (x := (1 : ℝ)))).integral_tendsto_of_countably_generated hl
    apply hc.congr'
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with c hc
    simp only [id_eq]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc_left hc.1.le), intervalIntegral.integral_of_le hc.2]
  · rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hl hr

/-- Full complex-valued source statement. Component reduction proves the
local Riemann property of the limit. All functions have absolutely convergent
improper Riemann integrals, and their complex integral values converge. -/
theorem exercise12_complex {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hg : ∀ a b : ℝ, 0 < a → a < b → ∃ v, HasDarbouxRSIntegral g id a b v)
    (hF : ∀ n a b, 0 < a → a < b → ∃ z, HasComplexRSIntegral (F n) id a b z)
    (hdom : ∀ n x, 0 < x → ‖F n x‖ ≤ g x)
    (hu : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 → TendstoUniformlyOn F f atTop K)
    (hgi : ∃ v, HasPositiveImproperRiemannIntegral g v) :
    LocallyComplexRiemannPositive f ∧
    (∀ n, HasPositiveComplexImproperRiemannIntegral (F n) (∫ x in Ioi 0, F n x)) ∧
    HasPositiveComplexImproperRiemannIntegral f (∫ x in Ioi 0, f x) ∧
    (∀ n, HasPositiveImproperRiemannIntegral (fun x ↦ ‖F n x‖) (∫ x in Ioi 0, ‖F n x‖)) ∧
    HasPositiveImproperRiemannIntegral (fun x ↦ ‖f x‖) (∫ x in Ioi 0, ‖f x‖) ∧
    Tendsto (fun n ↦ ∫ x in Ioi 0, F n x) atTop (𝓝 (∫ x in Ioi 0, f x)) := by
  have hg' := locallyRiemannPositive_of_strict hg
  have hFr (n : ℕ) : LocallyRiemannPositive (fun x ↦ (F n x).re) := by
    apply locallyRiemannPositive_of_strict
    intro a b ha hab
    obtain ⟨z, hz⟩ := hF n a b ha hab
    exact ⟨z.re, hasDarbouxRSIntegral_of_hasRSIntegral hab.le
      (hasComplexRSIntegral_iff.mp hz).1⟩
  have hFi (n : ℕ) : LocallyRiemannPositive (fun x ↦ (F n x).im) := by
    apply locallyRiemannPositive_of_strict
    intro a b ha hab
    obtain ⟨z, hz⟩ := hF n a b ha hab
    exact ⟨z.im, hasDarbouxRSIntegral_of_hasRSIntegral hab.le
      (hasComplexRSIntegral_iff.mp hz).2⟩
  have hr := exercise12_bridges hg' hFr
    (fun n x hx ↦ (Complex.abs_re_le_norm _).trans (hdom n x hx))
    (fun K hK hs ↦ Complex.reCLM.uniformContinuous.comp_tendstoUniformlyOn (hu K hK hs)) hgi
  have hi := exercise12_bridges hg' hFi
    (fun n x hx ↦ (Complex.abs_im_le_norm _).trans (hdom n x hx))
    (fun K hK hs ↦ Complex.imCLM.uniformContinuous.comp_tendstoUniformlyOn (hu K hK hs)) hgi
  have hFp (n : ℕ) := locallyComplexRiemannPositive_of_components (hFr n) (hFi n)
  have hfp := locallyComplexRiemannPositive_of_components hr.1 hi.1
  have hFn (n : ℕ) : IntegrableOn (F n) (Ioi 0) :=
    Integrable.re_im_iff.mp ⟨hr.2.1 n, hi.2.1 n⟩
  have hfi : IntegrableOn f (Ioi 0) := Integrable.re_im_iff.mp ⟨hr.2.2.1, hi.2.2.1⟩
  refine ⟨hfp, fun n ↦ positive_complex_improper_of_integrable (hFp n) (hFn n),
    positive_complex_improper_of_integrable hfp hfi,
    fun n ↦ positive_improper_of_integrable (hFp n).norm (hFn n).norm,
    positive_improper_of_integrable hfp.norm hfi.norm, ?_⟩
  have hgb : IntegrableOn g (Ioi 0) := positive_integrable_of_improper_nonneg hgi.choose_spec
    (fun x hx ↦ (norm_nonneg _).trans (hdom 0 x hx))
  apply tendsto_integral_of_dominated_convergence g (fun n ↦ (hFn n).aestronglyMeasurable) hgb
    (fun n ↦ (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hdom n x hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (hu {x} isCompact_singleton (by simpa using hx)).tendsto_at (by simp)

end Rudin.Chapter07
