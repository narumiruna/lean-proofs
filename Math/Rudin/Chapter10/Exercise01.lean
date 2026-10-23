module

public import Math.Rudin.Support.MultivariateRiemann
public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComplex
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Chapter 10, Exercise 1

Source: book page 288 / primary PDF page 297; Definitions 10.1–10.3 and
Example 10.4, book pages 245–248 / PDF pages 254–257.

The zero extension is the literal indicator of the closed convex set. Convex
frontiers in every affine parameter space have measure zero. This proves
regularity for all sections, including empty and lower-dimensional sections.
Integration preserves that regularity, so induction supplies every source
Darboux stage at every parameter. Complex stages use actual complex tagged sums.

Order independence follows from bounded continuous approximants supported in H,
their source-value limits, and the continuous-box order theorem. Approximation
is not uniform at nonzero boundary values. The measure comparison is proved
after source existence. The Euclidean conclusions are stronger than the source:
they do not require nonempty interior and also cover dimension zero.

Inventory mappings:
* `R10E01.existence`: `existence_real`, `existence_complex`.
* `R10E01.order_independence`: `order_independence_real`, `order_independence_complex`.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise01

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
open Rudin.Support Rudin.Support.MultivariateRiemann

/-- Bounded measurable functions whose restrictions to every finite-dimensional
real affine parameter space are continuous almost everywhere in that space.
This condition will be derived from convexity, not assumed in the exercise. -/
def AffineRegular {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [NormedAddCommGroup E] [MeasurableSpace E] (f : V → E) : Prop :=
  (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) ∧ Measurable f ∧
    ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
      [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
      (μ : Measure W) [IsAddHaarMeasure μ] (L : W →ᵃ[ℝ] V),
      ∀ᵐ x ∂μ, ContinuousAt (f ∘ L) x

section Regular
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
/-- The frontier is taken in the parameter space. This includes empty and
lower-dimensional affine sections, not just generic sections. -/
theorem convex_indicator_affineRegular {H : Set V} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : V → E} (hf : ContinuousOn f H) :
    AffineRegular (H.indicator f) := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf
  classical
  refine ⟨⟨max M 0, ?_⟩,
    hf.measurable_piecewise continuousOn_const hH.measurableSet, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · simpa only [indicator_of_mem hx] using (hM x hx).trans (le_max_left M 0)
    · simp only [indicator_of_notMem hx, norm_zero]
      exact le_max_right M 0
  · intro W _ _ _ _ _ μ _ L
    have hclosed : IsClosed (L ⁻¹' H) := hH.isClosed.preimage L.continuous_of_finiteDimensional
    have hc : Convex ℝ (L ⁻¹' H) := Convex.affine_preimage L hconv
    have hn : ∀ᵐ x ∂μ, x ∉ frontier (L ⁻¹' H) := by
      rw [ae_iff]
      simpa using hc.addHaar_frontier μ
    filter_upwards [hn] with x hx
    by_cases hm : L x ∈ H
    · have hi : x ∈ interior (L ⁻¹' H) := (mem_interior_iff_notMem_frontier (show x ∈ L ⁻¹' H from hm)).mpr hx
      have hfL : ContinuousOn (f ∘ L) (L ⁻¹' H) :=
        hf.comp L.continuous_of_finiteDimensional.continuousOn (fun _ h => h)
      apply (hfL.continuousAt (mem_interior_iff_mem_nhds.mp hi)).congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds hi] with y hy
      exact indicator_of_mem (show L y ∈ H from @interior_subset W _ (L ⁻¹' H) y hy) f
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [hclosed.isOpen_compl.mem_nhds hm] with y hy
      exact indicator_of_notMem (show L y ∉ H from hy) f

/-- Insert a scalar as the first coordinate, retaining the remaining affine
parameters exactly. -/
def consAffine {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (L : W →ᵃ[ℝ] (Fin n → ℝ)) : W × ℝ →ᵃ[ℝ] (Fin (n+1) → ℝ) :=
  AffineMap.pi (Fin.cons AffineMap.snd (fun i =>
    ((LinearMap.proj i).toAffineMap.comp L).comp AffineMap.fst))

@[simp] theorem consAffine_apply {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (L : W →ᵃ[ℝ] (Fin n → ℝ)) (x : W) (t : ℝ) :
    consAffine L (x,t) = Fin.cons t (L x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Integration preserves affine-section regularity. Fubini is used on the set
of continuity points; dominated convergence then proves continuity of the actual
marginal. No source-integrability hypothesis is used here. -/
theorem AffineRegular.marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → E}
    (hf : AffineRegular f) (a b : ℝ) :
    AffineRegular (fun x : Fin n → ℝ => ∫ t in a..b, f (Fin.cons t x)) := by
  obtain ⟨⟨M, hM⟩, hm, hc⟩ := hf
  refine ⟨⟨M * |b-a|, ?_⟩, ?_, ?_⟩
  · intro x
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hM (Fin.cons t x))
  · have hs := (hm.comp (show Measurable (fun p : (Fin n → ℝ) × ℝ =>
      Fin.cons p.2 p.1) from (by fun_prop))).stronglyMeasurable
    exact (hs.integral_prod_right' (ν := volume.restrict (Ioc a b))).measurable.sub
      (hs.integral_prod_right' (ν := volume.restrict (Ioc b a))).measurable
  · intro W _ _ _ _ _ μ _ L
    have h := hc (W × ℝ) (μ.prod volume) (consAffine L)
    have hh := Measure.ae_ae_of_ae_prod h
    filter_upwards [hh] with x hx
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
    · exact Eventually.of_forall fun y =>
        (hm.comp (show Measurable (fun t => Fin.cons t (L y)) from
          (by fun_prop))).aestronglyMeasurable
    · exact Eventually.of_forall fun y => Eventually.of_forall fun t _ => hM _
    · exact intervalIntegrable_const
    · filter_upwards [hx] with t ht _
      have hct := ht.comp (x := x) (continuous_id.prodMk continuous_const).continuousAt
      simpa only [Function.comp_def, consAffine_apply, id_eq] using hct

omit [BorelSpace V] [NormedSpace ℝ E] in
/-- All finite-measure restrictions are integrable by the proved global bound. -/
theorem AffineRegular.integrable {f : V → E} (hf : AffineRegular f)
    (μ : Measure V) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨⟨M, hM⟩, hm, _⟩ := hf
  exact ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Eventually.of_forall hM)⟩

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- Affine changes of coordinates retain all affine-section facts. -/
theorem AffineRegular.comp {f : V → E} (hf : AffineRegular f)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (L : W →ᵃ[ℝ] V) :
    AffineRegular (f ∘ L) := by
  refine ⟨hf.1.imp (fun M hM x => hM (L x)),
    hf.2.1.comp L.continuous_of_finiteDimensional.measurable, ?_⟩
  intro X _ _ _ _ _ μ _ T
  exact hf.2.2 X μ (L.comp T)

omit [BorelSpace V] [SecondCountableTopology E] in
/-- Continuous real-linear maps preserve the derived regularity. -/
theorem AffineRegular.clm {f : V → E} (hf : AffineRegular f)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (T : E →L[ℝ] F) : AffineRegular (T ∘ f) := by
  obtain ⟨M, hM⟩ := hf.1
  refine ⟨⟨‖T‖ * M, fun x => (T.le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg T))⟩,
    T.continuous.measurable.comp hf.2.1, ?_⟩
  intro W _ _ _ _ _ μ _ L
  filter_upwards [hf.2.2 W μ L] with x hx
  exact T.continuous.continuousAt.comp hx

end Regular

/-- A fixed coordinate row is an affine map, including boundary rows. -/
def rowAffine {n : ℕ} (x : Fin n → ℝ) : ℝ →ᵃ[ℝ] (Fin (n+1) → ℝ) :=
  AffineMap.pi (Fin.cons (AffineMap.id ℝ ℝ) (fun i => AffineMap.const ℝ ℝ (x i)))

@[simp] theorem rowAffine_apply {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    rowAffine x t = Fin.cons t x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Every row has a literal Darboux integral, not merely almost every row. -/
theorem AffineRegular.row_source {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : AffineRegular f) {a b : ℝ} (hab : a ≤ b) (x : Fin n → ℝ) :
    StieltjesPrototype.HasDarbouxRSIntegral (fun t => f (Fin.cons t x)) id a b
      (∫ t in a..b, f (Fin.cons t x)) := by
  obtain ⟨M, hM⟩ := hf.1
  apply RiemannIntegrability.hasDarbouxRSIntegral_of_ae_continuousWithinAt hab
    (M := M) (fun t _ => by simpa only [Real.norm_eq_abs] using hM (Fin.cons t x))
  have h := hf.2.2 ℝ volume (rowAffine x)
  filter_upwards [ae_restrict_of_ae h] with t ht
  simpa only [Function.comp_def, rowAffine_apply] using ht.continuousWithinAt (s := Icc a b)

/-- Source existence follows by induction, since actual integration preserves
regularity. No row or marginal integrability is an input. -/
theorem AffineRegular.source {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) :
    HasSourceIntegral n a b f (iterated n a b f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ⟨fun x _ => hf.row_source (hab 0) x,
      ih (hf.marginal (a 0) (b 0)) (fun i => hab i.succ)⟩

/-- The source repeated value equals the measure integral only after all-point
source existence and boundedness have been proved. -/
theorem AffineRegular.integral_eq_iterated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) :
    (∫ x in Icc a b, f x) = iterated n a b f := by
  induction n with
  | zero =>
    have hs : Icc a b = (univ : Set (Fin 0 → ℝ)) := by ext x; simp
    simp [hs, iterated, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
    have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
      isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
    rw [split_box_integral (hf.integrable (volume.restrict (Icc a b)))]
    simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab 0)]
    exact ih (hf.marginal (a 0) (b 0)) (fun i => hab i.succ)

/-- A continuous cutoff that vanishes on the complement and on the frontier.
The ENNReal distance convention also handles the zero-dimensional full set. -/
def cutoff {V : Type*} [PseudoEMetricSpace V] (H : Set V) (j : ℕ) (x : V) : ℝ :=
  1 - (thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) Hᶜ x : ℝ)

theorem cutoff_continuous {V : Type*} [PseudoEMetricSpace V] (H : Set V) (j : ℕ) :
    Continuous (cutoff H j) := by
  exact continuous_const.sub (NNReal.continuous_coe.comp
    (thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) Hᶜ).continuous)

theorem cutoff_bounds {V : Type*} [PseudoEMetricSpace V] (H : Set V) (j : ℕ) (x : V) :
    0 ≤ cutoff H j x ∧ cutoff H j x ≤ 1 := by
  have h := thickenedIndicator_le_one (show 0 < 1 / ((j : ℝ) + 1) by positivity) Hᶜ x
  have h' : (thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) Hᶜ x : ℝ) ≤ 1 := h
  have hn := (thickenedIndicator (show 0 < 1 / ((j : ℝ) + 1) by positivity) Hᶜ x).coe_nonneg
  dsimp [cutoff]
  constructor <;> linarith

theorem cutoff_zero {V : Type*} [PseudoEMetricSpace V] {H : Set V} {x : V}
    (hx : x ∉ H) (j : ℕ) : cutoff H j x = 0 := by
  simp [cutoff, thickenedIndicator_one _ Hᶜ hx]

/-- These are actual continuous functions, with topological support in H. -/
theorem approximation_support {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsClosed H)
    (g : (Fin n → ℝ) → ℝ) (j : ℕ) :
    tsupport (fun x => cutoff H j x * g x) ⊆ H := by
  apply closure_minimal _ hH
  intro x hx
  by_contra hn
  exact hx (by simp [cutoff_zero hn j])

/-- The approximants retain a common bound, including outside H. -/
theorem approximation_bound {n : ℕ} {H : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hg : ∀ x ∈ H, ‖g x‖ ≤ M) (j : ℕ) (x : Fin n → ℝ) :
    ‖cutoff H j x * g x‖ ≤ M := by
  by_cases hx : x ∈ H
  · rw [norm_mul, Real.norm_of_nonneg (cutoff_bounds H j x).1]
    exact (mul_le_mul_of_nonneg_right (cutoff_bounds H j x).2 (norm_nonneg _)).trans
      (by simpa using hg x hx)
  · simp only [cutoff_zero hx, zero_mul, norm_zero]
    exact hM

/-- Approximation is pointwise off the null convex frontier. Boundary values
are not changed in the target function. -/
theorem approximation_tendsto {n : ℕ} {H : Set (Fin n → ℝ)} (hconv : Convex ℝ H)
    (g : (Fin n → ℝ) → ℝ) :
    ∀ᵐ x ∂volume, Tendsto (fun j => cutoff H j x * g x) atTop (𝓝 (H.indicator g x)) := by
  have hn : ∀ᵐ x : Fin n → ℝ ∂volume, x ∉ frontier H := by
    rw [ae_iff]
    simpa using hconv.addHaar_frontier volume
  have ht := thickenedIndicator_tendsto_indicator_closure
    (fun j : ℕ => show 0 < 1 / ((j : ℝ) + 1) by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat Hᶜ
  rw [tendsto_pi_nhds] at ht
  filter_upwards [hn] with x hx
  by_cases hm : x ∈ H
  · have hi : x ∈ interior H := (mem_interior_iff_notMem_frontier hm).mpr hx
    have hnc : x ∉ closure Hᶜ := by simpa only [closure_compl, mem_compl_iff, not_not] using hi
    have ht' := NNReal.continuous_coe.continuousAt.tendsto.comp (ht x)
    simp only [indicator_of_notMem hnc, NNReal.coe_zero] at ht'
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub ht').mul (tendsto_const_nhds (x := g x))
    simpa only [cutoff, sub_zero, one_mul, indicator_of_mem hm, Function.comp_def] using hh
  · simp only [cutoff_zero hm, zero_mul, indicator_of_notMem hm]
    exact tendsto_const_nhds

/-- Convergence of continuous approximants transfers to each actual source
repeated value, after the all-point source/measure comparison. -/
theorem approximation_source_limit {n : ℕ} {a b : Fin n → ℝ} (hab : a ≤ b)
    {f : (Fin n → ℝ) → ℝ} (hf : AffineRegular f)
    {g : ℕ → (Fin n → ℝ) → ℝ} (hg : ∀ j, Continuous (g j))
    {M : ℝ} (hM : ∀ j x, ‖g j x‖ ≤ M)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun j => g j x) atTop (𝓝 (f x)))
    (σ : Equiv.Perm (Fin n)) :
    Tendsto (fun j => iterated n (a ∘ σ) (b ∘ σ) (g j ∘ coordinatePermutation σ))
      atTop (𝓝 (iterated n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ))) := by
  have hreg := hf.comp (coordinatePermutation σ).toAffineEquiv.toAffineMap
  have : IsFiniteMeasure (volume.restrict (Icc (a ∘ σ) (b ∘ σ))) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
  have hl := (permutation_volume σ).quasiMeasurePreserving.ae hlim
  have h := tendsto_integral_of_dominated_convergence (fun _ => M)
    (μ := volume.restrict (Icc (a ∘ σ) (b ∘ σ)))
    (fun j => ((hg j).comp (coordinatePermutation σ).continuous).aestronglyMeasurable)
    (integrable_const M) (fun j => Eventually.of_forall (fun x => hM j _))
    (ae_restrict_of_ae hl)
  have he (j) := box_integral_eq_iterated (fun i => hab (σ i))
    ((hg j).comp (coordinatePermutation σ).continuous).continuousOn
  have he' : (∫ x in Icc (a ∘ σ) (b ∘ σ), f (coordinatePermutation σ x)) =
      iterated n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ) :=
    hreg.integral_eq_iterated (fun i => hab (σ i))
  rw [he'] at h
  convert h using 1
  funext j
  exact (he j).symm

/-- Every coordinate order exists for the literal zero extension of an
arbitrary compact convex set. Empty and lower-dimensional sets are included. -/
theorem real_existence {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ)
      (iterated n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ)) :=
  ((convex_indicator_affineRegular hH hconv hf).comp
    (coordinatePermutation σ).toAffineEquiv.toAffineMap).source (fun i => hab (σ i))

/-- A single bounded sequence of continuous, H-supported functions approximates
the literal zero extension off its null frontier. No uniform convergence at
nonzero boundary values is asserted. -/
theorem continuous_approximations {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f H) :
    ∃ (G : ℕ → (Fin n → ℝ) → ℝ) (M : ℝ),
      (∀ j, Continuous (G j) ∧ tsupport (G j) ⊆ H) ∧
      (∀ j x, ‖G j x‖ ≤ M) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => G j x) atTop (𝓝 (H.indicator f x)) := by
  obtain ⟨g, hg, he⟩ := continuous_extension hH.isClosed hf
  have hz : H.indicator g = H.indicator f := indicator_congr he
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨fun j x => cutoff H j x * g x, max M 0,
    fun j => ⟨(cutoff_continuous H j).mul hg, approximation_support hH.isClosed g j⟩,
    approximation_bound (le_max_right M 0)
      (fun x hx => (hM x hx).trans (le_max_left M 0)), ?_⟩
  exact hz ▸ approximation_tendsto hconv g

/-- Order independence is obtained from the common continuous approximants.
Their supports lie in H; no vanishing assumption is imposed on f at the boundary. -/
theorem real_order_independence {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ τ : Equiv.Perm (Fin n)) :
    iterated n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ) =
      iterated n (a ∘ τ) (b ∘ τ) (H.indicator f ∘ coordinatePermutation τ) := by
  obtain ⟨G, M, hG, hbound, hlim⟩ := continuous_approximations hH hconv hf
  have hreg := convex_indicator_affineRegular hH hconv hf
  have hs := approximation_source_limit hab hreg (fun j => (hG j).1) hbound hlim σ
  have ht := approximation_source_limit hab hreg (fun j => (hG j).1) hbound hlim τ
  have heq (j) : iterated n (a ∘ σ) (b ∘ σ) (G j ∘ coordinatePermutation σ) =
      iterated n (a ∘ τ) (b ∘ τ) (G j ∘ coordinatePermutation τ) :=
    (box_source_all_orders hab (hG j).1.continuousOn σ).2.trans
      (box_source_all_orders hab (hG j).1.continuousOn τ).2.symm
  simp_rw [heq] at hs
  exact tendsto_nhds_unique hs ht

/-- The real approximation sequences combine to actual continuous complex
approximants with support in H and a common norm bound. -/
theorem continuous_approximations_complex {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f H) :
    ∃ (F : ℕ → (Fin n → ℝ) → ℂ) (M : ℝ),
      (∀ j, Continuous (F j) ∧ tsupport (F j) ⊆ H) ∧
      (∀ j x, ‖F j x‖ ≤ M) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => F j x) atTop (𝓝 (H.indicator f x)) := by
  obtain ⟨G, A, hG, hA, hlimG⟩ := continuous_approximations hH hconv
    (Complex.continuous_re.comp_continuousOn hf)
  obtain ⟨J, B, hJ, hB, hlimJ⟩ := continuous_approximations hH hconv
    (Complex.continuous_im.comp_continuousOn hf)
  let F (j : ℕ) (x : Fin n → ℝ) : ℂ := (G j x : ℂ) + (J j x : ℂ) * Complex.I
  refine ⟨F, A + B, ?_, ?_, ?_⟩
  · intro j
    constructor
    · exact (Complex.continuous_ofReal.comp (hG j).1).add
        ((Complex.continuous_ofReal.comp (hJ j).1).mul continuous_const)
    · apply closure_minimal _ hH.isClosed
      intro x hx
      by_contra hn
      have hg : G j x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn ((hG j).2 h))
      have hj : J j x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn ((hJ j).2 h))
      exact hx (by simp [F, hg, hj])
  · intro j x
    have h := (norm_add_le (G j x : ℂ) ((J j x : ℂ) * Complex.I))
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real] at h
    exact h.trans (add_le_add (hA j x) (hB j x))
  · filter_upwards [hlimG, hlimJ] with x hx hy
    have hh := ((Complex.continuous_ofReal.tendsto _).comp hx).add
      (((Complex.continuous_ofReal.tendsto _).comp hy).mul_const Complex.I)
    have he : ((H.indicator (fun x => (f x).re) x : ℝ) : ℂ) +
        ((H.indicator (fun x => (f x).im) x : ℝ) : ℂ) * Complex.I = H.indicator f x := by
      by_cases hm : x ∈ H <;> simp [hm]
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh

/-- Actual repeated complex integration, eliminating coordinate zero first. -/
def complexIterated (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℂ) → ℂ :=
  Nat.rec (motive := fun n => (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℂ) → ℂ)
    (fun _ _ f => f 0)
    (fun _ ih a b f => ih (fun i => a i.succ) (fun i => b i.succ)
      (fun x => ∫ t in a 0..b 0, f (Fin.cons t x))) n

/-- Every complex stage has literal complex tagged-sum convergence, at every
remaining parameter. This is not a predicate on equivalence classes. -/
def HasComplexSourceIntegral (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) →
    ((Fin n → ℝ) → ℂ) → ℂ → Prop :=
  Nat.rec (motive := fun n => (Fin n → ℝ) → (Fin n → ℝ) →
      ((Fin n → ℝ) → ℂ) → ℂ → Prop)
    (fun _ _ f v => f 0 = v)
    (fun _ ih a b f v =>
      (∀ x ∈ Icc (fun i => a i.succ) (fun i => b i.succ),
        StieltjesComplex.HasComplexRSIntegral (fun t => f (Fin.cons t x)) id
          (a 0) (b 0) (∫ t in a 0..b 0, f (Fin.cons t x))) ∧
      ih (fun i => a i.succ) (fun i => b i.succ)
        (fun x => ∫ t in a 0..b 0, f (Fin.cons t x)) v) n

theorem AffineRegular.complex_row_integrable {n : ℕ} {f : (Fin (n+1) → ℝ) → ℂ}
    (hf : AffineRegular f) (a b : ℝ) (x : Fin n → ℝ) :
    IntervalIntegrable (fun t => f (Fin.cons t x)) volume a b := by
  have hr := hf.comp (rowAffine x)
  constructor
  · simpa only [Function.comp_def, rowAffine_apply, IntegrableOn] using
      hr.integrable (volume.restrict (Ioc a b))
  · simpa only [Function.comp_def, rowAffine_apply, IntegrableOn] using
      hr.integrable (volume.restrict (Ioc b a))

/-- The complex source bridge is the proved tagged-sum component equivalence. -/
theorem AffineRegular.complex_row_source {n : ℕ} {f : (Fin (n+1) → ℝ) → ℂ}
    (hf : AffineRegular f) {a b : ℝ} (hab : a ≤ b) (x : Fin n → ℝ) :
    StieltjesComplex.HasComplexRSIntegral (fun t => f (Fin.cons t x)) id a b
      (∫ t in a..b, f (Fin.cons t x)) := by
  have hi := hf.complex_row_integrable a b x
  apply StieltjesComplex.hasComplexRSIntegral_iff.mpr
  constructor
  · change StieltjesPrototype.HasRSIntegral (fun t => (f (Fin.cons t x)).re) id a b _
    have he := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t in a..b, (f (Fin.cons t x)).re) = (∫ t in a..b, f (Fin.cons t x)).re at he
    rw [← he]
    exact StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral hab
      ((hf.clm Complex.reCLM).row_source hab x)
  · change StieltjesPrototype.HasRSIntegral (fun t => (f (Fin.cons t x)).im) id a b _
    have he := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t in a..b, (f (Fin.cons t x)).im) = (∫ t in a..b, f (Fin.cons t x)).im at he
    rw [← he]
    exact StieltjesRefinement.hasRSIntegral_of_hasDarbouxRSIntegral hab
      ((hf.clm Complex.imCLM).row_source hab x)

theorem AffineRegular.complex_source {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) :
    HasComplexSourceIntegral n a b f (complexIterated n a b f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ⟨fun x _ => hf.complex_row_source (hab 0) x,
      ih (hf.marginal (a 0) (b 0)) (fun i => hab i.succ)⟩

/-- Component reduction commutes with actual integration because every complex
row is integrable. It is not an assumption about component integrals. -/
theorem AffineRegular.complex_component {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : AffineRegular f) (a b : Fin n → ℝ) (T : ℂ →L[ℝ] ℝ) :
    iterated n a b (T ∘ f) = T (complexIterated n a b f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change iterated n (fun i => a i.succ) (fun i => b i.succ)
      (fun x => ∫ t in a 0..b 0, T (f (Fin.cons t x))) = _
    have he : (fun x => ∫ t in a 0..b 0, T (f (Fin.cons t x))) =
        T ∘ (fun x => ∫ t in a 0..b 0, f (Fin.cons t x)) := by
      funext x
      exact T.intervalIntegral_comp_comm (hf.complex_row_integrable _ _ x)
    rw [he]
    exact ih (hf.marginal (a 0) (b 0)) _ _

/-- Literal complex source existence in every coordinate order. -/
theorem complex_existence {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ : Equiv.Perm (Fin n)) :
    HasComplexSourceIntegral n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ)
      (complexIterated n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ)) :=
  ((convex_indicator_affineRegular hH hconv hf).comp
    (coordinatePermutation σ).toAffineEquiv.toAffineMap).complex_source (fun i => hab (σ i))

/-- Complex order independence reduces to the two proved real approximation
arguments, with literal complex stages certified separately. -/
theorem complex_order_independence {n : ℕ} {H : Set (Fin n → ℝ)} (hH : IsCompact H)
    (hconv : Convex ℝ H) {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ τ : Equiv.Perm (Fin n)) :
    complexIterated n (a ∘ σ) (b ∘ σ) (H.indicator f ∘ coordinatePermutation σ) =
      complexIterated n (a ∘ τ) (b ∘ τ) (H.indicator f ∘ coordinatePermutation τ) := by
  have hreg (ρ) : AffineRegular (H.indicator f ∘ coordinatePermutation ρ) :=
    (convex_indicator_affineRegular hH hconv hf).comp
      (coordinatePermutation ρ).toAffineEquiv.toAffineMap
  have he (T : ℂ →L[ℝ] ℝ) (ρ : Equiv.Perm (Fin n)) :
      T ∘ (H.indicator f ∘ coordinatePermutation ρ) =
        H.indicator (T ∘ f) ∘ coordinatePermutation ρ := by
    ext x
    by_cases hx : coordinatePermutation ρ x ∈ H <;> simp [Function.comp_def, hx]
  apply Complex.ext
  · change Complex.reCLM (complexIterated n (a ∘ σ) (b ∘ σ) _) =
      Complex.reCLM (complexIterated n (a ∘ τ) (b ∘ τ) _)
    rw [← (hreg σ).complex_component _ _ Complex.reCLM,
      ← (hreg τ).complex_component _ _ Complex.reCLM, he, he]
    exact real_order_independence hH hconv (Complex.continuous_re.comp_continuousOn hf) hab σ τ
  · change Complex.imCLM (complexIterated n (a ∘ σ) (b ∘ σ) _) =
      Complex.imCLM (complexIterated n (a ∘ τ) (b ∘ τ) _)
    rw [← (hreg σ).complex_component _ _ Complex.imCLM,
      ← (hreg τ).complex_component _ _ Complex.imCLM, he, he]
    exact real_order_independence hH hconv (Complex.continuous_im.comp_continuousOn hf) hab σ τ

/-- Complex measure comparison follows from the proved component identities. -/
theorem AffineRegular.complex_integral_eq_iterated {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) :
    (∫ x in Icc a b, f x) = complexIterated n a b f := by
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
  have hi := hf.integrable (volume.restrict (Icc a b))
  have he (T : ℂ →L[ℝ] ℝ) : T (∫ x in Icc a b, f x) = T (complexIterated n a b f) :=
    (T.integral_comp_comm hi).symm.trans
      (((hf.clm T).integral_eq_iterated hab).trans (hf.complex_component a b T))
  exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)

/-- The common source value is identified using the actual coordinate-volume
transport, after all source stages have been established. -/
theorem AffineRegular.source_value {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) (σ : Equiv.Perm (Fin n)) :
    HasSourceIntegral n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ)
      (∫ x in Icc a b, f x) := by
  have hr : AffineRegular (f ∘ coordinatePermutation σ) :=
    hf.comp (coordinatePermutation σ).toAffineEquiv.toAffineMap
  have he := (permutation_volume σ).setIntegral_preimage_emb
    (coordinatePermutation σ).toHomeomorph.measurableEmbedding f (Icc a b)
  rw [permutation_preimage_box] at he
  have hv : iterated n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ) =
      ∫ x in Icc a b, f x :=
    (hr.integral_eq_iterated (a := a ∘ σ) (b := b ∘ σ) (fun i => hab (σ i))).symm.trans he
  exact hv ▸ hr.source (fun i => hab (σ i))

theorem AffineRegular.complex_source_value {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : AffineRegular f) {a b : Fin n → ℝ} (hab : a ≤ b) (σ : Equiv.Perm (Fin n)) :
    HasComplexSourceIntegral n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ)
      (∫ x in Icc a b, f x) := by
  have hr : AffineRegular (f ∘ coordinatePermutation σ) :=
    hf.comp (coordinatePermutation σ).toAffineEquiv.toAffineMap
  have he := (permutation_volume σ).setIntegral_preimage_emb
    (coordinatePermutation σ).toHomeomorph.measurableEmbedding f (Icc a b)
  rw [permutation_preimage_box] at he
  have hv : complexIterated n (a ∘ σ) (b ∘ σ) (f ∘ coordinatePermutation σ) =
      ∫ x in Icc a b, f x :=
    (hr.complex_integral_eq_iterated (a := a ∘ σ) (b := b ∘ σ)
      (fun i => hab (σ i))).symm.trans he
  exact hv ▸ hr.complex_source (fun i => hab (σ i))

/-- Compactness supplies an actual enclosing cell with strictly ordered bounds. -/
theorem enclosing_cell {n : ℕ} {H : Set (EuclideanSpace ℝ (Fin n))} (hH : IsCompact H) :
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      H ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn e.continuous.continuousOn
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  refine ⟨fun _ => -B, fun _ => B, fun _ => by linarith, ?_⟩
  intro x hx
  have h (i : Fin n) : |e x i| ≤ B := by
    exact (norm_le_pi_norm (e x) i).trans ((hM x hx).trans (by dsimp [B]; linarith [le_max_left M 0]))
  exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

/-- Literal zero extension in product coordinates, with no change at the
boundary. The formula applies equally to real and complex values. -/
theorem zeroExtension_coordinates {n : ℕ} {E : Type*} [Zero E]
    (H : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → E) :
    H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm =
      ((EuclideanSpace.equiv (Fin n) ℝ).symm ⁻¹' H).indicator
        (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) := by
  ext x
  exact indicator_comp_right _

/-- Coordinate measure comparison on any enclosing cell. -/
theorem zeroExtension_integral_coordinates {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Set (EuclideanSpace ℝ (Fin n))} (hH : IsCompact H)
    (f : EuclideanSpace ℝ (Fin n) → E) {a b : Fin n → ℝ}
    (hbox : H ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b) :
    (∫ x in Icc a b, H.indicator f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) =
      ∫ u in H, f u := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have he := (coordinates_volume n).setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (H.indicator f ∘ e.symm) (Icc a b)
  change (∫ x in e ⁻¹' Icc a b, H.indicator f (e.symm (e x))) = _ at he
  simp only [e.symm_apply_apply] at he
  calc
    _ = ∫ x in e ⁻¹' Icc a b, H.indicator f x := he.symm
    _ = _ := by rw [setIntegral_indicator hH.measurableSet, inter_eq_right.mpr hbox]

/-- R10E01.existence, real case. The hypotheses in the book are sufficient;
the proof also covers empty and lower-dimensional H. Every raw Darboux stage
exists for every parameter, in every coordinate order. -/
theorem existence_real {n : ℕ} {H : Set (EuclideanSpace ℝ (Fin n))}
    (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f H) :
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      H ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b ∧
      IntegrableOn f H ∧ ∀ σ : Equiv.Perm (Fin n),
      HasSourceIntegral n (a ∘ σ) (b ∘ σ)
        (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation σ)
        (∫ u in H, f u) := by
  obtain ⟨a, b, hab, hbox⟩ := enclosing_cell hH
  refine ⟨a, b, hab, hbox, hf.integrableOn_compact hH, fun σ => ?_⟩
  have hreg : AffineRegular (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) :=
    (convex_indicator_affineRegular hH hconv hf).comp
      (EuclideanSpace.equiv (Fin n) ℝ).symm.toAffineEquiv.toAffineMap
  rw [← zeroExtension_integral_coordinates hH f hbox]
  exact hreg.source_value (fun i => (hab i).le) σ

/-- R10E01.existence, complex case, with actual complex tagged-sum witnesses. -/
theorem existence_complex {n : ℕ} {H : Set (EuclideanSpace ℝ (Fin n))}
    (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContinuousOn f H) :
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      H ⊆ (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' Icc a b ∧
      IntegrableOn f H ∧ ∀ σ : Equiv.Perm (Fin n),
      HasComplexSourceIntegral n (a ∘ σ) (b ∘ σ)
        (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation σ)
        (∫ u in H, f u) := by
  obtain ⟨a, b, hab, hbox⟩ := enclosing_cell hH
  refine ⟨a, b, hab, hbox, hf.integrableOn_compact hH, fun σ => ?_⟩
  have hreg : AffineRegular (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) :=
    (convex_indicator_affineRegular hH hconv hf).comp
      (EuclideanSpace.equiv (Fin n) ℝ).symm.toAffineEquiv.toAffineMap
  rw [← zeroExtension_integral_coordinates hH f hbox]
  exact hreg.complex_source_value (fun i => (hab i).le) σ

/-- R10E01.order_independence, real case. This applies to every enclosing cell;
it also applies to the portion of H in any ordered cell. -/
theorem order_independence_real {n : ℕ} {H : Set (EuclideanSpace ℝ (Fin n))}
    (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ τ : Equiv.Perm (Fin n)) :
    iterated n (a ∘ σ) (b ∘ σ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation σ) =
    iterated n (a ∘ τ) (b ∘ τ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation τ) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hc : IsCompact (e.symm ⁻¹' H) := e.symm.toHomeomorph.isCompact_preimage.mpr hH
  have hv : Convex ℝ (e.symm ⁻¹' H) :=
    Convex.affine_preimage e.symm.toAffineEquiv.toAffineMap hconv
  have hf' : ContinuousOn (f ∘ e.symm) (e.symm ⁻¹' H) :=
    hf.comp e.symm.continuous.continuousOn (fun _ hx => hx)
  simpa only [e, ← zeroExtension_coordinates, Function.comp_assoc] using
    real_order_independence hc hv hf' hab σ τ

/-- R10E01.order_independence, complex case. The component proof uses the
continuous H-supported approximants and the actual complex source bridges. -/
theorem order_independence_complex {n : ℕ} {H : Set (EuclideanSpace ℝ (Fin n))}
    (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContinuousOn f H)
    {a b : Fin n → ℝ} (hab : a ≤ b) (σ τ : Equiv.Perm (Fin n)) :
    complexIterated n (a ∘ σ) (b ∘ σ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation σ) =
    complexIterated n (a ∘ τ) (b ∘ τ)
      (H.indicator f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ coordinatePermutation τ) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hc : IsCompact (e.symm ⁻¹' H) := e.symm.toHomeomorph.isCompact_preimage.mpr hH
  have hv : Convex ℝ (e.symm ⁻¹' H) :=
    Convex.affine_preimage e.symm.toAffineEquiv.toAffineMap hconv
  have hf' : ContinuousOn (f ∘ e.symm) (e.symm ⁻¹' H) :=
    hf.comp e.symm.continuous.continuousOn (fun _ hx => hx)
  simpa only [e, ← zeroExtension_coordinates, Function.comp_assoc] using
    complex_order_independence hc hv hf' hab σ τ

/-- Literal zero-extension source values in Cartesian plane coordinates. -/
def HasPlaneSource (H : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ) (v : ℝ) : Prop :=
  ∃ a b : Fin 2 → ℝ, (∀ i, a i < b i) ∧
    (∀ p ∈ H, ![p.1,p.2] ∈ Icc a b) ∧
    ∀ σ : Equiv.Perm (Fin 2), HasSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      ((fun u ↦ H.indicator f (u 0,u 1)) ∘ coordinatePermutation σ) v

/-- The complex version uses actual complex tagged integrals at every stage. -/
def HasPlaneComplexSource (H : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℂ) (v : ℂ) : Prop :=
  ∃ a b : Fin 2 → ℝ, (∀ i, a i < b i) ∧
    (∀ p ∈ H, ![p.1,p.2] ∈ Icc a b) ∧
    ∀ σ : Equiv.Perm (Fin 2), HasComplexSourceIntegral 2 (a ∘ σ) (b ∘ σ)
      ((fun u ↦ H.indicator f (u 0,u 1)) ∘ coordinatePermutation σ) v

theorem plane_source_real {H : Set (ℝ × ℝ)} (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : (ℝ × ℝ) → ℝ} (hf : ContinuousOn f H) :
    HasPlaneSource H f (∫ p in H, f p) := by
  obtain ⟨a,b,hab,hbox,_,hs⟩ := existence_real
    (pairCoordinates.toHomeomorph.isCompact_preimage.mpr hH)
    (hconv.affine_preimage pairCoordinates.toAffineEquiv.toAffineMap)
    (hf.comp pairCoordinates.continuous.continuousOn (fun _ hx ↦ hx))
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply] at hs
  have hi := pairCoordinates_volume.setIntegral_preimage_emb
    pairCoordinates.toHomeomorph.measurableEmbedding f H
  refine ⟨a,b,hab,?_,fun σ ↦ ?_⟩
  · intro p hp
    have hh := hbox (show pairCoordinates.symm p ∈ pairCoordinates ⁻¹' H by simpa)
    have he : (EuclideanSpace.equiv (Fin 2) ℝ) (pairCoordinates.symm p) = ![p.1,p.2] := by
      ext i
      fin_cases i <;> rfl
    change (EuclideanSpace.equiv (Fin 2) ℝ) (pairCoordinates.symm p) ∈ Icc a b at hh
    rwa [he] at hh
  · have h := hs σ
    rw [hi] at h
    convert h using 1
    funext u
    simp only [Function.comp_apply, ← indicator_comp_right]
    rfl

theorem plane_source_complex {H : Set (ℝ × ℝ)} (hH : IsCompact H) (hconv : Convex ℝ H)
    {f : (ℝ × ℝ) → ℂ} (hf : ContinuousOn f H) :
    HasPlaneComplexSource H f (∫ p in H, f p) := by
  obtain ⟨a,b,hab,hbox,_,hs⟩ := existence_complex
    (pairCoordinates.toHomeomorph.isCompact_preimage.mpr hH)
    (hconv.affine_preimage pairCoordinates.toAffineEquiv.toAffineMap)
    (hf.comp pairCoordinates.continuous.continuousOn (fun _ hx ↦ hx))
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply] at hs
  have hi := pairCoordinates_volume.setIntegral_preimage_emb
    pairCoordinates.toHomeomorph.measurableEmbedding f H
  refine ⟨a,b,hab,?_,fun σ ↦ ?_⟩
  · intro p hp
    have hh := hbox (show pairCoordinates.symm p ∈ pairCoordinates ⁻¹' H by simpa)
    have he : (EuclideanSpace.equiv (Fin 2) ℝ) (pairCoordinates.symm p) = ![p.1,p.2] := by
      ext i
      fin_cases i <;> rfl
    change (EuclideanSpace.equiv (Fin 2) ℝ) (pairCoordinates.symm p) ∈ Icc a b at hh
    rwa [he] at hh
  · have h := hs σ
    rw [hi] at h
    convert h using 1
    funext u
    simp only [Function.comp_apply, ← indicator_comp_right]
    rfl

end Rudin.Chapter10.Exercise01
