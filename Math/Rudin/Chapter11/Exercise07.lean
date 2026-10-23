module

public import Math.Rudin.Support.RiemannIntegrability

/-!
# Exercise 11.7: raw Stieltjes oscillations

For each weak partition, put the oscillation of `f` on the CLOSED cell
`[xᵢ,xᵢ₊₁]` on the mass interval `(α(xᵢ),α(xᵢ₊₁)]`.
The integral exists if and only if `f` is bounded and some sequence of these
oscillation functions tends to zero almost everywhere in mass coordinates.
This criterion uses the original values of `α`, not its right normalization.
Necessity uses an L¹-null sequence and an almost-everywhere subsequence.
Sufficiency uses dominated convergence on the finite mass interval.

For `u < v`, the raw cell mass is
`μ((u,v)) + (α(u+) - α(u)) + (α(v) - α(v-))`.
The two endpoint terms cannot be discarded. Positive left jumps require left
continuity of `f`; positive right jumps require right continuity. Only the
inward condition applies at each interval endpoint. These statements are
proved below. A positive source atom with a discontinuous but integrable
integrand shows why `μ`-almost-everywhere continuity alone is not the answer.
The identity specialization is the full ordinary Lebesgue criterion.

Source: Exercise 7, book 333 / PDF 342 (the exercise section starts at book
332 / PDF 341); Example 11.6(b), book 303–304 / PDF 312–313; Theorem 11.33,
book 323–324 / PDF 332–333. Closed cells and raw increments are those of
Definitions 6.1–6.2, book 120–122 / PDF 129–131. No measure-integral bridge
for discontinuous raw integrators is assumed.
-/

@[expose] public section

namespace Rudin.Chapter11.Exercise07

open Set MeasureTheory Filter
open Rudin.Support StieltjesPrototype StieltjesRefinement StieltjesEquivalence
open StieltjesIntegralLaws RiemannIntegrability
open scoped Topology ENNReal NNReal

variable {a b : ℝ}

/-- Map all nodes, including repeated nodes, to their raw integrator values. -/
noncomputable def massPartition (p : Partition a b) (α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) : Partition (α a) (α b) where
  n := p.n
  pos := p.pos
  x := α ∘ p.x
  first := by simp [p.first]
  last := by simp [p.last]
  increasing := by
    intro i hi j hj hij
    exact hα (node_mem p hi) (node_mem p hj) (p.increasing hi hj hij)

/-- The coefficients use both endpoints, even though the mass intervals are half open. -/
noncomputable def cellOscillation (p : Partition a b) (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  sSup (f '' Icc (p.x i) (p.x (i + 1))) -
    sInf (f '' Icc (p.x i) (p.x (i + 1)))

/-- A measurable oscillation function on the raw mass interval. -/
noncomputable def massOscillation (p : Partition a b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) : ℝ → ℝ :=
  step (massPartition p α hα) (cellOscillation p f)

private theorem cell_bounds (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    (f '' Icc (p.x i) (p.x (i + 1))).Nonempty ∧
    BddBelow (f '' Icc (p.x i) (p.x (i + 1))) ∧
    BddAbove (f '' Icc (p.x i) (p.x (i + 1))) := by
  refine ⟨⟨_, mem_image_of_mem f (left_isTag p i hi)⟩, ⟨-M, ?_⟩, ⟨M, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).2

theorem cellOscillation_bounds (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    0 ≤ cellOscillation p f i ∧ cellOscillation p f i ≤ M + M := by
  obtain ⟨hne, hlo, hup⟩ := cell_bounds p hf hi
  have hl : -M ≤ sInf (f '' Icc (p.x i) (p.x (i + 1))) := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).1
  have hu : sSup (f '' Icc (p.x i) (p.x (i + 1))) ≤ M := by
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).2
  have ho := csInf_le_csSup hne hlo hup
  dsimp [cellOscillation]
  constructor <;> linarith

theorem massOscillation_bounds (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (y : ℝ) :
    0 ≤ massOscillation p f α hα y ∧
      massOscillation p f α hα y ≤ (Ioc (α a) (α b)).indicator (fun _ ↦ M + M) y := by
  have hl := step_mono_at (massPartition p α hα)
    (c := fun _ ↦ 0) (d := cellOscillation p f) (y := y)
    (fun i hi _ ↦ (cellOscillation_bounds p hf hi).1)
  have hu := step_mono_at (massPartition p α hα)
    (c := cellOscillation p f) (d := fun _ ↦ M + M) (y := y)
    (fun i hi _ ↦ (cellOscillation_bounds p hf hi).2)
  simpa [step_const, massOscillation] using And.intro hl hu

theorem integrable_massOscillation (p : Partition a b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) : Integrable (massOscillation p f α hα) volume :=
  integrable_step _ _

/-- The mass-coordinate integral is proved equal to the literal Darboux gap. -/
theorem integral_massOscillation (p : Partition a b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) :
    (∫ y, massOscillation p f α hα y) = upperSum p f α - lowerSum p f α := by
  rw [massOscillation, integral_step]
  simp only [massPartition, Function.comp_apply, cellOscillation, sub_mul,
    Finset.sum_sub_distrib, upperSum, lowerSum]

/-- A Lebesgue criterion, not a measurability assumption on `f`.
The exceptional set is null in mass coordinates. -/
def VanishingMassOscillation (f α : ℝ → ℝ) (a b : ℝ)
    (hα : MonotoneOn α (Icc a b)) : Prop :=
  ∃ p : ℕ → Partition a b,
    ∀ᵐ y ∂volume, Tendsto (fun n ↦ massOscillation (p n) f α hα y) atTop (𝓝 0)

/-- Necessity uses an almost-everywhere subsequence of an L¹-null sequence. -/
theorem vanishingMassOscillation_of_integral {f α : ℝ → ℝ} {v : ℝ}
    (hab : a ≤ b) (h : HasDarbouxRSIntegral f α a b v) :
    VanishingMassOscillation f α a b h.1 := by
  obtain ⟨M, hf⟩ := h.2.1
  have hgap : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      upperSum p f α - lowerSum p f α < ε := by
    intro ε hε
    obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
      (hasRSIntegral_of_hasDarbouxRSIntegral hab h) (show 0 < ε / 2 by linarith)
    exact ⟨p, by linarith⟩
  choose p hp using fun n : ℕ ↦ hgap (1 / ((n : ℝ) + 1)) (by positivity)
  let g : ℕ → ℝ → ℝ := fun n ↦ massOscillation (p n) f α h.1
  have hg (n : ℕ) : Integrable (g n) volume := integrable_massOscillation _ _ _ _
  have hpos (n : ℕ) (y : ℝ) : 0 ≤ g n y := (massOscillation_bounds _ h.1 hf y).1
  have hlim : Tendsto (fun n ↦ ∫ y, g n y) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ integral_nonneg (hpos n))
      (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [g, integral_massOscillation] using (hp n).le
  have hLp : Tendsto (fun n ↦ eLpNorm (g n - 0) 1 volume) atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (g n - 0) 1 volume = ENNReal.ofReal (∫ y, g n y) := by
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (hg n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hg n)]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun y ↦ Real.norm_of_nonneg (hpos n y))
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    hLp).exists_seq_tendsto_ae
  exact ⟨fun n ↦ p (ns n), hns⟩

/-- Sufficiency is dominated convergence on the finite raw mass interval. -/
theorem integral_of_vanishingMassOscillation {f α : ℝ → ℝ} {M : ℝ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (h : VanishingMassOscillation f α a b hα) :
    ∃ v, HasDarbouxRSIntegral f α a b v := by
  obtain ⟨p, hp⟩ := h
  have hdom : Integrable ((Ioc (α a) (α b)).indicator (fun _ : ℝ ↦ M + M)) volume :=
    (integrableOn_const (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hi := tendsto_integral_of_dominated_convergence
    ((Ioc (α a) (α b)).indicator (fun _ : ℝ ↦ M + M))
    (fun n ↦ (integrable_massOscillation (p n) f α hα).aestronglyMeasurable) hdom
    (fun n ↦ Eventually.of_forall fun y ↦ by
      have hb := massOscillation_bounds (p n) hα hf y
      rw [Real.norm_of_nonneg hb.1]
      exact hb.2) hp
  simp only [integral_zero] at hi
  apply exists_hasDarbouxRSIntegral_of_small_gap hab hα hf
  intro ε hε
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hi.eventually (gt_mem_nhds hε))
  exact ⟨p n, by simpa only [integral_massOscillation] using hn n le_rfl⟩

/-- Necessary and sufficient criterion for arbitrary monotone raw integrators. -/
theorem exercise07 (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) :
    (∃ v, HasDarbouxRSIntegral f α a b v) ↔
      (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
        VanishingMassOscillation f α a b hα := by
  constructor
  · rintro ⟨v, h⟩
    exact ⟨h.2.1, vanishingMassOscillation_of_integral hab h⟩
  · rintro ⟨⟨M, hf⟩, h⟩
    exact integral_of_vanishingMassOscillation hab hα hf h

/-- The same criterion for the literal tagged refinement integral. -/
theorem exercise07_tagged (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) :
    (∃ v, HasRSIntegral f α a b v) ↔
      (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
        VanishingMassOscillation f α a b hα := by
  simp_rw [hasRSIntegral_iff_hasDarbouxRSIntegral hab]
  exact exercise07 hab hα

private theorem cell_pair_bound (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n)
    {x z : ℝ} (hx : x ∈ Icc (p.x i) (p.x (i + 1)))
    (hz : z ∈ Icc (p.x i) (p.x (i + 1))) :
    |f z - f x| ≤ cellOscillation p f i := by
  have hb := cell_bounds p hf hi
  have hxlo := csInf_le hb.2.1 (mem_image_of_mem f hx)
  have hxhi := le_csSup hb.2.2 (mem_image_of_mem f hx)
  have hzlo := csInf_le hb.2.1 (mem_image_of_mem f hz)
  have hzhi := le_csSup hb.2.2 (mem_image_of_mem f hz)
  rw [abs_le]
  dsimp [cellOscillation]
  constructor <;> linarith

private theorem cell_cover (p : Partition a b) {y : ℝ} (hy : y ∈ Ioc a b) :
    ∃ i < p.n, y ∈ Ioc (p.x i) (p.x (i + 1)) := by
  by_contra! hn
  have hz : step p (fun _ ↦ 1) y = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact indicator_of_notMem (hn i (Finset.mem_range.mp hi)) _
  rw [step_const, indicator_of_mem hy] at hz
  norm_num at hz

private theorem step_at_cell (p : Partition a b) (c : ℕ → ℝ) {i : ℕ}
    (hi : i < p.n) {y : ℝ} (hy : y ∈ Ioc (p.x i) (p.x (i + 1))) :
    step p c y = c i := by
  classical
  unfold step
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hy _
  · intro j hj hji
    apply indicator_of_notMem
    intro hyj
    have hj' := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hji with hji | hij
    · have ho := p.increasing (show j + 1 ∈ Iic p.n by simp only [mem_Iic]; omega)
        (show i ∈ Iic p.n by simp only [mem_Iic]; omega) (by omega : j + 1 ≤ i)
      exact (not_lt_of_ge (hyj.2.trans ho)) hy.1
    · have ho := p.increasing (show i + 1 ∈ Iic p.n by simp only [mem_Iic]; omega)
        (show j ∈ Iic p.n by simp only [mem_Iic]; omega) (by omega : i + 1 ≤ j)
      exact (not_lt_of_ge (hy.2.trans ho)) hyj.1
  · simp [Finset.mem_range, hi]

/-- In the identity case, almost-everywhere vanishing implies relative continuity
away from the countable union of all partition nodes. -/
theorem ae_continuous_of_vanishing_id {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (h : VanishingMassOscillation f id a b (fun _ _ _ _ h ↦ h)) :
    ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x := by
  obtain ⟨p, hp⟩ := h
  have hn : (⋃ n : ℕ, Set.range (p n).x).Countable :=
    countable_iUnion (fun n ↦ countable_range (p n).x)
  have hnodes : ∀ᵐ x ∂volume, x ∉ ⋃ n : ℕ, Set.range (p n).x := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hn.measure_zero (μ := volume)
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hp, hnodes] with x hx hxn hxI
  have hxnode (n k : ℕ) : x ≠ (p n).x k := by
    intro heq
    apply hxn
    exact mem_iUnion.mpr ⟨n, ⟨k, heq.symm⟩⟩
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hx.eventually (gt_mem_nhds hε))
  have hxa : a < x := lt_of_le_of_ne hxI.1 (by simpa only [(p n).first] using (hxnode n 0).symm)
  obtain ⟨i, hi, hxi⟩ := cell_cover (p n) ⟨hxa, hxI.2⟩
  have hxi' : x < (p n).x (i + 1) := lt_of_le_of_ne hxi.2 (hxnode n (i + 1))
  have hosc : cellOscillation (p n) f i < ε := by
    have he := step_at_cell (massPartition (p n) id (fun _ _ _ _ h ↦ h))
      (cellOscillation (p n) f) hi hxi
    exact he ▸ hn n le_rfl
  refine ⟨min (x - (p n).x i) ((p n).x (i + 1) - x),
    lt_min (sub_pos.mpr hxi.1) (sub_pos.mpr hxi'), ?_⟩
  intro z _ hzx
  have hdist := abs_lt.mp (show |z - x| < min (x - (p n).x i)
      ((p n).x (i + 1) - x) by simpa only [Real.dist_eq] using hzx)
  have hz : z ∈ Icc ((p n).x i) ((p n).x (i + 1)) := by
    constructor <;> linarith [min_le_left (x - (p n).x i) ((p n).x (i + 1) - x),
      min_le_right (x - (p n).x i) ((p n).x (i + 1) - x)]
  rw [Real.dist_eq]
  exact (cell_pair_bound (p n) hf hi ⟨hxi.1.le, hxi.2⟩ hz).trans_lt hosc

/-- The criterion specializes to Theorem 11.33(b), in both directions,
including the singleton interval and without a measurability hypothesis. -/
theorem exercise07_id (hab : a ≤ b) (f : ℝ → ℝ) :
    (∃ v, HasDarbouxRSIntegral f id a b v) ↔
      (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
        ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x := by
  constructor
  · intro h
    obtain ⟨hf, ho⟩ := (exercise07 hab (fun _ _ _ _ h ↦ h)).mp h
    obtain ⟨M, hM⟩ := hf
    exact ⟨⟨M, hM⟩, ae_continuous_of_vanishing_id hM ho⟩
  · rintro ⟨⟨M, hf⟩, hc⟩
    exact ⟨_, hasDarbouxRSIntegral_of_ae_continuousWithinAt hab hf hc⟩

private theorem cell_gap_le (p : Partition a b) {f α : ℝ → ℝ} {M : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    {i : ℕ} (hi : i < p.n) :
    cellOscillation p f i * (α (p.x (i + 1)) - α (p.x i)) ≤
      upperSum p f α - lowerSum p f α := by
  have heq : upperSum p f α - lowerSum p f α =
      ∑ j ∈ Finset.range p.n, cellOscillation p f j *
        (α (p.x (j + 1)) - α (p.x j)) := by
    simp only [cellOscillation, sub_mul, Finset.sum_sub_distrib, upperSum, lowerSum]
  rw [heq]
  exact Finset.single_le_sum (fun j hj ↦ mul_nonneg
    (cellOscillation_bounds p hf (Finset.mem_range.mp hj)).1
    (increment_nonneg p hα (Finset.mem_range.mp hj))) (Finset.mem_range.mpr hi)

private theorem small_gap {f α : ℝ → ℝ} {v ε : ℝ} (hab : a ≤ b)
    (h : HasDarbouxRSIntegral f α a b v) (hε : 0 < ε) :
    ∃ p : Partition a b, upperSum p f α - lowerSum p f α < ε := by
  obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
    (hasRSIntegral_of_hasDarbouxRSIntegral hab h) (show 0 < ε / 2 by linarith)
  exact ⟨p, by linarith⟩

/-- Positive left mass forces left continuity, including at the upper endpoint.
The jump condition uses only the raw values on the source interval. -/
theorem left_continuous_of_positive_jump {f α : ℝ → ℝ} {v c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (h : HasDarbouxRSIntegral f α a b v)
    (hj : ∃ d > (0 : ℝ), ∀ t ∈ Ico a c, d ≤ α c - α t) :
    ContinuousWithinAt f (Icc a c) c := by
  obtain ⟨M, hf⟩ := h.2.1
  obtain ⟨d, hd, hj⟩ := hj
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := small_gap (hac.le.trans hcb) h (mul_pos hε hd)
  obtain ⟨i, hi, hci⟩ := cell_cover p ⟨hac, hcb⟩
  have hm : d ≤ α (p.x (i + 1)) - α (p.x i) := by
    have hj' := hj (p.x i) ⟨(node_mem p hi.le).1, hci.1⟩
    have ho := h.1 ⟨hac.le, hcb⟩ (node_mem p (Nat.succ_le_of_lt hi)) hci.2
    linarith
  have hb := cell_gap_le p h.1 hf hi
  have hmul := mul_le_mul_of_nonneg_left hm (cellOscillation_bounds p hf hi).1
  have ho : cellOscillation p f i < ε := by nlinarith
  refine ⟨c - p.x i, sub_pos.mpr hci.1, ?_⟩
  intro z hz hzc
  have hzdist := (abs_lt.mp (show |z - c| < c - p.x i by
    simpa only [Real.dist_eq] using hzc)).1
  have hzi : z ∈ Icc (p.x i) (p.x (i + 1)) := ⟨by linarith, hz.2.trans hci.2⟩
  rw [Real.dist_eq]
  exact (cell_pair_bound p hf hi ⟨hci.1.le, hci.2⟩ hzi).trans_lt ho

private theorem cell_cover_right (p : Partition a b) {y : ℝ} (hy : y ∈ Ico a b) :
    ∃ i < p.n, y ∈ Ico (p.x i) (p.x (i + 1)) := by
  have hex : ∃ k : ℕ, k ≤ p.n ∧ y < p.x k := ⟨p.n, le_rfl, by simpa [p.last] using hy.2⟩
  let k := Nat.find hex
  have hk : k ≤ p.n ∧ y < p.x k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra! hn
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hn
    have := hk.2
    rw [hk0, p.first] at this
    linarith [hy.1]
  have hprev : p.x (k - 1) ≤ y := by
    by_contra! hn
    have hmin := Nat.find_min' hex (show k - 1 ≤ p.n ∧ y < p.x (k - 1) from ⟨by omega, hn⟩)
    change k ≤ k - 1 at hmin
    omega
  refine ⟨k - 1, by omega, hprev, ?_⟩
  simpa only [Nat.sub_add_cancel hkpos] using hk.2

/-- Positive right mass forces right continuity, including at the lower endpoint. -/
theorem right_continuous_of_positive_jump {f α : ℝ → ℝ} {v c : ℝ}
    (hac : a ≤ c) (hcb : c < b) (h : HasDarbouxRSIntegral f α a b v)
    (hj : ∃ d > (0 : ℝ), ∀ t ∈ Ioc c b, d ≤ α t - α c) :
    ContinuousWithinAt f (Icc c b) c := by
  obtain ⟨M, hf⟩ := h.2.1
  obtain ⟨d, hd, hj⟩ := hj
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := small_gap (hac.trans hcb.le) h (mul_pos hε hd)
  obtain ⟨i, hi, hci⟩ := cell_cover_right p ⟨hac, hcb⟩
  have hm : d ≤ α (p.x (i + 1)) - α (p.x i) := by
    have hj' := hj (p.x (i + 1)) ⟨hci.2, (node_mem p (Nat.succ_le_of_lt hi)).2⟩
    have ho := h.1 (node_mem p hi.le) ⟨hac, hcb.le⟩ hci.1
    linarith
  have hb := cell_gap_le p h.1 hf hi
  have hmul := mul_le_mul_of_nonneg_left hm (cellOscillation_bounds p hf hi).1
  have ho : cellOscillation p f i < ε := by nlinarith
  refine ⟨p.x (i + 1) - c, sub_pos.mpr hci.2, ?_⟩
  intro z hz hzc
  have hzdist := (abs_lt.mp (show |z - c| < p.x (i + 1) - c by
    simpa only [Real.dist_eq] using hzc)).2
  have hzi : z ∈ Icc (p.x i) (p.x (i + 1)) := ⟨hci.1.trans hz.1, by linarith⟩
  rw [Real.dist_eq]
  exact (cell_pair_bound p hf hi ⟨hci.1, hci.2.le⟩ hzi).trans_lt ho

/-- Both positive jump parts require full relative continuity at an interior point. -/
theorem continuous_of_two_positive_jumps {f α : ℝ → ℝ} {v c : ℝ}
    (hac : a < c) (hcb : c < b) (h : HasDarbouxRSIntegral f α a b v)
    (hl : ∃ d > (0 : ℝ), ∀ t ∈ Ico a c, d ≤ α c - α t)
    (hr : ∃ d > (0 : ℝ), ∀ t ∈ Ioc c b, d ≤ α t - α c) :
    ContinuousWithinAt f (Icc a b) c := by
  simpa only [Icc_union_Icc_eq_Icc hac.le hcb.le] using
    (left_continuous_of_positive_jump hac hcb.le h hl).union
      (right_continuous_of_positive_jump hac.le hcb h hr)

/-- The local jump conditions, with only the inward condition at each endpoint. -/
def OneSidedJumpConditions (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ c ∈ Ioc a b, (∃ d > (0 : ℝ), ∀ t ∈ Ico a c, d ≤ α c - α t) →
    ContinuousWithinAt f (Icc a c) c) ∧
  (∀ c ∈ Ico a b, (∃ d > (0 : ℝ), ∀ t ∈ Ioc c b, d ≤ α t - α c) →
    ContinuousWithinAt f (Icc c b) c)

/-- Expanded criterion with the jump conditions displayed explicitly.
The oscillation condition already implies these conditions; they are not added
hypotheses that restrict the class of integrable functions. -/
theorem exercise07_with_one_sided_conditions (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) :
    (∃ v, HasDarbouxRSIntegral f α a b v) ↔
      (∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M) ∧
        VanishingMassOscillation f α a b hα ∧ OneSidedJumpConditions f α a b := by
  constructor
  · intro h
    obtain ⟨hf, ho⟩ := (exercise07 hab hα).mp h
    obtain ⟨v, hv⟩ := h
    exact ⟨hf, ho, (fun _ hc hj ↦ left_continuous_of_positive_jump hc.1 hc.2 hv hj),
      (fun _ hc hj ↦ right_continuous_of_positive_jump hc.1 hc.2 hv hj)⟩
  · rintro ⟨hf, ho, _⟩
    exact (exercise07 hab hα).mpr ⟨hf, ho⟩

/-- For a global raw monotone extension the left jump is exactly `α c - α(c-)`. -/
theorem left_continuous_of_leftLim_lt {f α : ℝ → ℝ} {v c : ℝ}
    (hα : Monotone α) (hac : a < c) (hcb : c ≤ b)
    (h : HasDarbouxRSIntegral f α a b v) (hj : Function.leftLim α c < α c) :
    ContinuousWithinAt f (Icc a c) c := by
  apply left_continuous_of_positive_jump hac hcb h
  refine ⟨α c - Function.leftLim α c, sub_pos.mpr hj, ?_⟩
  intro t ht
  exact sub_le_sub_left (hα.le_leftLim ht.2) _

/-- The right jump is exactly `α(c+) - α c`; no right continuity is assumed. -/
theorem right_continuous_of_lt_rightLim {f α : ℝ → ℝ} {v c : ℝ}
    (hα : Monotone α) (hac : a ≤ c) (hcb : c < b)
    (h : HasDarbouxRSIntegral f α a b v) (hj : α c < Function.rightLim α c) :
    ContinuousWithinAt f (Icc c b) c := by
  apply right_continuous_of_positive_jump hac hcb h
  refine ⟨Function.rightLim α c - α c, sub_pos.mpr hj, ?_⟩
  intro t ht
  exact sub_le_sub_right (hα.rightLim_le ht.1) _

/-- The source measure of Example 11.6(b), without an assumption that `α`
is right continuous. This measure alone does not retain the split at `α c`. -/
noncomputable def sourceMeasure (α : ℝ → ℝ) (hα : Monotone α) : Measure ℝ :=
  hα.stieltjesFunction.measure

/-- The open-interval formula printed in Example 11.6(b). -/
theorem sourceMeasure_Ioo {α : ℝ → ℝ} (hα : Monotone α) (u v : ℝ) :
    sourceMeasure α hα (Ioo u v) =
      ENNReal.ofReal (Function.leftLim α v - Function.rightLim α u) := by
  rw [sourceMeasure, StieltjesFunction.measure_Ioo]
  have heq : (hα.stieltjesFunction : ℝ → ℝ) = Function.rightLim α := rfl
  rw [heq, leftLim_rightLim (hα.tendsto_leftLim v)]

/-- The closed-interval formula includes both complete endpoint atoms. -/
theorem sourceMeasure_Icc {α : ℝ → ℝ} (hα : Monotone α) (u v : ℝ) :
    sourceMeasure α hα (Icc u v) =
      ENNReal.ofReal (Function.rightLim α v - Function.leftLim α u) := by
  rw [sourceMeasure, StieltjesFunction.measure_Icc]
  have heq : (hα.stieltjesFunction : ℝ → ℝ) = Function.rightLim α := rfl
  rw [heq, leftLim_rightLim (hα.tendsto_leftLim u)]

/-- The left-open formula from Example 11.6(b). -/
theorem sourceMeasure_Ioc {α : ℝ → ℝ} (hα : Monotone α) (u v : ℝ) :
    sourceMeasure α hα (Ioc u v) =
      ENNReal.ofReal (Function.rightLim α v - Function.rightLim α u) :=
  hα.stieltjesFunction.measure_Ioc u v

/-- The right-open formula from Example 11.6(b). -/
theorem sourceMeasure_Ico {α : ℝ → ℝ} (hα : Monotone α) (u v : ℝ) :
    sourceMeasure α hα (Ico u v) =
      ENNReal.ofReal (Function.leftLim α v - Function.leftLim α u) := by
  rw [sourceMeasure, StieltjesFunction.measure_Ico]
  have heq : (hα.stieltjesFunction : ℝ → ℝ) = Function.rightLim α := rfl
  rw [heq, leftLim_rightLim (hα.tendsto_leftLim v), leftLim_rightLim (hα.tendsto_leftLim u)]

/-- The total source atom is the sum of the left and right jump masses. -/
theorem sourceMeasure_atom {α : ℝ → ℝ} (hα : Monotone α) (c : ℝ) :
    sourceMeasure α hα {c} =
      ENNReal.ofReal (α c - Function.leftLim α c) +
      ENNReal.ofReal (Function.rightLim α c - α c) := by
  rw [sourceMeasure, StieltjesFunction.measure_singleton]
  have heq : (hα.stieltjesFunction : ℝ → ℝ) = Function.rightLim α := rfl
  rw [heq, leftLim_rightLim (hα.tendsto_leftLim c),
    ← ENNReal.ofReal_add (sub_nonneg.mpr (hα.leftLim_le le_rfl))
      (sub_nonneg.mpr (hα.le_rightLim le_rfl))]
  congr 1
  ring

/-- Every nonempty raw cell contains its open-interval measure, the right jump
at its LEFT endpoint, and the left jump at its RIGHT endpoint.
This is the link between the mass-coordinate criterion and the source hint. -/
theorem raw_increment_sourceMeasure {α : ℝ → ℝ} (hα : Monotone α)
    {u v : ℝ} (huv : u < v) :
    α v - α u = (sourceMeasure α hα (Ioo u v)).toReal +
      (Function.rightLim α u - α u) + (α v - Function.leftLim α v) := by
  rw [sourceMeasure_Ioo, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (hα.rightLim_le_leftLim huv))]
  ring

/-- Repeated nodes have empty mass intervals, regardless of `f` and its endpoint values. -/
theorem repeated_node_mass (p : Partition a b) (α : ℝ → ℝ) {i : ℕ}
    (hi : p.x (i + 1) = p.x i) :
    Ioc (α (p.x i)) (α (p.x (i + 1))) = ∅ := by
  rw [hi, Ioc_self]

/-- On a singleton all mass envelopes are zero, with no regularity assumption. -/
theorem massOscillation_self (p : Partition a a) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a a)) (y : ℝ) :
    massOscillation p f α hα y = 0 := by
  unfold massOscillation step
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < p.n := Finset.mem_range.mp hi
  change (Ioc (α (p.x i)) (α (p.x (i + 1)))).indicator _ y = 0
  rw [node_eq_of_self p (show i ≤ p.n by omega),
    node_eq_of_self p (show i + 1 ≤ p.n by omega), Ioc_self, indicator_empty]

/-- The criterion includes singleton intervals, for arbitrary functions. -/
theorem exercise07_self (f α : ℝ → ℝ) (a : ℝ) :
    HasDarbouxRSIntegral f α a a 0 ∧ HasRSIntegral f α a a 0 :=
  ⟨hasDarbouxRSIntegral_self f α a, hasRSIntegral_self f α a⟩

/-- Normalization is not a valid way to erase finite endpoint jumps. -/
theorem exercise07_normalization_endpoint :
    HasDarbouxRSIntegral (fun _ ↦ 1) delayedStep (-1) 0 0 ∧
    (∫ _ in (-1 : ℝ)..0, (1 : ℝ) ∂sourceMeasure delayedStep monotone_delayedStep) = 1 :=
  normalization_changes_endpoint

/-- A right-continuous step with a left atom at zero. -/
noncomputable def immediateStep (x : ℝ) : ℝ := if x < 0 then 0 else 1

theorem monotone_immediateStep : Monotone immediateStep := by
  intro x y hxy
  by_cases hy : y < 0
  · simp [immediateStep, hy, hxy.trans_lt hy]
  · simp only [immediateStep, ite_eq_right hy]
    split_ifs <;> norm_num

private theorem integral_zero_of_equal_endpoints {f α : ℝ → ℝ} {M : ℝ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (heq : α a = α b) :
    HasDarbouxRSIntegral f α a b 0 := by
  apply hasDarbouxRSIntegral_of_hasRSIntegral hab
  refine ⟨hα, ⟨M, hf⟩, fun ε hε ↦ ⟨single hab, fun q _ tag _ ↦ ?_⟩⟩
  have hz : taggedSum q f α tag = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hn (k : ℕ) (hk : k ≤ q.n) : α (q.x k) = α a := by
      have hm := node_mem q hk
      have hl := hα ⟨le_rfl, hab⟩ hm hm.1
      have hu := hα hm ⟨hab, le_rfl⟩ hm.2
      rw [← heq] at hu
      exact le_antisymm hu hl
    rw [hn i hi'.le, hn (i + 1) (Nat.succ_le_of_lt hi'), sub_self, mul_zero]
  simpa only [hz, sub_zero, abs_zero] using hε

private theorem delayedStep_bound (x : ℝ) : |delayedStep x| ≤ 1 := by
  unfold delayedStep
  split_ifs <;> norm_num

/-- A jump discontinuity of `f` is allowed at a positive source atom when its
jump is on the side to which the raw integrator assigns no mass. -/
theorem opposite_jump_integrable : HasDarbouxRSIntegral delayedStep immediateStep (-1) 1 0 := by
  have hl : HasDarbouxRSIntegral delayedStep immediateStep (-1) 0 0 := by
    apply hasDarbouxRSIntegral_congr (by norm_num : (-1 : ℝ) ≤ 0)
      (f := fun _ ↦ 0)
    · simpa using hasDarbouxRSIntegral_const (by norm_num : (-1 : ℝ) < 0)
        (monotone_immediateStep.monotoneOn _) 0
    · intro x hx
      simp [delayedStep, not_lt.mpr hx.2]
  have hr : HasDarbouxRSIntegral delayedStep immediateStep 0 1 0 :=
    integral_zero_of_equal_endpoints (by norm_num) (monotone_immediateStep.monotoneOn _)
      (fun x _ ↦ delayedStep_bound x) (by norm_num [immediateStep])
  simpa using hasDarbouxRSIntegral_join (by norm_num : (-1 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hl hr

private theorem delayedStep_not_right_continuous :
    ¬ ContinuousWithinAt delayedStep (Icc 0 1) 0 := by
  intro h
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousWithinAt_iff.mp h (1 / 2) (by norm_num)
  let z := min δ 1 / 2
  have hz : 0 < z := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have hzδ : z < δ := by dsimp [z]; linarith [min_le_left δ 1]
  have hz1 : z ≤ 1 := by dsimp [z]; linarith [min_le_right δ 1]
  have he := hh (show z ∈ Icc 0 1 from ⟨hz.le, hz1⟩)
    (show dist z 0 < δ by simpa [Real.dist_eq, abs_of_pos hz] using hzδ)
  norm_num [delayedStep, hz, Real.dist_eq] at he

/-- The right endpoint value is tested by the adjacent closed cell when the
integrator has a right jump at the LOWER endpoint. -/
theorem shared_right_endpoint_jump_not_integrable :
    ¬ ∃ v, HasDarbouxRSIntegral delayedStep delayedStep 0 1 v := by
  rintro ⟨v, hv⟩
  apply delayedStep_not_right_continuous
  apply right_continuous_of_positive_jump (a := 0) (by norm_num) (by norm_num) hv
  refine ⟨1, by norm_num, ?_⟩
  intro t ht
  norm_num [delayedStep, ht.1]

private theorem immediateStep_not_left_continuous :
    ¬ ContinuousWithinAt immediateStep (Icc (-1) 0) 0 := by
  intro h
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousWithinAt_iff.mp h (1 / 2) (by norm_num)
  let z := -(min δ 1 / 2)
  have hz : z < 0 := neg_neg_of_pos (div_pos (lt_min hδ zero_lt_one) (by norm_num))
  have hzδ : -z < δ := by dsimp [z]; linarith [min_le_left δ 1]
  have hz1 : -1 ≤ z := by dsimp [z]; linarith [min_le_right δ 1]
  have he := hh (show z ∈ Icc (-1) 0 from ⟨hz1, hz.le⟩)
    (show dist z 0 < δ by simpa [Real.dist_eq, abs_of_neg hz] using hzδ)
  norm_num [immediateStep, hz, Real.dist_eq] at he

/-- The upper endpoint's LEFT jump also forces its actual value to agree with
the corresponding one-sided limit. -/
theorem shared_left_endpoint_jump_not_integrable :
    ¬ ∃ v, HasDarbouxRSIntegral immediateStep immediateStep (-1) 0 v := by
  rintro ⟨v, hv⟩
  apply immediateStep_not_left_continuous
  apply left_continuous_of_positive_jump (b := 0) (by norm_num) (by norm_num) hv
  refine ⟨1, by norm_num, ?_⟩
  intro t ht
  norm_num [immediateStep, ht.2]

/-- A positive source atom does not by itself require two-sided continuity. -/
theorem positive_atom_discontinuous_integrable :
    HasDarbouxRSIntegral delayedStep immediateStep (-1) 1 0 ∧
      sourceMeasure immediateStep monotone_immediateStep {0} = 1 ∧
      ¬ ContinuousWithinAt delayedStep (Icc (-1) 1) 0 := by
  refine ⟨opposite_jump_integrable, ?_, ?_⟩
  · have hl : Function.leftLim immediateStep 0 = 0 := by
      apply leftLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [immediateStep, show x < 0 from hx]
    have hr : Function.rightLim immediateStep 0 = 1 := by
      apply rightLim_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [immediateStep, not_lt.mpr (le_of_lt (show 0 < x from hx))]
    rw [sourceMeasure_atom, hl, hr]
    norm_num [immediateStep]
  · intro hc
    apply delayedStep_not_right_continuous
    exact hc.mono (Icc_subset_Icc (by norm_num) le_rfl)

/-- The naive source-measure continuity criterion is not necessary. -/
theorem source_ae_continuity_not_necessary :
    HasDarbouxRSIntegral delayedStep immediateStep (-1) 1 0 ∧
      ¬ (∀ᵐ x ∂(sourceMeasure immediateStep monotone_immediateStep).restrict (Icc (-1) 1),
        ContinuousWithinAt delayedStep (Icc (-1) 1) x) := by
  obtain ⟨hi, hm, hc⟩ := positive_atom_discontinuous_integrable
  refine ⟨hi, ?_⟩
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  intro hz
  have hsub : ({0} : Set ℝ) ⊆ {x | ¬ (x ∈ Icc (-1) 1 →
      ContinuousWithinAt delayedStep (Icc (-1) 1) x)} := by
    intro x hx
    have hx0 : x = 0 := hx
    subst x
    exact fun h ↦ hc (h (by constructor <;> norm_num))
  have hle := measure_mono (μ := sourceMeasure immediateStep monotone_immediateStep) hsub
  rw [hm, hz] at hle
  exact (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0) hle

/-- The same discontinuity fails at an interior right jump. -/
theorem shared_right_interior_jump_not_integrable :
    ¬ ∃ v, HasDarbouxRSIntegral delayedStep delayedStep (-1) 1 v := by
  rintro ⟨v, hv⟩
  apply delayedStep_not_right_continuous
  apply right_continuous_of_positive_jump (a := -1) (by norm_num) (by norm_num) hv
  refine ⟨1, by norm_num, ?_⟩
  intro t ht
  norm_num [delayedStep, ht.1]

/-- Changing only the raw value at a jump can change integrability, although
Example 11.6(b) assigns exactly the same measure to both integrators. -/
theorem raw_value_changes_integrability :
    sourceMeasure delayedStep monotone_delayedStep =
      sourceMeasure immediateStep monotone_immediateStep ∧
    HasDarbouxRSIntegral delayedStep immediateStep (-1) 1 0 ∧
      ¬ ∃ v, HasDarbouxRSIntegral delayedStep delayedStep (-1) 1 v := by
  refine ⟨?_, opposite_jump_integrable, shared_right_interior_jump_not_integrable⟩
  change monotone_delayedStep.stieltjesFunction.measure =
    monotone_immediateStep.stieltjesFunction.measure
  congr 1
  ext x
  change Function.rightLim delayedStep x = Function.rightLim immediateStep x
  symm
  apply rightLim_eq_of_tendsto
  apply (monotone_delayedStep.tendsto_rightLim x).congr'
  by_cases hx : x < 0
  · filter_upwards [Ioo_mem_nhdsGT hx] with t ht
    simp [delayedStep, immediateStep, ht.2, not_lt.mpr ht.2.le]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := lt_of_le_of_lt (le_of_not_gt hx) (show x < t from ht)
    simp [delayedStep, immediateStep, ht0, not_lt.mpr ht0.le]

/-- Zero raw total mass still requires boundedness, but no continuity. -/
theorem exercise07_zero_mass (hab : a ≤ b) {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (heq : α a = α b) :
    (∃ v, HasDarbouxRSIntegral f α a b v) ↔
      ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M := by
  constructor
  · rintro ⟨v, hv⟩
    exact hv.2.1
  · rintro ⟨M, hf⟩
    exact ⟨0, integral_zero_of_equal_endpoints hab hα hf heq⟩

end Rudin.Chapter11.Exercise07
