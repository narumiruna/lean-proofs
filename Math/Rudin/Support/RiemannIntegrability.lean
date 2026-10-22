module

public import Math.Rudin.Support.StieltjesIntegralLaws
public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ordinary Riemann integrability

These results use `HasDarbouxRSIntegral f id`, with infima and suprema on the
original closed cells of weak partitions. The results include repeated nodes
and singleton intervals.

The measurable step envelopes use half-open cells only to compute their
Lebesgue integrals. Their coefficients still use closed cells. Uniform grids
and dominated convergence give small Darboux gaps from almost-everywhere
relative continuity. Conversely, small gaps give an almost-everywhere limit
of measurable envelopes and thus prove measurability of the integrand.
No BoxIntegral criterion or additional measurability assumption is used.

Source: Rudin, Chapter 6, Theorems 6.8–6.10; foundations for Exercises 6, 8,
16, and 17.
-/

@[expose] public section

namespace Rudin.Support.RiemannIntegrability

open Set MeasureTheory Filter
open StieltjesPrototype StieltjesRefinement StieltjesIntegralLaws StieltjesEquivalence
open scoped Topology ENNReal NNReal

variable {a b : ℝ}

/-- A measurable step function on half-open cells. Empty cells contribute zero. -/
noncomputable def step (p : Partition a b) (c : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n, (Ioc (p.x i) (p.x (i + 1))).indicator (fun _ ↦ c i) y

private theorem indicator_Ioc_sub (l u c y : ℝ) (h : l ≤ u) :
    (Ioc l u).indicator (fun _ ↦ c) y =
      (Iic u).indicator (fun _ ↦ c) y - (Iic l).indicator (fun _ ↦ c) y := by
  simp only [Set.indicator, mem_Ioc, mem_Iic]
  split_ifs <;> simp_all <;> linarith

/-- Constants telescope pointwise, including repeated nodes. -/
theorem step_const (p : Partition a b) (c : ℝ) (y : ℝ) :
    step p (fun _ ↦ c) y = (Ioc a b).indicator (fun _ ↦ c) y := by
  unfold step
  calc
    _ = ∑ i ∈ Finset.range p.n,
        ((Iic (p.x (i + 1))).indicator (fun _ ↦ c) y -
          (Iic (p.x i)).indicator (fun _ ↦ c) y) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact indicator_Ioc_sub _ _ c y (left_isTag p i (Finset.mem_range.mp hi)).2
    _ = _ := by
      rw [Finset.sum_range_sub (fun i ↦ (Iic (p.x i)).indicator (fun _ ↦ c) y),
        p.first, p.last]
      exact (indicator_Ioc_sub a b c y (endpoints_le p)).symm

/-- Cellwise bounds give bounds on the step function at each point. -/
theorem step_mono_at (p : Partition a b) {c d : ℕ → ℝ} {y : ℝ}
    (h : ∀ i < p.n, y ∈ Ioc (p.x i) (p.x (i + 1)) → c i ≤ d i) :
    step p c y ≤ step p d y := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hy : y ∈ Ioc (p.x i) (p.x (i + 1))
  · simpa only [indicator_of_mem hy] using h i (Finset.mem_range.mp hi) hy
  · simp only [indicator_of_notMem hy, le_refl]

theorem integrable_step (p : Partition a b) (c : ℕ → ℝ) : Integrable (step p c) volume := by
  apply integrable_finsetSum
  intro i _
  exact (integrableOn_const (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

/-- The integral of a step function uses the actual lengths of the weak cells. -/
theorem integral_step (p : Partition a b) (c : ℕ → ℝ) :
    (∫ y, step p c y) = ∑ i ∈ Finset.range p.n, c i * (p.x (i + 1) - p.x i) := by
  rw [show step p c = fun y ↦ ∑ i ∈ Finset.range p.n,
    (Ioc (p.x i) (p.x (i + 1))).indicator (fun _ ↦ c i) y from rfl,
    integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator measurableSet_Ioc, setIntegral_const]
    simp only [smul_eq_mul, Real.volume_real_Ioc,
      max_eq_left (sub_nonneg.mpr (left_isTag p i (Finset.mem_range.mp hi)).2)]
    ring
  · intro i _
    exact (integrableOn_const (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc

noncomputable def lowerStep (p : Partition a b) (f : ℝ → ℝ) : ℝ → ℝ :=
  step p (fun i ↦ sInf (f '' Icc (p.x i) (p.x (i + 1))))

noncomputable def upperStep (p : Partition a b) (f : ℝ → ℝ) : ℝ → ℝ :=
  step p (fun i ↦ sSup (f '' Icc (p.x i) (p.x (i + 1))))

private theorem cell_bdd {f : ℝ → ℝ} {M : ℝ} (p : Partition a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    BddBelow (f '' Icc (p.x i) (p.x (i + 1))) ∧
      BddAbove (f '' Icc (p.x i) (p.x (i + 1))) := by
  constructor
  · exact ⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hf x (cell_subset p hi hx))).1⟩
  · exact ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hf x (cell_subset p hi hx))).2⟩

/-- The envelopes bound the integrand on `(a,b]`; no measurability is assumed. -/
theorem step_sandwich {f : ℝ → ℝ} {M : ℝ} (p : Partition a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (y : ℝ) :
    lowerStep p f y ≤ (Ioc a b).indicator f y ∧
      (Ioc a b).indicator f y ≤ upperStep p f y := by
  have hconst : (Ioc a b).indicator f y = step p (fun _ ↦ f y) y := by
    rw [step_const]
    by_cases hy : y ∈ Ioc a b <;> simp [hy]
  rw [hconst]
  constructor
  · apply step_mono_at
    intro i hi hy
    exact csInf_le (cell_bdd p hf hi).1 (mem_image_of_mem f ⟨hy.1.le, hy.2⟩)
  · apply step_mono_at
    intro i hi hy
    exact le_csSup (cell_bdd p hf hi).2 (mem_image_of_mem f ⟨hy.1.le, hy.2⟩)

/-- Global bounds for both measurable envelopes. -/
theorem step_bounds {f : ℝ → ℝ} {M : ℝ} (p : Partition a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (y : ℝ) :
    |lowerStep p f y| ≤ (Ioc a b).indicator (fun _ ↦ M) y ∧
      |upperStep p f y| ≤ (Ioc a b).indicator (fun _ ↦ M) y := by
  have hne (i : ℕ) (hi : i < p.n) :
      (f '' Icc (p.x i) (p.x (i + 1))).Nonempty :=
    ⟨_, mem_image_of_mem f (left_isTag p i hi)⟩
  have hcoeff (i : ℕ) (hi : i < p.n) :
      -M ≤ sInf (f '' Icc (p.x i) (p.x (i + 1))) ∧
      sSup (f '' Icc (p.x i) (p.x (i + 1))) ≤ M := by
    constructor
    · apply le_csInf (hne i hi)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hf x (cell_subset p hi hx))).1
    · apply csSup_le (hne i hi)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hf x (cell_subset p hi hx))).2
  have horder (i : ℕ) (hi : i < p.n) := csInf_le_csSup (hne i hi)
    (cell_bdd p hf hi).1 (cell_bdd p hf hi).2
  have hl : step p (fun _ ↦ -M) y ≤ lowerStep p f y :=
    step_mono_at p (fun i hi _ ↦ (hcoeff i hi).1)
  have hu : upperStep p f y ≤ step p (fun _ ↦ M) y :=
    step_mono_at p (fun i hi _ ↦ (hcoeff i hi).2)
  have hlu : lowerStep p f y ≤ upperStep p f y :=
    step_mono_at p (fun i hi _ ↦ horder i hi)
  rw [step_const] at hl hu
  have hneg : (Ioc a b).indicator (fun _ ↦ -M) y =
      -(Ioc a b).indicator (fun _ ↦ M) y := by
    by_cases hy : y ∈ Ioc a b <;> simp [hy]
  rw [hneg] at hl
  exact ⟨abs_le.mpr ⟨hl, hlu.trans hu⟩, abs_le.mpr ⟨hl.trans hlu, hu⟩⟩

/-- Arbitrarily small literal Darboux gaps imply Lebesgue integrability.
Measurability of the integrand is a conclusion, not a hypothesis. -/
theorem integrable_indicator_of_small_gap {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hgap : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      upperSum p f id - lowerSum p f id < ε) :
    Integrable ((Ioc a b).indicator f) volume := by
  choose p hp using fun n : ℕ ↦ hgap (1 / ((n : ℝ) + 1)) (by positivity)
  let g : ℕ → ℝ → ℝ := fun n y ↦ upperStep (p n) f y - lowerStep (p n) f y
  have hg (n : ℕ) : Integrable (g n) volume :=
    (integrable_step _ _).sub (integrable_step _ _)
  have hpos (n : ℕ) (y : ℝ) : 0 ≤ g n y := by
    have := step_sandwich (p n) hf y
    dsimp [g]
    linarith
  have hint (n : ℕ) : (∫ y, g n y) = upperSum (p n) f id - lowerSum (p n) f id := by
    dsimp only [g, upperStep, lowerStep]
    rw [integral_sub (integrable_step _ _) (integrable_step _ _)]
    simp only [integral_step, upperSum, lowerSum, id_eq]
  have hlim : Tendsto (fun n ↦ ∫ y, g n y) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ integral_nonneg (hpos n))
      (fun n ↦ (hint n).symm ▸ (hp n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hLp : Tendsto (fun n ↦ eLpNorm (g n - 0) 1 volume) atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (g n - 0) 1 volume = ENNReal.ofReal (∫ y, g n y) := by
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm (hg n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (hg n)]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ Real.norm_of_nonneg (hpos n y)
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    hLp).exists_seq_tendsto_ae
  have hlower : ∀ᵐ y ∂volume, Tendsto (fun n ↦ lowerStep (p (ns n)) f y) atTop
      (𝓝 ((Ioc a b).indicator f y)) := by
    filter_upwards [hns] with y hy
    have hleft := (tendsto_const_nhds (x := (Ioc a b).indicator f y) (f := atTop)).sub hy
    simp only [Pi.zero_apply, sub_zero] at hleft
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hleft tendsto_const_nhds
    · intro n
      have := (step_sandwich (p (ns n)) hf y).2
      dsimp [g]
      linarith
    · intro n
      exact (step_sandwich (p (ns n)) hf y).1
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (integrable_step (p (ns n)) _).aestronglyMeasurable) hlower
  have hdom : Integrable ((Ioc a b).indicator (fun _ : ℝ ↦ M)) volume :=
    (integrableOn_const (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  apply hdom.mono' hm
  exact Eventually.of_forall fun y ↦ by
    by_cases hy : y ∈ Ioc a b
    · simpa [hy, Real.norm_eq_abs] using hf y ⟨hy.1.le, hy.2⟩
    · simp [hy]

/-- Every integrable ordinary integrand is between its literal Darboux sums. -/
theorem integral_sandwich {f : ℝ → ℝ} {M : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hi : IntervalIntegrable f volume a b)
    (p : Partition a b) :
    lowerSum p f id ≤ (∫ x in a..b, f x) ∧ (∫ x in a..b, f x) ≤ upperSum p f id := by
  have hfi : Integrable ((Ioc a b).indicator f) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi).integrable_indicator measurableSet_Ioc
  have hl := integral_mono (integrable_step p _) hfi
    (fun y ↦ (step_sandwich p hf y).1)
  have hu := integral_mono hfi (integrable_step p _)
    (fun y ↦ (step_sandwich p hf y).2)
  simpa only [lowerStep, upperStep, integral_step, lowerSum, upperSum, id_eq,
    integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab] using And.intro hl hu

/-- An actual ordinary Darboux integral is interval integrable and has the same value.
No continuity or measurability is added to the assumptions. -/
theorem intervalIntegrable_and_integral_eq {f : ℝ → ℝ} {v : ℝ}
    (hab : a ≤ b) (hf : HasDarbouxRSIntegral f id a b v) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) = v := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hgap : ∀ ε > (0 : ℝ), ∃ p : Partition a b,
      upperSum p f id - lowerSum p f id < ε := by
    intro ε hε
    obtain ⟨p, hl, hu⟩ := hasRSIntegral_small_darboux_sums
      (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) (show 0 < ε / 2 by linarith)
    exact ⟨p, by linarith⟩
  have hi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((integrable_indicator_iff measurableSet_Ioc).mp (integrable_indicator_of_small_gap hM hgap))
  refine ⟨hi, le_antisymm ?_ ?_⟩
  · calc
      (∫ x in a..b, f x) ≤ sInf (Set.range fun p : Partition a b ↦ upperSum p f id) := ?_
      _ = v := hf.2.2.2
    apply le_csInf (show (Set.range fun p : Partition a b ↦ upperSum p f id).Nonempty from
      ⟨_, ⟨single hab, rfl⟩⟩)
    rintro _ ⟨p, rfl⟩
    exact (integral_sandwich hab hM hi p).2
  · calc
      v = sSup (Set.range fun p : Partition a b ↦ lowerSum p f id) := hf.2.2.1.symm
      _ ≤ (∫ x in a..b, f x) := ?_
    apply csSup_le (show (Set.range fun p : Partition a b ↦ lowerSum p f id).Nonempty from
      ⟨_, ⟨single hab, rfl⟩⟩)
    rintro _ ⟨p, rfl⟩
    exact (integral_sandwich hab hM hi p).1

/-- Both envelopes preserve bounds valid on all cells that contain the point. -/
theorem step_local_bounds {f : ℝ → ℝ} {M l u y : ℝ} (p : Partition a b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hy : y ∈ Ioc a b)
    (h : ∀ i < p.n, y ∈ Ioc (p.x i) (p.x (i + 1)) →
      ∀ x ∈ Icc (p.x i) (p.x (i + 1)), l ≤ f x ∧ f x ≤ u) :
    l ≤ lowerStep p f y ∧ lowerStep p f y ≤ u ∧
      l ≤ upperStep p f y ∧ upperStep p f y ≤ u := by
  have hlo (i : ℕ) (hi : i < p.n) (hyi : y ∈ Ioc (p.x i) (p.x (i + 1))) :
      l ≤ sInf (f '' Icc (p.x i) (p.x (i + 1))) := by
    apply le_csInf ⟨_, mem_image_of_mem f (left_isTag p i hi)⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (h i hi hyi x hx).1
  have hup (i : ℕ) (hi : i < p.n) (hyi : y ∈ Ioc (p.x i) (p.x (i + 1))) :
      sSup (f '' Icc (p.x i) (p.x (i + 1))) ≤ u := by
    apply csSup_le ⟨_, mem_image_of_mem f (left_isTag p i hi)⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (h i hi hyi x hx).2
  have hl := step_mono_at p hlo
  have hu := step_mono_at p hup
  rw [step_const, indicator_of_mem hy] at hl hu
  have hlu := (step_sandwich p hf y).1.trans (step_sandwich p hf y).2
  exact ⟨hl, hlu.trans hu, hl.trans hlu, hu⟩

/-- Uniform weak grids, including the singleton case. -/
noncomputable def grid (hab : a ≤ b) (n : ℕ) : Partition a b :=
  StieltjesMeasureBridge.uniformGrid hab (n + 1) (Nat.succ_pos n)

/-- At relative continuity points, the closed-cell envelopes converge to the function. -/
theorem grid_steps_tendsto {f : ℝ → ℝ} {M y : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hy : y ∈ Ioc a b)
    (hc : ContinuousWithinAt f (Icc a b) y) :
    Tendsto (fun n ↦ lowerStep (grid hab n) f y) atTop (𝓝 (f y)) ∧
      Tendsto (fun n ↦ upperStep (grid hab n) f y) atTop (𝓝 (f y)) := by
  have hmesh : Tendsto (fun n : ℕ ↦ (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hbound : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      dist (lowerStep (grid hab n) f y) (f y) < ε ∧
      dist (upperStep (grid hab n) f y) (f y) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by linarith)
    filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn
    have hb := step_local_bounds (grid hab n) hf hy (l := f y - ε / 2)
      (u := f y + ε / 2) (by
        intro i hi hyi x hx
        have hlen : (grid hab n).x (i + 1) - (grid hab n).x i =
            (b - a) / ((n : ℝ) + 1) := by
          simpa only [grid, Nat.cast_add, Nat.cast_one] using
            StieltjesMeasureBridge.uniformGrid_cell_length hab (n + 1) (Nat.succ_pos n) i
        have hdist : dist x y < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hx.1, hx.2, hyi.1, hyi.2]
        have hclose := hmod (cell_subset (grid hab n) hi hx) hdist
        rw [Real.dist_eq, abs_lt] at hclose
        constructor <;> linarith)
    constructor <;> rw [Real.dist_eq, abs_lt] <;> constructor <;> linarith [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  exact ⟨Metric.tendsto_nhds.mpr (fun ε hε ↦ (hbound ε hε).mono fun _ h ↦ h.1),
    Metric.tendsto_nhds.mpr (fun ε hε ↦ (hbound ε hε).mono fun _ h ↦ h.2)⟩

/-- Bounded functions continuous almost everywhere have arbitrarily small literal
Darboux gaps. Relative continuity includes compact interval endpoints. -/
theorem small_gap_of_ae_continuousWithinAt {f : ℝ → ℝ} {M : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x) :
    ∀ ε > (0 : ℝ), ∃ p : Partition a b, upperSum p f id - lowerSum p f id < ε := by
  let g : ℕ → ℝ → ℝ := fun n y ↦ upperStep (grid hab n) f y - lowerStep (grid hab n) f y
  have hg (n : ℕ) : Integrable (g n) volume :=
    (integrable_step _ _).sub (integrable_step _ _)
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n ↦ g n y) atTop (𝓝 0) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hc] with y hy
    by_cases hym : y ∈ Ioc a b
    · have h := grid_steps_tendsto hab hf hym (hy ⟨hym.1.le, hym.2⟩)
      simpa only [sub_self] using h.2.sub h.1
    · have hz (n : ℕ) : g n y = 0 := by
        have hb := step_bounds (grid hab n) hf y
        simp only [indicator_of_notMem hym] at hb
        have hl := abs_eq_zero.mp (le_antisymm hb.1 (abs_nonneg _))
        have hu := abs_eq_zero.mp (le_antisymm hb.2 (abs_nonneg _))
        simp only [g, hl, hu, sub_self]
      simpa only [hz] using (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  have hdom : Integrable ((Ioc a b).indicator (fun _ : ℝ ↦ M + M)) volume :=
    (integrableOn_const (measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hi := tendsto_integral_of_dominated_convergence
    ((Ioc a b).indicator (fun _ : ℝ ↦ M + M)) (fun n ↦ (hg n).aestronglyMeasurable) hdom
    (fun n ↦ Eventually.of_forall fun y ↦ by
      have hb := step_bounds (grid hab n) hf y
      have hn := abs_sub (upperStep (grid hab n) f y) (lowerStep (grid hab n) f y)
      rw [Real.norm_eq_abs]
      dsimp only [g]
      by_cases hy : y ∈ Ioc a b
      · simp only [indicator_of_mem hy] at hb ⊢
        exact hn.trans (add_le_add hb.2 hb.1)
      · simp only [indicator_of_notMem hy] at hb ⊢
        simpa only [zero_add] using hn.trans (add_le_add hb.2 hb.1)) hlim
  simp only [integral_zero] at hi
  intro ε hε
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hi.eventually (gt_mem_nhds hε))
  refine ⟨grid hab n, ?_⟩
  have hn' := hn n le_rfl
  dsimp only [g, upperStep, lowerStep] at hn'
  rw [integral_sub (integrable_step _ _) (integrable_step _ _), integral_step, integral_step] at hn'
  exact hn'

/-- The ordinary Riemann integral exists and equals the interval integral for
bounded functions continuous almost everywhere on the compact interval. -/
theorem hasDarbouxRSIntegral_of_ae_continuousWithinAt {f : ℝ → ℝ} {M : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  obtain ⟨v, hv⟩ := exists_hasDarbouxRSIntegral_of_small_gap hab
    (fun _ _ _ _ h ↦ h) hf (small_gap_of_ae_continuousWithinAt hab hf hc)
  rw [(intervalIntegrable_and_integral_eq hab hv).2]
  exact hv

/-- Monotone functions on a compact interval have an actual ordinary Riemann integral. -/
theorem hasDarbouxRSIntegral_of_monotoneOn {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  apply hasDarbouxRSIntegral_of_ae_continuousWithinAt hab
    (M := |f a| + |f b|)
  · intro x hx
    have hl := hf ⟨le_rfl, hab⟩ hx hx.1
    have hu := hf hx ⟨hab, le_rfl⟩ hx.2
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (f b), neg_abs_le (f a), abs_nonneg (f a), abs_nonneg (f b)]
  · rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
    simpa only [not_imp] using hf.countable_not_continuousWithinAt.measure_zero (μ := volume)

/-- Decreasing monotone functions have the same ordinary Riemann existence result. -/
theorem hasDarbouxRSIntegral_of_antitoneOn {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  have hn : MonotoneOn (fun x ↦ -f x) (Icc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hf hx hy hxy)
  have h := hasDarbouxRSIntegral_neg hab (hasDarbouxRSIntegral_of_monotoneOn hab hn)
  simpa only [neg_neg, intervalIntegral.integral_neg] using h

-- Singleton regression: the function need not be continuous or measurable.
example (f : ℝ → ℝ) (a : ℝ) :
    IntervalIntegrable f volume a a ∧ (∫ x in a..a, f x) = 0 :=
  intervalIntegrable_and_integral_eq le_rfl (hasDarbouxRSIntegral_self f id a)

-- Repeated nodes contribute zero to each measurable cell envelope.
example (p : Partition a b) (c : ℕ → ℝ) {i : ℕ}
    (hi : p.x (i + 1) = p.x i) (y : ℝ) :
    (Ioc (p.x i) (p.x (i + 1))).indicator (fun _ ↦ c i) y = 0 := by
  simp only [hi, Ioc_self, indicator_empty]

-- A jump integrand checks that the bridge does not require continuity.
example (hab : a ≤ b) (c : ℝ) :
    HasDarbouxRSIntegral (fun x ↦ if x < c then 0 else 1) id a b
      (∫ x in a..b, if x < c then 0 else 1) := by
  apply hasDarbouxRSIntegral_of_monotoneOn hab
  intro x _ y _ hxy
  change (if x < c then (0 : ℝ) else 1) ≤ (if y < c then 0 else 1)
  split_ifs <;> norm_num at *
  linarith

end Rudin.Support.RiemannIntegrability
