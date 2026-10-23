module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Tactic

/-!
# Exercise 11.6
The literal function is 1/n on [-n,n] and zero elsewhere, for n ≥ 1.
Its integral is 2 although it converges uniformly to zero. There is no common
integrable dominating function. On a finite-measure set, uniform convergence
of bounded measurable functions gives a common integrable bound and convergence
of integrals. The last assertions apply to real and complex functions (and to
complete real normed spaces). Source: book page 333, PDF page 342.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter Set
open scoped Topology

noncomputable def exercise06_f (n : ℕ) (x : ℝ) : ℝ :=
  (Icc (-(n : ℝ)) n).indicator (fun _ => 1 / (n : ℝ)) x

theorem exercise06_literal (n : ℕ) (x : ℝ) :
    exercise06_f n x = if |x| ≤ n then 1 / (n : ℝ) else 0 := by
  simp [exercise06_f, indicator_apply, abs_le]

theorem exercise06_bound (n : ℕ) (x : ℝ) :
    ‖exercise06_f n x‖ ≤ 1 / (n : ℝ) := by
  rw [exercise06_literal]
  split_ifs <;> simp

theorem exercise06_uniform_limit :
    TendstoUniformly exercise06_f (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)] with n hn
  intro x
  simpa only [dist_zero_left] using (exercise06_bound n x).trans_lt hn

theorem exercise06_integrable (n : ℕ) : Integrable (exercise06_f n) := by
  exact (integrableOn_const (by simp [Real.volume_Icc])).integrable_indicator measurableSet_Icc

theorem exercise06_integrals (n : ℕ) (hn : 1 ≤ n) :
    ∫ x, exercise06_f n x = (2 : ℝ) := by
  unfold exercise06_f
  rw [integral_indicator measurableSet_Icc]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
  field_simp
  ring

theorem exercise06_no_domination :
    ¬ ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ n : ℕ, 1 ≤ n → ∀ᵐ x, ‖exercise06_f n x‖ ≤ g x := by
  rintro ⟨g, hg, hbound⟩
  have ht : Tendsto (fun n => ∫ x, exercise06_f (n + 1) x) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) g
      (fun n => (exercise06_integrable (n + 1)).aestronglyMeasurable) hg
      (fun n => hbound (n + 1) (by omega))
      (Filter.Eventually.of_forall fun x =>
        (exercise06_uniform_limit.tendsto_at x).comp (tendsto_add_atTop_nat 1))
  have heq : (fun n => ∫ x, exercise06_f (n + 1) x) = fun _ : ℕ => (2 : ℝ) := by
    funext n
    exact exercise06_integrals (n + 1) (by omega)
  rw [heq] at ht
  have : (2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

section FiniteMeasure
variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [MeasurableSpace α] [NormedSpace ℝ V] [CompleteSpace V] in
/-- Uniform convergence and separate boundedness imply one bound for the entire sequence
and its limit. No common bound is an input. -/
theorem exercise06_common_bound (E : Set α) (F : ℕ → α → V) (f : α → V)
    (hbounded : ∀ n, ∃ C : ℝ, ∀ x ∈ E, ‖F n x‖ ≤ C)
    (hconv : TendstoUniformlyOn F f atTop E) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ n x, x ∈ E → ‖F n x‖ ≤ B) ∧
      (∀ x ∈ E, ‖f x‖ ≤ B) := by
  choose C hC using hbounded
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hconv 1 (by norm_num))
  let B : ℝ := (∑ i ∈ Finset.range (N + 1), |C i|) + 2
  have hsum (i : ℕ) (hi : i ≤ N) : |C i| ≤ ∑ j ∈ Finset.range (N + 1), |C j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_range.mpr (by omega))
  have hlim (x : α) (hx : x ∈ E) : ‖f x‖ ≤ |C N| + 1 := by
    have hd := hN N le_rfl x hx
    have hn := norm_le_norm_add_norm_sub (F N x) (f x)
    rw [← dist_eq_norm, dist_comm] at hn
    have hb := (hC N x hx).trans (le_abs_self (C N))
    linarith
  refine ⟨B, by dsimp [B]; positivity, ?_, ?_⟩
  · intro n x hx
    by_cases hn : n ≤ N
    · exact ((hC n x hx).trans (le_abs_self _)).trans ((hsum n hn).trans (by dsimp [B]; linarith))
    · have hd := hN n (by omega) x hx
      have ht := norm_le_norm_add_norm_sub (f x) (F n x)
      rw [← dist_eq_norm] at ht
      have hl := hlim x hx
      have hs := hsum N le_rfl
      dsimp [B]
      linarith
  · intro x hx
    have hl := hlim x hx
    have hs := hsum N le_rfl
    dsimp [B]
    linarith

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- The bound is integrable because the domain has finite measure. -/
theorem exercise06_finite_measure_domination (μ : Measure α) (E : Set α)
    (hfinite : μ E < ⊤) (F : ℕ → α → V) (f : α → V)
    (hbounded : ∀ n, ∃ C : ℝ, ∀ x ∈ E, ‖F n x‖ ≤ C)
    (hconv : TendstoUniformlyOn F f atTop E) :
    ∃ g : α → ℝ, IntegrableOn g E μ ∧
      (∀ n x, x ∈ E → ‖F n x‖ ≤ g x) ∧ (∀ x ∈ E, ‖f x‖ ≤ g x) := by
  obtain ⟨B, _, hB, hfB⟩ := exercise06_common_bound E F f hbounded hconv
  exact ⟨fun _ => B, integrableOn_const hfinite.ne, hB, hfB⟩

omit [CompleteSpace V] in
/-- Integrability of every term and the limit is proved before the integral limit. -/
theorem exercise06_finite_measure_convergence (μ : Measure α) (E : Set α)
    (hE : MeasurableSet E) (hfinite : μ E < ⊤) (F : ℕ → α → V) (f : α → V)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (μ.restrict E))
    (hbounded : ∀ n, ∃ C : ℝ, ∀ x ∈ E, ‖F n x‖ ≤ C)
    (hconv : TendstoUniformlyOn F f atTop E) :
    (∀ n, IntegrableOn (F n) E μ) ∧ IntegrableOn f E μ ∧
      Tendsto (fun n => ∫ x in E, F n x ∂μ) atTop (𝓝 (∫ x in E, f x ∂μ)) := by
  obtain ⟨g, hg, hbound, hlimit⟩ :=
    exercise06_finite_measure_domination μ E hfinite F f hbounded hconv
  have hb n : ∀ᵐ x ∂μ.restrict E, ‖F n x‖ ≤ g x :=
    (ae_restrict_iff' hE).mpr (.of_forall (hbound n))
  have hl : ∀ᵐ x ∂μ.restrict E, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    (ae_restrict_iff' hE).mpr (.of_forall fun x hx => hconv.tendsto_at hx)
  have hm : AEStronglyMeasurable f (μ.restrict E) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hl
  exact ⟨fun n => hg.mono' (hmeas n) (hb n),
    hg.mono' hm ((ae_restrict_iff' hE).mpr (.of_forall hlimit)),
    tendsto_integral_of_dominated_convergence g hmeas hg hb hl⟩

end FiniteMeasure
end Rudin.Chapter11
