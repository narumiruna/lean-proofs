module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exercise 11.3
The convergence set of measurable extended-real-valued functions is measurable,
for extended limits and, separately, for finite real limits. The finite-limit
result does not require finite-valued terms. The real and complex specializations
are retained. Source: book page 332, PDF page 341; Definition 11.13 on book
page 310, PDF page 319.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter
open scoped Topology
variable {α : Type*} [MeasurableSpace α]

/-- Extended convergence includes limits at either infinity. -/
theorem exercise03_ereal (f : ℕ → α → EReal) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : EReal, Tendsto (fun n => f n x) atTop (𝓝 y)} :=
  measurableSet_exists_tendsto hf

/-- A finite limit is an extended limit other than either infinity. -/
theorem exercise03_ereal_finite_iff (u : ℕ → EReal) :
    (∃ y : ℝ, Tendsto u atTop (𝓝 (y : EReal))) ↔
      (∃ y : EReal, Tendsto u atTop (𝓝 y)) ∧
        ¬ Tendsto u atTop (𝓝 ⊤) ∧ ¬ Tendsto u atTop (𝓝 ⊥) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, hy⟩,
      fun ht => EReal.coe_ne_top y (tendsto_nhds_unique hy ht),
      fun hb => EReal.coe_ne_bot y (tendsto_nhds_unique hy hb)⟩
  · rintro ⟨⟨y, hy⟩, ht, hb⟩
    have htop : y ≠ ⊤ := fun h => ht (h ▸ hy)
    have hbot : y ≠ ⊥ := fun h => hb (h ▸ hy)
    exact ⟨y.toReal, by simpa only [EReal.coe_toReal htop hbot] using hy⟩

/-- The finite-real-limit set is measurable even when terms can be infinite. -/
theorem exercise03_ereal_finite (f : ℕ → α → EReal)
    (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (y : EReal))} := by
  have hs : {x | ∃ y : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (y : EReal))} =
      {x | ∃ y : EReal, Tendsto (fun n => f n x) atTop (𝓝 y)} \
        ({x | Tendsto (fun n => f n x) atTop (𝓝 ⊤)} ∪
          {x | Tendsto (fun n => f n x) atTop (𝓝 ⊥)}) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, not_or] using
      exercise03_ereal_finite_iff (fun n => f n x)
  rw [hs]
  exact (exercise03_ereal f hf).diff
    ((measurableSet_tendsto_fun hf measurable_const).union
      (measurableSet_tendsto_fun hf measurable_const))

theorem exercise03_real (f : ℕ → α → ℝ) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : ℝ, Tendsto (fun n => f n x) atTop (𝓝 y)} :=
  measurableSet_exists_tendsto hf

/-- Finite complex convergence is equivalent to finite convergence of both components. -/
theorem exercise03_complex_iff (u : ℕ → ℂ) :
    (∃ z : ℂ, Tendsto u atTop (𝓝 z)) ↔
      (∃ a : ℝ, Tendsto (fun n => (u n).re) atTop (𝓝 a)) ∧
      (∃ b : ℝ, Tendsto (fun n => (u n).im) atTop (𝓝 b)) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨⟨z.re, Complex.continuous_re.continuousAt.tendsto.comp hz⟩,
      ⟨z.im, Complex.continuous_im.continuousAt.tendsto.comp hz⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_⟩
    have h := ha.ofReal.add (hb.ofReal.mul_const Complex.I)
    simpa only [Complex.re_add_im] using h

theorem exercise03_complex (f : ℕ → α → ℂ) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : ℂ, Tendsto (fun n => f n x) atTop (𝓝 y)} := by
  have hs : {x | ∃ y : ℂ, Tendsto (fun n => f n x) atTop (𝓝 y)} =
      {x | ∃ a : ℝ, Tendsto (fun n => (f n x).re) atTop (𝓝 a)} ∩
      {x | ∃ b : ℝ, Tendsto (fun n => (f n x).im) atTop (𝓝 b)} := by
    ext x
    exact exercise03_complex_iff (fun n => f n x)
  rw [hs]
  exact (exercise03_real _ (fun n => Complex.continuous_re.measurable.comp (hf n))).inter
    (exercise03_real _ (fun n => Complex.continuous_im.measurable.comp (hf n)))

end Rudin.Chapter11
