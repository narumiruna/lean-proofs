module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Exercise 11.10
Finite measure includes the zero measure. The counterexample is exactly
1 / (1 + |x|), with Lebesgue measure on the whole real line.
Source: book page 333, PDF page 342.
-/
@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Set

theorem exercise10_finite_measure_inclusion {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hf : MemLp f 2 μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hf.mono_exponent (by norm_num))

noncomputable def exercise10_f (x : ℝ) : ℝ := 1 / (1 + |x|)

theorem exercise10_continuous : Continuous exercise10_f := by
  unfold exercise10_f
  exact continuous_const.div (continuous_const.add continuous_abs)
    (fun x => ne_of_gt (by positivity))

theorem exercise10_square_integrable :
    Integrable (fun x : ℝ => exercise10_f x ^ 2) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp))
  convert h using 1
  funext x
  simp [exercise10_f, Real.norm_eq_abs, inv_pow]

theorem exercise10_memLp_two : MemLp exercise10_f 2 volume :=
  (memLp_two_iff_integrable_sq exercise10_continuous.aestronglyMeasurable).mpr
    exercise10_square_integrable

theorem exercise10_nonintegrable : ¬ Integrable exercise10_f := by
  intro hf
  have hi : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioi 1) := by
    apply (hf.const_mul 2).integrableOn.mono'
      (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_inv, abs_of_pos hx0]
    dsimp [exercise10_f]
    rw [abs_of_pos hx0]
    rw [← one_div, ← mul_div_assoc]
    apply (div_le_div_iff₀ hx0 (by positivity : 0 < 1 + x)).mpr
    have hx1 : 1 < x := hx
    nlinarith
  have h := (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mp hi
  norm_num at h

theorem exercise10_infinite_measure : volume (univ : Set ℝ) = ⊤ := by simp

end Rudin.Chapter11
