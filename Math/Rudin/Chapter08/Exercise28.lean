module

public import Math.Rudin.Chapter08.Exercise27

/-! # Chapter 8, Exercise 28 -/

@[expose] public section

open Set
open scoped Topology Real

namespace Rudin.Chapter08

/-- The closed complex unit disc, with the Euclidean norm and induced topology. -/
abbrev ComplexDisc := {z : ℂ // ‖z‖ ≤ 1}

/-- The complex unit circle, with its induced topology. -/
abbrev ComplexUnitCircle := {z : ℂ // ‖z‖ = 1}

noncomputable def discRadiusPoint (r : Icc (0 : ℝ) 1) (t : ℝ) : ComplexDisc :=
  ⟨r * Complex.exp (Complex.I * t), by
    simpa [Complex.norm_exp_I_mul_ofReal, abs_of_nonneg r.property.1] using r.property.2⟩

theorem continuous_discRadiusPoint :
    Continuous (fun p : Icc (0 : ℝ) 1 × ℝ ↦ discRadiusPoint p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

theorem discRadiusPoint_closed (r : Icc (0 : ℝ) 1) :
    discRadiusPoint r 0 = discRadiusPoint r (2 * Real.pi) := by
  apply Subtype.ext
  exact congrArg ((r : ℂ) * ·) (by simpa using (exercise23_circle 1).1.closed)

/-- Distinct non-antipodal unit vectors have distance strictly less than two. -/
theorem unit_distance_lt_two {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hne : w ≠ -z) : ‖w - z‖ < 2 := by
  have hp : 0 < ‖w + z‖ := norm_pos_iff.mpr (by
    intro h
    apply hne
    exact eq_neg_of_add_eq_zero_left h)
  have hid : ‖w - z‖ ^ 2 + ‖w + z‖ ^ 2 = 4 := by
    have hz' := Complex.sq_norm z
    have hw' := Complex.sq_norm w
    rw [hz] at hz'
    rw [hw] at hw'
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im] at *
    nlinarith
  nlinarith [sq_pos_of_pos hp, norm_nonneg (w - z)]

/-- A continuous disc-to-circle map has an antipodal value at a boundary
point. The witness is on the circle, not just in the closed disc. -/
theorem exercise28_boundary_antipode (g : ComplexDisc → ComplexUnitCircle)
    (hg : Continuous g) :
    ∃ z : ComplexDisc, ‖(z : ℂ)‖ = 1 ∧ (g z : ℂ) = -(z : ℂ) := by
  by_contra hanti
  have hne (z : ComplexDisc) (hz : ‖(z : ℂ)‖ = 1) : (g z : ℂ) ≠ -(z : ℂ) := by
    intro he
    exact hanti ⟨z, hz, he⟩
  let H : Icc (0 : ℝ) 1 → ℝ → ℂ := fun r t ↦ g (discRadiusPoint r t)
  have hcont : Continuous (fun p : Icc (0 : ℝ) 1 × ℝ ↦ H p.1 p.2) :=
    continuous_subtype_val.comp (hg.comp continuous_discRadiusPoint)
  have hl (r) : IsContinuousNonzeroLoop (H r) := by
    refine ⟨(hcont.comp (continuous_const.prodMk continuous_id)).continuousOn,
      congrArg (fun z ↦ (g z : ℂ)) (discRadiusPoint_closed r), ?_⟩
    intro t ht
    exact norm_ne_zero_iff.mp (by rw [(g (discRadiusPoint r t)).property]; norm_num)
  have hidx : Continuous (fun r ↦ continuousCurveIndex (H r) (hl r)) :=
    continuous_family_index H
      (hcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) hl
  let r₀ : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let r₁ : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hzero : continuousCurveIndex (H r₀) (hl r₀) = 0 := by
    have he : H r₀ = fun _ ↦ (g ⟨0, by simp⟩ : ℂ) := by
      funext t
      dsimp only [H]
      congr 2
      apply Subtype.ext
      simp [discRadiusPoint, r₀]
    simp only [he]
    apply continuousCurveIndex_const
    exact norm_ne_zero_iff.mp (by rw [(g ⟨0, by simp⟩).property]; norm_num)
  have heq : continuousCurveIndex (H r₀) (hl r₀) =
      continuousCurveIndex (H r₁) (hl r₁) :=
    IsPreconnected.constant isPreconnected_univ
      hidx.continuousOn (mem_univ r₀) (mem_univ r₁)
  let E : ℝ → ℂ := fun t ↦ Complex.exp (Complex.I * t)
  have hE : IsContinuousNonzeroLoop E := by
    simpa [E] using (show IsContinuousNonzeroLoop
      (fun t : ℝ ↦ Complex.exp (Complex.I * (1 : ℤ) * t)) from
      ⟨(exercise23_circle 1).1.continuous, (exercise23_circle 1).1.closed,
        (exercise23_circle 1).1.nonzero⟩)
  have hEi : continuousCurveIndex E hE = 1 := by
    have hi := exercise26_smooth_agreement hE
      (show IsC1NonzeroLoop E (fun t ↦ Complex.exp (Complex.I * t) * Complex.I)
        0 (2 * Real.pi) by simpa [E] using (exercise23_circle 1).1)
    have hs := (exercise23_circle 1).2
    simp only [Int.cast_one, mul_one] at hs
    have hi' : (continuousCurveIndex E hE : ℂ) = 1 := hi.trans hs
    exact_mod_cast hi'
  have hdist (t : ℝ) : ‖H r₁ t - E t‖ < 2 := by
    apply unit_distance_lt_two (Complex.norm_exp_I_mul_ofReal t)
      (g (discRadiusPoint r₁ t)).property
    simpa [H, E, discRadiusPoint, r₁] using
      hne (discRadiusPoint r₁ t) (by simp [discRadiusPoint, r₁, Complex.norm_exp_I_mul_ofReal])
  let M : ℝ → ℂ := fun t ↦ (H r₁ t + E t) / 2
  have hmE (t : ℝ) : ‖E t - M t‖ < ‖E t‖ := by
    have he : E t - M t = -(H r₁ t - E t) / 2 := by dsimp [M]; ring
    rw [he, norm_div, norm_neg]
    rw [show ‖E t‖ = 1 from Complex.norm_exp_I_mul_ofReal t]
    norm_num
    linarith [hdist t]
  have hmH (t : ℝ) : ‖H r₁ t - M t‖ < ‖H r₁ t‖ := by
    have he : H r₁ t - M t = (H r₁ t - E t) / 2 := by dsimp [M]; ring
    rw [he, norm_div]
    change ‖H r₁ t - E t‖ / ‖(2 : ℂ)‖ < ‖(g (discRadiusPoint r₁ t) : ℂ)‖
    rw [(g (discRadiusPoint r₁ t)).property]
    norm_num
    linarith [hdist t]
  have hM : IsContinuousNonzeroLoop M := by
    refine ⟨((hl r₁).continuous.add hE.continuous).div_const 2, ?_, ?_⟩
    · dsimp [M]
      rw [(hl r₁).closed, hE.closed]
    · intro t ht hz
      have hh := hmE t
      rw [hz, sub_zero] at hh
      exact lt_irrefl _ hh
  have hi₁ := exercise26_perturbation_extension hE hM (fun t _ ↦ hmE t)
  have hi₂ := exercise26_perturbation_extension (hl r₁) hM (fun t _ ↦ hmH t)
  omega

end Rudin.Chapter08
