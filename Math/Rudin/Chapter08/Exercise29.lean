module

public import Math.Rudin.Chapter08.Exercise28

/-! # Chapter 8, Exercise 29

The proof uses the specified quadratic ray construction, not a fixed-point
theorem from the library.
-/

@[expose] public section

open Set
open scoped Topology Real

namespace Rudin.Chapter08

/-- The nonnegative root of `A s² - 2 B s + C = 0`. -/
noncomputable def rayRoot (A B C : ℝ) : ℝ :=
  (B + Real.sqrt (B ^ 2 - A * C)) / A

/-- The geometric coefficient bounds select exactly one nonnegative root,
including when the initial point is on the boundary (`C = 0`). -/
theorem rayRoot_unique {A B C : ℝ} (hA : 0 < A) (hC : C ≤ 0)
    (hbound : A + 2 * B + C ≤ 0) :
    0 ≤ rayRoot A B C ∧
    A * rayRoot A B C ^ 2 - 2 * B * rayRoot A B C + C = 0 ∧
    ∀ t : ℝ, 0 ≤ t → A * t ^ 2 - 2 * B * t + C = 0 → t = rayRoot A B C := by
  have hd : 0 ≤ B ^ 2 - A * C := by nlinarith [sq_nonneg B, mul_nonpos_of_nonneg_of_nonpos hA.le hC]
  have hs := Real.sq_sqrt hd
  have hp := Real.sqrt_nonneg (B ^ 2 - A * C)
  have hab : -B ≤ Real.sqrt (B ^ 2 - A * C) := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hA.le hC]
  have hstrict : B < Real.sqrt (B ^ 2 - A * C) := by
    rcases lt_or_eq_of_le hC with hlt | rfl
    · nlinarith [mul_neg_of_pos_of_neg hA hlt]
    · nlinarith
  have hr : A * rayRoot A B C = B + Real.sqrt (B ^ 2 - A * C) := by
    unfold rayRoot
    field_simp
  have hroot : A * rayRoot A B C ^ 2 - 2 * B * rayRoot A B C + C = 0 := by
    have he : A * (A * rayRoot A B C ^ 2 - 2 * B * rayRoot A B C + C) = 0 := by
      nlinarith [sq_nonneg (A * rayRoot A B C - B - Real.sqrt (B ^ 2 - A * C))]
    exact (mul_eq_zero.mp he).resolve_left hA.ne'
  refine ⟨by unfold rayRoot; exact div_nonneg (by linarith) hA.le, hroot, ?_⟩
  intro t ht he
  have hpos : 0 < A * (t + rayRoot A B C) - 2 * B := by
    nlinarith [mul_nonneg hA.le ht]
  have hfactor : (t - rayRoot A B C) * (A * (t + rayRoot A B C) - 2 * B) = 0 := by
    nlinarith [he, hroot]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hpos.ne')

/-- The leading coefficient is the squared Euclidean distance from `w` to `z`. -/
noncomputable def rayA (z w : ℂ) : ℝ := Complex.normSq (w - z)

/-- The mixed coefficient is the real inner product of `z` and `w-z`. -/
noncomputable def rayB (z w : ℂ) : ℝ :=
  z.re * (w - z).re + z.im * (w - z).im

noncomputable def rayC (z : ℂ) : ℝ := Complex.normSq z - 1

noncomputable def rayParameter (z w : ℂ) : ℝ := rayRoot (rayA z w) (rayB z w) (rayC z)

/-- The point on the ray from `w` through `z`, beyond `z`. -/
noncomputable def rayBoundaryPoint (z w : ℂ) : ℂ := z - rayParameter z w * (w - z)

theorem ray_coefficients {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hne : w ≠ z) :
    0 < rayA z w ∧ rayC z ≤ 0 ∧ rayA z w + 2 * rayB z w + rayC z ≤ 0 := by
  have hA : 0 < rayA z w := by
    rw [rayA, Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hz' : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hw' : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  refine ⟨hA, by dsimp [rayC]; linarith, ?_⟩
  simp only [rayA, rayB, rayC, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

/-- Expanding the exact complex norm gives the source quadratic equation. -/
theorem ray_quadratic (z w : ℂ) (s : ℝ) :
    Complex.normSq (z - s * (w - z)) - 1 =
      rayA z w * s ^ 2 - 2 * rayB z w * s + rayC z := by
  simp only [rayA, rayB, rayC, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Exercise 29: the explicit parameter is the unique nonnegative quadratic
root and the unique nonnegative parameter for intersection with the circle. -/
theorem exercise29_ray_boundary_map {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hne : w ≠ z) :
    0 ≤ rayParameter z w ∧
    rayA z w * rayParameter z w ^ 2 - 2 * rayB z w * rayParameter z w + rayC z = 0 ∧
    ‖rayBoundaryPoint z w‖ = 1 ∧
    (∀ s : ℝ, 0 ≤ s →
      (rayA z w * s ^ 2 - 2 * rayB z w * s + rayC z = 0 ↔ s = rayParameter z w)) ∧
    (∀ s : ℝ, 0 ≤ s → (‖z - s * (w - z)‖ = 1 ↔ s = rayParameter z w)) := by
  obtain ⟨hA, hC, hb⟩ := ray_coefficients hz hw hne
  obtain ⟨hs, he, hu⟩ := rayRoot_unique hA hC hb
  change 0 ≤ rayParameter z w at hs
  change rayA z w * rayParameter z w ^ 2 - 2 * rayB z w * rayParameter z w + rayC z = 0 at he
  have hnorm : ‖rayBoundaryPoint z w‖ = 1 := by
    have hq := ray_quadratic z w (rayParameter z w)
    rw [he] at hq
    rw [Complex.normSq_eq_norm_sq] at hq
    change ‖rayBoundaryPoint z w‖ ^ 2 - 1 = 0 at hq
    nlinarith [norm_nonneg (rayBoundaryPoint z w)]
  refine ⟨hs, he, hnorm, ?_, ?_⟩
  · intro s hs
    exact ⟨hu s hs, fun h ↦ h ▸ he⟩
  · intro s hs
    constructor
    · intro hn
      apply hu s hs
      rw [← ray_quadratic, Complex.normSq_eq_norm_sq, hn]
      norm_num
    · rintro rfl
      exact hnorm

/-- The constructed point lies on the ray starting at `w` and passing
through `z`; its ray coordinate is at least one. -/
theorem rayBoundaryPoint_on_ray {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hne : w ≠ z) :
    1 ≤ 1 + rayParameter z w ∧
    rayBoundaryPoint z w = w + (1 + rayParameter z w : ℝ) * (z - w) := by
  refine ⟨by linarith [(exercise29_ray_boundary_map hz hw hne).1], ?_⟩
  unfold rayBoundaryPoint
  push_cast
  ring

/-- A continuous disc self-map without a fixed point gives this circle map. -/
noncomputable def discRayMap (f : ComplexDisc → ComplexDisc)
    (hne : ∀ z, f z ≠ z) : ComplexDisc → ComplexUnitCircle := fun z ↦
  ⟨rayBoundaryPoint z (f z),
    (exercise29_ray_boundary_map z.property (f z).property
      (fun h ↦ hne z (Subtype.ext h))).2.2.1⟩

/-- The quadratic coefficients and its positive denominator make the
explicit root continuous. No choice of a root is used. -/
theorem exercise29_ray_map_continuity (f : ComplexDisc → ComplexDisc)
    (hf : Continuous f) (hne : ∀ z, f z ≠ z) : Continuous (discRayMap f hne) := by
  have hc : Continuous (fun z : ComplexDisc ↦ (f z : ℂ)) := continuous_subtype_val.comp hf
  have hA : Continuous (fun z : ComplexDisc ↦ rayA z (f z)) :=
    Complex.continuous_normSq.comp (hc.sub continuous_subtype_val)
  have hB : Continuous (fun z : ComplexDisc ↦ rayB z (f z)) := by
    unfold rayB
    fun_prop
  have hC : Continuous (fun z : ComplexDisc ↦ rayC z) :=
    (Complex.continuous_normSq.comp continuous_subtype_val).sub continuous_const
  have hAn (z : ComplexDisc) : rayA z (f z) ≠ 0 :=
    (ray_coefficients z.property (f z).property
      (fun h ↦ hne z (Subtype.ext h))).1.ne'
  have hs : Continuous (fun z : ComplexDisc ↦ rayParameter z (f z)) :=
    (hB.add (Real.continuous_sqrt.comp ((hB.pow 2).sub (hA.mul hC)))).div hA hAn
  apply Continuous.subtype_mk
  exact continuous_subtype_val.sub ((Complex.continuous_ofReal.comp hs).mul (hc.sub continuous_subtype_val))

/-- At boundary points the unique nonnegative parameter is zero. -/
theorem exercise29_ray_boundary_identity (f : ComplexDisc → ComplexDisc)
    (hne : ∀ z, f z ≠ z) (z : ComplexDisc) (hz : ‖(z : ℂ)‖ = 1) :
    rayParameter z (f z) = 0 ∧ (discRayMap f hne z : ℂ) = (z : ℂ) := by
  have h := exercise29_ray_boundary_map z.property (f z).property
    (fun h ↦ hne z (Subtype.ext h))
  have hs : rayParameter z (f z) = 0 := by
    symm
    apply (h.2.2.2.2 0 le_rfl).mp
    simpa using hz
  exact ⟨hs, by simp [discRayMap, rayBoundaryPoint, hs]⟩

/-- The boundary antipode theorem contradicts the identity boundary values
of the constructed ray map, and gives a fixed point in the closed disc. -/
theorem exercise29_disc_fixed_point (f : ComplexDisc → ComplexDisc)
    (hf : Continuous f) : ∃ z : ComplexDisc, f z = z := by
  by_contra h
  have hne : ∀ z, f z ≠ z := by simpa only [not_exists] using h
  obtain ⟨z, hz, ha⟩ := exercise28_boundary_antipode (discRayMap f hne)
    (exercise29_ray_map_continuity f hf hne)
  rw [(exercise29_ray_boundary_identity f hne z hz).2] at ha
  have hz0 : (z : ℂ) = 0 := by linear_combination (1 / 2 : ℂ) * ha
  simp [hz0] at hz

end Rudin.Chapter08
