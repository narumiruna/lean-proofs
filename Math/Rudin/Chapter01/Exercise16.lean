module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Tactic

/-!
# R01E16: equal-radius sphere intersections

Source: Rudin, book page 23 (PDF page 32).
All norms are Euclidean norms. The midpoint bridge identifies the locus
with a sphere in the orthogonal complement of the line of centers.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The midpoint of the centers, written using vector operations. -/
noncomputable def exercise16_midpoint {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :=
  (1 / 2 : ℝ) • (x + y)

/-- The source locus is a sphere in the perpendicular bisector hyperplane.
The squared radius is `r² - ‖y-x‖²/4`. -/
theorem exercise16_bridge {k : ℕ} (x y z : EuclideanSpace ℝ (Fin k))
    {r : ℝ} (hr : 0 ≤ r) :
    (‖z - x‖ = r ∧ ‖z - y‖ = r) ↔
      inner ℝ (y - x) (z - exercise16_midpoint x y) = 0 ∧
      ‖z - exercise16_midpoint x y‖ ^ 2 = r ^ 2 - ‖y - x‖ ^ 2 / 4 := by
  have h₁ : z - x = (z - exercise16_midpoint x y) + (1 / 2 : ℝ) • (y - x) := by
    unfold exercise16_midpoint
    module
  have h₂ : z - y = (z - exercise16_midpoint x y) - (1 / 2 : ℝ) • (y - x) := by
    unfold exercise16_midpoint
    module
  have he₁ : ‖z - x‖ ^ 2 = ‖z - exercise16_midpoint x y‖ ^ 2 +
      ‖y - x‖ ^ 2 / 4 + inner ℝ (y - x) (z - exercise16_midpoint x y) := by
    rw [h₁, norm_add_sq_real]
    simp [norm_smul, inner_smul_right, real_inner_comm]
    ring
  have he₂ : ‖z - y‖ ^ 2 = ‖z - exercise16_midpoint x y‖ ^ 2 +
      ‖y - x‖ ^ 2 / 4 - inner ℝ (y - x) (z - exercise16_midpoint x y) := by
    rw [h₂, norm_sub_sq_real]
    simp [norm_smul, inner_smul_right, real_inner_comm]
    ring
  constructor
  · rintro ⟨hx, hy⟩
    rw [hx] at he₁
    rw [hy] at he₂
    constructor <;> nlinarith
  · rintro ⟨hi, hn⟩
    constructor
    · apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
      nlinarith
    · apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
      nlinarith

/-- No intersection when the diameter is smaller than the distance of the centers,
in every dimension. -/
theorem exercise16_c {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (h : 2 * r < ‖x - y‖) :
    ¬ ∃ z : EuclideanSpace ℝ (Fin k), ‖z - x‖ = r ∧ ‖z - y‖ = r := by
  rintro ⟨z, hx, hy⟩
  have ht := norm_sub_le (x - z) (y - z)
  have he : (x - z) - (y - z) = x - y := by abel
  rw [he, norm_sub_rev x z, hx, norm_sub_rev y z, hy] at ht
  linarith

/-- At tangency the midpoint is the unique point, in every dimension. -/
theorem exercise16_b {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) {r : ℝ}
    (hr : 0 ≤ r) (h : 2 * r = ‖x - y‖) :
    ∃! z : EuclideanSpace ℝ (Fin k), ‖z - x‖ = r ∧ ‖z - y‖ = r := by
  have hsq : r ^ 2 - ‖y - x‖ ^ 2 / 4 = 0 := by
    rw [norm_sub_rev y x, ← h]
    ring
  refine ⟨exercise16_midpoint x y, ?_, ?_⟩
  · apply (exercise16_bridge x y _ hr).mpr
    simp [hsq]
  · intro z hz
    have hn := ((exercise16_bridge x y z hr).mp hz).2
    rw [hsq, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hn
    exact hn

/-- The perpendicular bisector description as an image of an actual Euclidean
sphere in a subspace. This supplies the bridge used for the cardinality results. -/
theorem exercise16_sphere_image {k : ℕ} (x y : EuclideanSpace ℝ (Fin k))
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsq : s ^ 2 = r ^ 2 - ‖y - x‖ ^ 2 / 4) :
    {z | ‖z - x‖ = r ∧ ‖z - y‖ = r} =
      (fun u : (ℝ ∙ (y - x))ᗮ => exercise16_midpoint x y + u.val) ''
        Metric.sphere 0 s := by
  ext z
  constructor
  · intro hz
    obtain ⟨hi, hn⟩ := (exercise16_bridge x y z hr).mp hz
    let u : (ℝ ∙ (y - x))ᗮ := ⟨z - exercise16_midpoint x y,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hi⟩
    refine ⟨u, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      apply (sq_eq_sq₀ (norm_nonneg _) hs).mp
      exact hn.trans hsq.symm
    · dsimp [u]
      abel
  · rintro ⟨u, hu, rfl⟩
    apply (exercise16_bridge x y _ hr).mpr
    have hu' : ‖u.val‖ = s := by simpa using hu
    simp only [add_sub_cancel_left]
    exact ⟨Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.property,
      by rw [hu', hsq]⟩

private theorem exercise16_perp_finrank {k : ℕ} (hk : 1 ≤ k)
    (x y : EuclideanSpace ℝ (Fin k)) (hxy : x ≠ y) :
    Module.finrank ℝ (ℝ ∙ (y - x))ᗮ = k - 1 := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1) :=
    ⟨by simp only [finrank_euclideanSpace_fin]; omega⟩
  exact Submodule.finrank_orthogonal_span_singleton (sub_ne_zero.mpr hxy.symm)

private theorem exercise16_radius_pos {k : ℕ} (x y : EuclideanSpace ℝ (Fin k))
    {r : ℝ} (h : ‖x - y‖ < 2 * r) :
    0 < r ^ 2 - ‖y - x‖ ^ 2 / 4 := by
  rw [norm_sub_rev y x]
  have hn := norm_nonneg (x - y)
  nlinarith

/-- Above tangency, there are at least two distinct points in dimension at least two. -/
theorem exercise16_two_points {k : ℕ} (hk : 2 ≤ k)
    (x y : EuclideanSpace ℝ (Fin k)) (hxy : x ≠ y) {r : ℝ}
    (h : ‖x - y‖ < 2 * r) :
    ∃ p q : EuclideanSpace ℝ (Fin k), p ≠ q ∧
      (‖p - x‖ = r ∧ ‖p - y‖ = r) ∧ (‖q - x‖ = r ∧ ‖q - y‖ = r) := by
  let K := (ℝ ∙ (y - x))ᗮ
  have hd : Module.finrank ℝ K = k - 1 := exercise16_perp_finrank (by omega) x y hxy
  have : Nontrivial K := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ K)
  let s := Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2 / 4)
  have hs : 0 < s := Real.sqrt_pos.mpr (exercise16_radius_pos x y h)
  have hsq : s ^ 2 = r ^ 2 - ‖y - x‖ ^ 2 / 4 := Real.sq_sqrt (le_of_lt (exercise16_radius_pos x y h))
  obtain ⟨u, hu⟩ := exists_norm_eq K hs.le
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu; linarith
  have hr : 0 ≤ r := by have := norm_nonneg (x - y); linarith
  have himage := exercise16_sphere_image x y hr hs.le hsq
  let f : K → EuclideanSpace ℝ (Fin k) := fun v => exercise16_midpoint x y + v.val
  have hf : Function.Injective f := by
    intro u v huv
    exact Subtype.ext (add_left_cancel huv)
  have hup : f u ∈ {z | ‖z - x‖ = r ∧ ‖z - y‖ = r} := by
    rw [himage]
    exact ⟨u, by simpa using hu, rfl⟩
  have hum : f (-u) ∈ {z | ‖z - x‖ = r ∧ ‖z - y‖ = r} := by
    rw [himage]
    exact ⟨-u, by simpa using hu, rfl⟩
  refine ⟨f u, f (-u), ?_, hup, hum⟩
  intro he
  have he' := hf he
  have h2 : (2 : ℝ) • u = 0 := by
    rw [two_smul]
    nth_rw 1 [he']
    exact neg_add_cancel u
  exact hu0 ((smul_eq_zero.mp h2).resolve_left (by norm_num))

/-- In dimension two, above tangency the locus consists of exactly two points. -/
theorem exercise16_dimension_two_gt (x y : EuclideanSpace ℝ (Fin 2))
    (hxy : x ≠ y) {r : ℝ} (h : ‖x - y‖ < 2 * r) :
    ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
      ∀ z, (‖z - x‖ = r ∧ ‖z - y‖ = r) ↔ z = p ∨ z = q := by
  obtain ⟨p, q, hpq, hp, hq⟩ := exercise16_two_points (by decide) x y hxy h
  refine ⟨p, q, hpq, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (by simp) hxy hpq
      (by simpa [dist_eq_norm] using hp.1) (by simpa [dist_eq_norm] using hq.1)
      (by simpa [dist_eq_norm] using hz.1) (by simpa [dist_eq_norm] using hp.2)
      (by simpa [dist_eq_norm] using hq.2) (by simpa [dist_eq_norm] using hz.2)
  · rintro (rfl | rfl) <;> assumption

/-- In dimension at least three, above tangency there are infinitely many points. -/
theorem exercise16_a {k : ℕ} (hk : 3 ≤ k)
    (x y : EuclideanSpace ℝ (Fin k)) (hxy : x ≠ y) {r : ℝ}
    (h : ‖x - y‖ < 2 * r) :
    {z : EuclideanSpace ℝ (Fin k) | ‖z - x‖ = r ∧ ‖z - y‖ = r}.Infinite := by
  let K := (ℝ ∙ (y - x))ᗮ
  have hd : Module.finrank ℝ K = k - 1 := exercise16_perp_finrank (by omega) x y hxy
  have : Nontrivial K := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ K)
  have hdim : 1 < Module.rank ℝ K := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ K by omega)
  let s := Real.sqrt (r ^ 2 - ‖y - x‖ ^ 2 / 4)
  have hs : 0 < s := Real.sqrt_pos.mpr (exercise16_radius_pos x y h)
  have hsq : s ^ 2 = r ^ 2 - ‖y - x‖ ^ 2 / 4 := Real.sq_sqrt (le_of_lt (exercise16_radius_pos x y h))
  obtain ⟨u, hu⟩ := exists_norm_eq K hs.le
  have hne : u ≠ -u := by
    intro he
    have h2 : (2 : ℝ) • u = 0 := by
      rw [two_smul]
      nth_rw 1 [he]
      exact neg_add_cancel u
    have hu0 : u = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    simp [hu0] at hu
    linarith
  have hn : (Metric.sphere (0 : K) s).Nontrivial :=
    ⟨u, by simpa using hu, -u, by simpa using hu, hne⟩
  have hi := (isPreconnected_sphere hdim (0 : K) s).infinite_of_nontrivial hn
  have hr : 0 ≤ r := by have := norm_nonneg (x - y); linarith
  rw [exercise16_sphere_image x y hr hs.le hsq]
  apply hi.image
  intro u hu v hv he
  exact Subtype.ext (add_left_cancel he)

/-- In dimension one, intersection is possible exactly at tangency.
Together with `exercise16_b`, this gives the counts zero, one, zero. -/
theorem exercise16_dimension_one (x y : EuclideanSpace ℝ (Fin 1))
    (hxy : x ≠ y) {r : ℝ} (hr : 0 ≤ r) :
    (∃ z : EuclideanSpace ℝ (Fin 1), ‖z - x‖ = r ∧ ‖z - y‖ = r) ↔
      2 * r = ‖x - y‖ := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hi, hn⟩ := (exercise16_bridge x y z hr).mp hz
    have hK : (ℝ ∙ (y - x))ᗮ = ⊥ := Submodule.finrank_eq_zero.mp
      (by simpa using exercise16_perp_finrank (by decide) x y hxy)
    have hm : z - exercise16_midpoint x y = 0 := by
      have hm := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hi
      rwa [hK, Submodule.mem_bot] at hm
    rw [hm, norm_zero, zero_pow (by decide : 2 ≠ 0), norm_sub_rev y x] at hn
    have hd := norm_nonneg (x - y)
    nlinarith
  · intro h
    exact (exercise16_b x y hr h).exists

/-- Complete two-dimensional classification: two points, one point, no points,
according as the diameter is greater than, equal to, or less than the separation. -/
theorem exercise16_dimension_two (x y : EuclideanSpace ℝ (Fin 2))
    (hxy : x ≠ y) {r : ℝ} (hr : 0 < r) :
    (‖x - y‖ < 2 * r → ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
      ∀ z, (‖z - x‖ = r ∧ ‖z - y‖ = r) ↔ z = p ∨ z = q) ∧
    (2 * r = ‖x - y‖ → ∃! z : EuclideanSpace ℝ (Fin 2),
      ‖z - x‖ = r ∧ ‖z - y‖ = r) ∧
    (2 * r < ‖x - y‖ → ¬ ∃ z : EuclideanSpace ℝ (Fin 2),
      ‖z - x‖ = r ∧ ‖z - y‖ = r) :=
  ⟨exercise16_dimension_two_gt x y hxy, exercise16_b x y hr.le, exercise16_c x y⟩

/-- Complete one-dimensional classification: no points, one point, no points. -/
theorem exercise16_dimension_one_cases (x y : EuclideanSpace ℝ (Fin 1))
    (hxy : x ≠ y) {r : ℝ} (hr : 0 < r) :
    (‖x - y‖ < 2 * r → ¬ ∃ z : EuclideanSpace ℝ (Fin 1),
      ‖z - x‖ = r ∧ ‖z - y‖ = r) ∧
    (2 * r = ‖x - y‖ → ∃! z : EuclideanSpace ℝ (Fin 1),
      ‖z - x‖ = r ∧ ‖z - y‖ = r) ∧
    (2 * r < ‖x - y‖ → ¬ ∃ z : EuclideanSpace ℝ (Fin 1),
      ‖z - x‖ = r ∧ ‖z - y‖ = r) := by
  refine ⟨?_, exercise16_b x y hr.le, exercise16_c x y⟩
  intro h hz
  have he := (exercise16_dimension_one x y hxy hr.le).mp hz
  linarith

end Rudin.Chapter01
