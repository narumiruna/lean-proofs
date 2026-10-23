module

public import Math.Rudin.Support.SimplexStokes
public import Mathlib.Analysis.Convex.Combination

/-! # Chapter 10, Exercise 24

The potential is the prescribed affine-segment integral. The increment identity
uses analytic Stokes on the actual affine triangle.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise24
open Set MeasureTheory Filter Topology
open Rudin.Support SimplexIntegration

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev line (x y : V) : ℝ → V := OrientedChains.Parametric.segment x y

/-- The prescribed segment integral, with its actual tangent. -/
def segmentIntegral (ω : PathIntegration.OneForm V) (x y : V) : ℝ :=
  ∫ t in (0 : ℝ)..1, ω (line x y t) (y - x)

/-- The base-point construction in Exercise 24. -/
def potential (ω : PathIntegration.OneForm V) (p : V) : V → ℝ :=
  segmentIntegral ω p

/-- The construction is literally the prescribed segment integral. -/
theorem potential_eq_segmentIntegral (ω : PathIntegration.OneForm V) (p x : V) :
    potential ω p x = segmentIntegral ω p x := rfl

theorem line_mem {U : Set V} (hU : Convex ℝ U) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    line x y t ∈ U :=
  hU hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem line_continuous (x y : V) : Continuous (line x y) := by
  unfold line OrientedChains.Parametric.segment
  fun_prop

theorem segment_coefficient_continuous {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (hc : Convex ℝ U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    ContinuousOn (fun t => ω (line x y t) (y - x)) (Icc (0 : ℝ) 1) :=
  (hω.comp (line_continuous x y).continuousOn (fun _ ht => line_mem hc hx hy ht)).clm_apply
    continuousOn_const

/-- Source Riemann existence, not the default value of an undefined integral. -/
theorem segmentIntegral_source {U : Set V} {ω : PathIntegration.OneForm V}
    (hω : ContinuousOn ω U) (hc : Convex ℝ U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    StieltjesPrototype.HasDarbouxRSIntegral (fun t => ω (line x y t) (y-x)) id 0 1
      (segmentIntegral ω x y) := by
  have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by norm_num : (0 : ℝ) ≤ 1) (segment_coefficient_continuous hω hc hx hy)
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id, segmentIntegral] using h

theorem affine_image_subset {U : Set V} (hc : Convex ℝ U) {n : ℕ}
    (v : Fin (n+1) → V) (hv : ∀ i, v i ∈ U) :
    (SmoothChains.affine v).val '' standardSimplex n ⊆ U := by
  rintro _ ⟨u, hu, rfl⟩
  exact hc.sum_mem (fun i _ => (SmoothChains.mem_simplex_iff_weights u).mp hu i)
    (SmoothChains.sum_weights u) (fun i _ => hv i)

theorem affine_path (x y : V) : (SmoothChains.affine ![x,y]).path = line x y := by
  funext t
  simp [SmoothChains.Simplex.path, SmoothChains.affine, SmoothChains.weights,
    SmoothChains.line, Fin.sum_univ_succ, line, OrientedChains.Parametric.segment]

theorem affine_integral {U : Set V} (hc : Convex ℝ U) {ω : Form 1 V}
    (hω : ContinuousOn ω U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    SmoothChains.integral ω (SmoothChains.simplex (SmoothChains.affine ![x,y])) =
      segmentIntegral (PathIntegration.fromAlternating ω) x y := by
  rw [SmoothChains.integral_eq_pathIntegral ω _
    (hω.mono (affine_image_subset hc _ (by intro i; fin_cases i <;> assumption))),
    affine_path]
  unfold PathIntegration.pathIntegral PathIntegration.coefficient segmentIntegral
  congr 1
  funext t
  rw [(PathIntegration.segment_hasDerivAt x y t).deriv]

/-- The zero exterior integral and the three signed affine faces give the
increment identity. All points, including repeated vertices, are allowed. -/
theorem increment {U : Set V} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : Form 1 V} (hω : ContDiffOn ℝ 1 ω U) (hz : ∀ x ∈ U, extDeriv ω x = 0)
    {p x y : V} (hp : p ∈ U) (hx : x ∈ U) (hy : y ∈ U) :
    potential (PathIntegration.fromAlternating ω) p y -
      potential (PathIntegration.fromAlternating ω) p x =
        segmentIntegral (PathIntegration.fromAlternating ω) x y := by
  let S := SmoothChains.affine ![p,x,y]
  have him : S.val '' standardSimplex 2 ⊆ U :=
    affine_image_subset hc _ (by intro i; fin_cases i <;> assumption)
  have hs := SimplexStokes.smoothChains_stokes ω S ho hω him
  have he : SmoothChains.integral (extDeriv ω) (SmoothChains.simplex S) = 0 := by
    rw [SmoothChains.integral_simplex, simplexIntegral]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    change extDeriv ω (S.val u) _ = 0
    rw [hz _ (him (mem_image_of_mem _ hu))]
    rfl
  rw [he] at hs
  dsimp only [S] at hs
  rw [SmoothChains.boundary_triangle] at hs
  simp only [map_add, map_sub] at hs
  rw [affine_integral hc hω.continuousOn hx hy,
    affine_integral hc hω.continuousOn hp hy,
    affine_integral hc hω.continuousOn hp hx] at hs
  unfold potential
  linarith

/-- Segment increments and continuous coefficients imply a genuine Fréchet
 derivative. This lemma does not assume that the potential is differentiable. -/
theorem hasFDerivAt_of_segment_increment {U : Set V} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) {f : V → ℝ} {x : V}
    (hx : x ∈ U) (hi : ∀ y ∈ U, f y - f x = segmentIntegral ω x y) :
    HasFDerivAt f (ω x) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp (hω.continuousAt (ho.mem_nhds hx)) ε hε
  filter_upwards [ho.mem_nhds hx, Metric.ball_mem_nhds x hδ] with y hy hyd
  rw [hi y hy]
  have hint : IntervalIntegrable (fun t => ω (line x y t) (y-x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using segment_coefficient_continuous hω hc hx hy
  have he : segmentIntegral ω x y - ω x (y-x) =
      ∫ t in (0 : ℝ)..1, (ω (line x y t) - ω x) (y-x) := by
    simp only [sub_apply]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp [segmentIntegral]
  rw [he]
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1, ‖(ω (line x y t) - ω x) (y-x)‖ ≤ ε * ‖y-x‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hl : line x y t - x = t • (y-x) := by
      simp only [line, OrientedChains.Parametric.segment, sub_smul, smul_sub, one_smul]
      abel
    have hd : dist (line x y t) x < δ := by
      rw [dist_eq_norm, hl, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht'.2).trans_lt
        (by simpa [Metric.mem_ball, dist_eq_norm] using hyd)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (by simpa [dist_eq_norm] using (hb hd).le) (norm_nonneg _))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem fromAlternating_continuousOn {U : Set V} {ω : Form 1 V}
    (hω : ContinuousOn ω U) : ContinuousOn (PathIntegration.fromAlternating ω) U :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V)
    (F := ℝ) (0 : Fin 1)).symm.continuous.comp_continuousOn hω

/-- The actual Fréchet derivative of the prescribed segment potential. -/
theorem potential_derivative {U : Set V} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : Form 1 V} (hω : ContDiffOn ℝ 1 ω U) (hz : ∀ x ∈ U, extDeriv ω x = 0)
    {p x : V} (hp : p ∈ U) (hx : x ∈ U) :
    HasFDerivAt (potential (PathIntegration.fromAlternating ω) p)
      (PathIntegration.fromAlternating ω x) x :=
  hasFDerivAt_of_segment_increment ho hc (fromAlternating_continuousOn hω.continuousOn)
    hx (fun _ hy => increment ho hc hω hz hp hx hy)

/-- A continuous field of genuine derivatives gives C¹ regularity. -/
theorem contDiffOn_of_hasFDerivAt {U : Set V} (ho : IsOpen U)
    {ω : PathIntegration.OneForm V} (hω : ContinuousOn ω U) {f : V → ℝ}
    (hd : ∀ x ∈ U, HasFDerivAt f (ω x) x) : ContDiffOn ℝ 1 f U := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  exact ⟨by simp, ω, contDiffOn_zero.mpr hω, fun x hx => (hd x hx).hasFDerivWithinAt⟩

/-- Exactness on every convex open domain, including the empty domain. -/
theorem exactness {U : Set V} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : Form 1 V} (hω : ContDiffOn ℝ 1 ω U) (hz : ∀ x ∈ U, extDeriv ω x = 0) :
    ∃ f : V → ℝ, ContDiffOn ℝ 1 f U ∧
      (∀ x ∈ U, HasFDerivAt f (PathIntegration.fromAlternating ω x) x) ∧
      (∀ x ∈ U, extDeriv (PathIntegration.zeroForm f) x = ω x) ∧
      (∀ p ∈ U, ∀ x ∈ U, f x - f p = segmentIntegral (PathIntegration.fromAlternating ω) p x) := by
  by_cases hne : U.Nonempty
  · obtain ⟨p, hp⟩ := hne
    let f := potential (PathIntegration.fromAlternating ω) p
    have hd : ∀ x ∈ U, HasFDerivAt f (PathIntegration.fromAlternating ω x) x :=
      fun _ hx => potential_derivative ho hc hω hz hp hx
    refine ⟨f, contDiffOn_of_hasFDerivAt ho (fromAlternating_continuousOn hω.continuousOn) hd,
      hd, ?_, fun q hq x hx => increment ho hc hω hz hp hq hx⟩
    intro x hx
    ext v
    have he := PathIntegration.exterior_potential f x (v 0)
    rw [(hd x hx).fderiv] at he
    simpa only [PathIntegration.fromAlternating_apply,
      show (fun _ : Fin 1 => v 0) = v by ext i; fin_cases i; rfl] using he
  · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst U
    exact ⟨fun _ => 0, contDiffOn_const, by simp, by simp, by simp⟩

section Coordinates
variable {n : ℕ}
local notation "R" => EuclideanSpace ℝ (Fin n)

/-- The coefficient of `dxᵢ` in the Euclidean coordinate frame. -/
def coordinate (ω : Form 1 R) (i : Fin n) (x : R) : ℝ :=
  PathIntegration.fromAlternating ω x (EuclideanSpace.single i 1)

theorem coordinate_expansion (ω : Form 1 R) (x v : R) :
    PathIntegration.fromAlternating ω x v = ∑ i, v i * coordinate ω i x := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i 1 := by
    ext j
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, coordinate]

/-- The coordinate formula in the source, with actual integrable coefficients. -/
theorem increment_formula {U : Set R} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : Form 1 R} (hω : ContDiffOn ℝ 1 ω U) (hz : ∀ x ∈ U, extDeriv ω x = 0)
    {p x y : R} (hp : p ∈ U) (hx : x ∈ U) (hy : y ∈ U) :
    potential (PathIntegration.fromAlternating ω) p y -
      potential (PathIntegration.fromAlternating ω) p x =
        ∑ i, (y i - x i) * ∫ t in (0 : ℝ)..1, coordinate ω i (line x y t) := by
  rw [increment ho hc hω hz hp hx hy, segmentIntegral]
  simp_rw [coordinate_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    rfl
  · intro i _
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    have h := ((fromAlternating_continuousOn hω.continuousOn).comp
      (line_continuous x y).continuousOn (fun _ ht => line_mem hc hx hy ht)).clm_apply
        (continuousOn_const (c := EuclideanSpace.single i 1))
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), coordinate, Function.comp_apply] using h

/-- Coordinate directional derivatives exist, and equal the prescribed coefficients. -/
theorem coordinate_derivative {U : Set R} (ho : IsOpen U) (hc : Convex ℝ U)
    {ω : Form 1 R} (hω : ContDiffOn ℝ 1 ω U) (hz : ∀ x ∈ U, extDeriv ω x = 0)
    {p x : R} (hp : p ∈ U) (hx : x ∈ U) (i : Fin n) :
    HasDerivAt (fun t : ℝ => potential (PathIntegration.fromAlternating ω) p
      (x + t • EuclideanSpace.single i 1)) (coordinate ω i x) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) 0 := by
    simpa only [Pi.add_def, zero_add, one_smul, id_eq] using!
      (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i 1))
  have hd : HasFDerivAt (potential (PathIntegration.fromAlternating ω) p)
      (PathIntegration.fromAlternating ω x) (x + (0 : ℝ) • EuclideanSpace.single i 1) := by
    simpa only [zero_smul, add_zero] using potential_derivative ho hc hω hz hp hx
  exact hd.comp_hasDerivAt (0 : ℝ) hl

end Coordinates
end Rudin.Chapter10.Exercise24
