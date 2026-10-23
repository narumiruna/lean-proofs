module

public import Math.Rudin.Chapter10.Exercise25
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Chapter 10, Exercise 26

The radial cone of a C² loop has Hausdorff dimension at most two. Its complement
in Euclidean three-space is dense. A point outside the cone gives an actual
straight contraction avoiding zero. Two affine parameter triangles and analytic
Stokes give zero periods. Exercise 25 then constructs a global potential.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise26
open Set MeasureTheory Filter Topology
open Rudin.Support SimplexIntegration SmoothChains OrientedChains.Parametric

abbrev R3 := EuclideanSpace ℝ (Fin 3)
def puncturedSpace : Set R3 := {x | x ≠ 0}

/-- Analytic Stokes on a full C² triangle whose image stays in the form domain. -/
theorem closed_triangle_boundary {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ω : Form 1 V) (S : SmoothChains.Simplex 2 V)
    {U : Set V} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (him : S.val '' standardSimplex 2 ⊆ U) (hz : ∀ x ∈ U, extDeriv ω x = 0) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating ω)
      (toPaths (boundary 1 (simplex S))) = 0 := by
  have he : SmoothChains.integral (extDeriv ω) (simplex S) = 0 := by
    rw [SmoothChains.integral_simplex, simplexIntegral]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    change extDeriv ω (S.val u) _ = 0
    rw [hz _ (him (mem_image_of_mem _ hu))]
    rfl
  have hs := SimplexStokes.smoothChains_stokes ω S hU hω him
  rw [he] at hs
  rw [hs]
  simp only [boundary_simplex, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [toPaths_simplex, PathIntegration.chainIntegral_path]
  apply (integral_eq_pathIntegral ω (S.face i) _).symm
  apply hω.continuousOn.mono
  rintro y ⟨u,hu,rfl⟩
  exact him ⟨relabel i.succAbove u, relabel_mem _ hu, rfl⟩

/-- Closed-square Stokes obtained from two actual mapped affine triangles.
 Only the form's open domain, not the whole ambient space, needs regularity. -/
theorem closed_square_boundary {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ω : Form 1 V) (S : (ℝ × ℝ) → V) (hS : ContDiff ℝ 2 S)
    {U : Set V} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (him : MapsTo S (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) U)
    (hz : ∀ x ∈ U, extDeriv ω x = 0) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating ω)
      (surfaceBoundary (surface S)) = 0 := by
  let A := affine ![((0,0) : ℝ × ℝ),(1,0),(1,1)]
  let B := affine ![((0,0) : ℝ × ℝ),(0,1),(1,1)]
  have hA : ∀ u ∈ standardSimplex 2, A.val u ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← square_coverage]
    exact Or.inl (mem_image_of_mem _ hu)
  have hB : ∀ u ∈ standardSimplex 2, B.val u ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← square_coverage]
    exact Or.inr (mem_image_of_mem _ hu)
  have ha := closed_triangle_boundary ω (A.map S hS) hU hω
    (by rintro _ ⟨u,hu,rfl⟩; exact him (hA u hu)) hz
  have hb := closed_triangle_boundary ω (B.map S hS) hU hω
    (by rintro _ ⟨u,hu,rfl⟩; exact him (hB u hu)) hz
  rw [← triangulate_boundary S hS]
  simp only [triangulate, squareParameters, square, map_sub, map_simplex]
  exact sub_eq_zero.mpr (ha.trans hb.symm)

/-- The full radial cone map has two-dimensional source. -/
def radialCone (γ : ℝ → R3) (u : ℝ × ℝ) : R3 := u.1 • γ u.2

/-- Mathlib's dimension theorem supplies a point outside the entire radial cone.
 No star-shapedness of punctured three-space is assumed. -/
theorem exists_cone_avoiding_point {γ : ℝ → R3} (hγ : ContDiff ℝ 2 γ) :
    ∃ q : R3, ∀ (s t : ℝ), q ≠ s • γ t := by
  have hc : ContDiff ℝ 2 (radialCone γ) :=
    contDiff_fst.smul (hγ.comp contDiff_snd)
  have hd : Differentiable ℝ (radialCone γ) := hc.differentiable (by norm_num)
  have hh := hd.dense_compl_range_of_finrank_lt_finrank (by
    norm_num [Module.finrank_prod] : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ R3)
  obtain ⟨q, hq⟩ := hh.nonempty
  refine ⟨q, fun s t he => hq ?_⟩
  exact ⟨(s,t), he.symm⟩

/-- The contraction is a literal full parameter map. -/
def coneSquare (γ : ℝ → R3) (q : R3) (u : ℝ × ℝ) : R3 :=
  (1-u.2) • γ u.1 + u.2 • q

theorem coneSquare_smooth {γ : ℝ → R3} (hγ : ContDiff ℝ 2 γ) (q : R3) :
    ContDiff ℝ 2 (coneSquare γ q) := by
  exact ((contDiff_const.sub contDiff_snd).smul (hγ.comp contDiff_fst)).add
    (contDiff_snd.smul contDiff_const)

/-- Avoiding the radial cone prevents the whole contraction from meeting zero. -/
theorem coneSquare_avoids_zero {γ : ℝ → R3} {q : R3}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) (hq : ∀ s t : ℝ, q ≠ s • γ t) :
    MapsTo (coneSquare γ q) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) puncturedSpace := by
  intro u hu he
  change (1-u.2) • γ u.1 + u.2 • q = 0 at he
  by_cases ht : u.2 = 0
  · exact hγ u.1 hu.1 (by simpa [ht] using he)
  · apply hq (-(1-u.2)/u.2) u.1
    have h : u.2 • q = -(1-u.2) • γ u.1 := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_right he
    have hh := congrArg (fun v : R3 => u.2⁻¹ • v) h
    simpa [smul_smul, ht, div_eq_mul_inv, mul_comm] using hh

/-- Every closed path used by the component construction has zero period.
 These paths are C², so the Stokes regularity hypothesis is met exactly. -/
theorem flat_periods {ω : Form 1 R3} (hω : ContDiffOn ℝ 1 ω puncturedSpace)
    (hz : ∀ x ∈ puncturedSpace, extDeriv ω x = 0) :
    Exercise25.FlatClosedIntegralsVanish (PathIntegration.fromAlternating ω) puncturedSpace := by
  intro x γ
  obtain ⟨q,hq⟩ := exists_cone_avoiding_point γ.smooth
  have hs := closed_square_boundary ω (coneSquare γ.toFun q) (coneSquare_smooth γ.smooth q)
    isOpen_ne hω (coneSquare_avoids_zero (fun t _ => γ.image t) hq) hz
  have hbot : (fun t => coneSquare γ.toFun q (t,0)) = γ.toFun := by
    funext t; simp [coneSquare]
  have htop : (fun t => coneSquare γ.toFun q (t,1)) = fun _ => q := by
    funext t; simp [coneSquare]
  have hside : (fun t => coneSquare γ.toFun q (1,t)) =
      fun t => coneSquare γ.toFun q (0,t) := by
    funext t; simp [coneSquare, γ.at_zero, γ.at_one]
  rw [surfaceBoundary_surface, hside] at hs
  simp only [map_sub, map_add, PathIntegration.chainIntegral_path] at hs
  rw [hbot, htop, PathIntegration.pathIntegral_constant] at hs
  change PathIntegration.pathIntegral (PathIntegration.fromAlternating ω) γ.toFun = 0
  linarith

/-- Global exactness of every C¹ closed one-form on punctured Euclidean R³. -/
theorem exactness {ω : Form 1 R3} (hω : ContDiffOn ℝ 1 ω puncturedSpace)
    (hz : ∀ x ∈ puncturedSpace, extDeriv ω x = 0) :
    ∃ f : R3 → ℝ, ContDiffOn ℝ 1 f puncturedSpace ∧
      (∀ x ≠ 0, HasFDerivAt f (PathIntegration.fromAlternating ω x) x) ∧
      ∀ x ≠ 0, extDeriv (PathIntegration.zeroForm f) x = ω x := by
  exact ⟨Exercise25.potential (PathIntegration.fromAlternating ω) puncturedSpace,
    Exercise25.exactness_of_flat_closed isOpen_ne hω.continuousOn (flat_periods hω hz)⟩

/-- The conclusion also gives zero periods on every closed C¹ curve, including
 curves with only one-sided endpoint derivatives. No C¹ cone is sent to C² Stokes. -/
theorem closed_c1_periods {ω : Form 1 R3} (hω : ContDiffOn ℝ 1 ω puncturedSpace)
    (hz : ∀ x ∈ puncturedSpace, extDeriv ω x = 0) :
    Exercise25.ClosedIntegralsVanish (PathIntegration.fromAlternating ω) puncturedSpace := by
  intro γ hγ
  have h := Exercise25.curve_integral_of_flat_closed isOpen_ne
    (Exercise24.fromAlternating_continuousOn hω.continuousOn) (flat_periods hω hz) γ
  rw [hγ, sub_self] at h
  exact h

end Rudin.Chapter10.Exercise26
