module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Chapter 7, Exercise 21
Complex polynomial restrictions separate points of the unit circle and vanish
at no point. Conjugation is at uniform distance at least one from every such
restriction, so it is not in their uniform closure.

Source: book page 169, PDF page 178. We use the maximum modulus principle on
`z * p.eval z - 1` instead of the suggested integral.
-/

@[expose] public section

open Set Metric Polynomial

namespace Rudin.Chapter07

noncomputable section

/-- The complex unit circle, with its subspace topology. -/
def exercise21_circle : Set ℂ := sphere 0 1

instance exercise21_circle_compactSpace : CompactSpace exercise21_circle :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) 1)

/-- The algebra of restrictions of complex polynomials, not polynomials in
both `z` and its conjugate. -/
def exercise21_algebra : Subalgebra ℂ C(exercise21_circle, ℂ) :=
  polynomialFunctions exercise21_circle

/-- The source set `A`, as a subset of continuous complex-valued functions. -/
def exercise21_A : Set C(exercise21_circle, ℂ) := exercise21_algebra

/-- Membership means equality with an actual complex polynomial restriction. -/
theorem exercise21_mem_iff (f : C(exercise21_circle, ℂ)) :
    f ∈ exercise21_A ↔ ∃ p : ℂ[X], ∀ z : exercise21_circle, f z = p.eval (z : ℂ) := by
  change f ∈ (polynomialFunctions exercise21_circle : Set _) ↔ _
  rw [polynomialFunctions_coe]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, fun _ => rfl⟩
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    ext z
    exact (hp z).symm

/-- The coordinate polynomial `X` separates any two distinct points. -/
theorem exercise21_point_separation (x y : exercise21_circle) (hxy : x ≠ y) :
    ∃ f ∈ exercise21_A, f x ≠ f y := by
  refine ⟨Polynomial.X.toContinuousMapOn exercise21_circle, ?_, ?_⟩
  · exact (exercise21_mem_iff _).2 ⟨Polynomial.X, fun _ => rfl⟩
  · simpa using (show (x : ℂ) ≠ (y : ℂ) from fun h => hxy (Subtype.ext h))

/-- The constant polynomial one is nonzero at every point. -/
theorem exercise21_nonvanishing (z : exercise21_circle) :
    ∃ f ∈ exercise21_A, f z ≠ 0 := by
  refine ⟨(1 : ℂ[X]).toContinuousMapOn exercise21_circle, ?_, ?_⟩
  · exact (exercise21_mem_iff _).2 ⟨1, fun _ => rfl⟩
  · simp

/-- The explicit continuous function that cannot be uniformly approximated. -/
def exercise21_conjugation : C(exercise21_circle, ℂ) :=
  ⟨fun z => star (z : ℂ), continuous_star.comp continuous_subtype_val⟩

/-- Maximum modulus on the disk gives a uniform separation of at least one. -/
theorem exercise21_uniform_separation (p : ℂ[X]) :
    1 ≤ ‖p.toContinuousMapOn exercise21_circle - exercise21_conjugation‖ := by
  have hd : Differentiable ℂ (fun z : ℂ => z * p.eval z - 1) :=
    (differentiable_id.mul p.differentiable).sub_const 1
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball (0 : ℂ) 1) isBounded_ball hd.diffContOnCl
    (C := ‖p.toContinuousMapOn exercise21_circle - exercise21_conjugation‖)
    (fun z hz => ?_) (z := 0) (subset_closure (by simp))
  · simpa using h
  · have hz' : ‖z‖ = 1 := by
      simpa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz
    have hzK : z ∈ exercise21_circle := by
      simpa [exercise21_circle] using hz'
    have hconj : z * star z = 1 := by
      simpa [hz'] using Complex.mul_conj' z
    have he : z * p.eval z - 1 = z * (p.eval z - star z) := by
      rw [mul_sub, hconj]
    rw [he, norm_mul, hz', one_mul]
    exact ContinuousMap.norm_coe_le_norm
      (p.toContinuousMapOn exercise21_circle - exercise21_conjugation) ⟨z, hzK⟩

/-- The same positive lower bound holds throughout the uniform closure.
The norm topology on continuous maps from this compact circle is uniform. -/
theorem exercise21_closure_separation {f : C(exercise21_circle, ℂ)}
    (hf : f ∈ closure exercise21_A) :
    1 ≤ ‖f - exercise21_conjugation‖ := by
  have hc : IsClosed {f : C(exercise21_circle, ℂ) |
      1 ≤ ‖f - exercise21_conjugation‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  apply closure_minimal (t := {f : C(exercise21_circle, ℂ) |
    1 ≤ ‖f - exercise21_conjugation‖}) ?_ hc hf
  intro g hg
  obtain ⟨p, hp⟩ := (exercise21_mem_iff g).1 hg
  have he : g = p.toContinuousMapOn exercise21_circle := by
    ext z
    exact hp z
  simpa [he] using exercise21_uniform_separation p

/-- Conjugation is an explicit continuous function outside the uniform closure. -/
theorem exercise21_not_dense : exercise21_conjugation ∉ closure exercise21_A := by
  intro h
  have := exercise21_closure_separation h
  norm_num at this

end

end Rudin.Chapter07
