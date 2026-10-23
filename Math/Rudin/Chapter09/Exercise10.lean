module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R09E10: independence of the first coordinate

Source: Rudin, Third Edition, Exercise 9.10, book page 239 (PDF page 248).
The dimension is `n + 1`, so that a first coordinate exists. The weaker domain
condition is connectedness of each parallel coordinate fiber. Derivative
hypotheses are `HasDerivAt`, not values of the total function `deriv`.
-/

@[expose] public section
namespace Rudin.Chapter09

/-- Replace the first coordinate, leaving all other coordinates unchanged. -/
def firstCoordinateLine {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) 0 t)

@[simp] theorem firstCoordinateLine_self {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) : firstCoordinateLine x (x 0) = x := by
  simp [firstCoordinateLine]

@[simp] theorem firstCoordinateLine_twice {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (s t : ℝ) :
    firstCoordinateLine (firstCoordinateLine x s) t = firstCoordinateLine x t := by
  simp [firstCoordinateLine, Function.update_idem]

theorem continuous_firstCoordinateLine {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) : Continuous (firstCoordinateLine x) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_const.update 0 continuous_id)

/-- Connected horizontal fibers suffice; global convexity is not needed. -/
theorem exercise10_weaker_condition {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hE : IsOpen E)
    (hfiber : ∀ x, IsPreconnected (firstCoordinateLine x ⁻¹' E))
    (hf : ∀ x ∈ E, HasDerivAt (fun t => f (firstCoordinateLine x t)) 0 (x 0))
    {x y : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : ∀ i, i ≠ 0 → x i = y i) : f x = f y := by
  have heq : firstCoordinateLine x (y 0) = y := by
    ext i
    by_cases hi : i = 0
    · subst i; simp [firstCoordinateLine]
    · simp [firstCoordinateLine, Function.update_of_ne hi, hxy i hi]
  have hd : ∀ t ∈ firstCoordinateLine x ⁻¹' E,
      HasDerivAt (fun t => f (firstCoordinateLine x t)) 0 t := by
    intro t ht
    simpa [firstCoordinateLine] using hf (firstCoordinateLine x t) ht
  have h := (hE.preimage (continuous_firstCoordinateLine x)).is_const_of_deriv_eq_zero
    (hfiber x) (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) (x := x 0) (y := y 0)
    (by simpa using hx) (by simpa [heq] using hy)
  simpa [heq] using h

/-- A convex open domain has connected horizontal fibers. -/
theorem exercise10 {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hE : IsOpen E) (hconv : Convex ℝ E)
    (hf : ∀ x ∈ E, HasDerivAt (fun t => f (firstCoordinateLine x t)) 0 (x 0))
    {x y : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : ∀ i, i ≠ 0 → x i = y i) : f x = f y := by
  apply exercise10_weaker_condition hE _ hf hx hy hxy
  intro z
  apply Convex.isPreconnected
  intro a ha b hb c d hc hd hcd
  have heq : firstCoordinateLine z (c • a + d • b) =
      c • firstCoordinateLine z a + d • firstCoordinateLine z b := by
    ext i
    by_cases hi : i = 0
    · subst i; simp [firstCoordinateLine]
    · simp [firstCoordinateLine, Function.update_of_ne hi, ← add_mul, hcd]
  change firstCoordinateLine z (c • a + d • b) ∈ E
  rw [heq]
  exact hconv ha hb hc hd hcd

/-- An open planar domain with two horizontal components. -/
def splitHorizontalDomain : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 ≠ 0}

/-- The function distinguishes the two components. -/
noncomputable def splitHorizontalFunction (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if 0 < x 0 then 1 else 0

/-- The domain assumption cannot be omitted, even for an open planar set.
The two points have the same second coordinate, but different function values. -/
theorem exercise10_domain_counterexample :
    IsOpen splitHorizontalDomain ∧
    (∀ x ∈ splitHorizontalDomain,
      HasDerivAt (fun t => splitHorizontalFunction (firstCoordinateLine x t)) 0 (x 0)) ∧
    ∃ x ∈ splitHorizontalDomain, ∃ y ∈ splitHorizontalDomain,
      x 1 = y 1 ∧ splitHorizontalFunction x ≠ splitHorizontalFunction y := by
  refine ⟨isOpen_ne_fun (PiLp.continuous_apply 2 _ 0) continuous_const, ?_, ?_⟩
  · intro x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · apply (hasDerivAt_const (x 0) (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hx] with t ht
      simp [splitHorizontalFunction, firstCoordinateLine, not_lt.mpr ht.le]
    · apply (hasDerivAt_const (x 0) (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with t ht
      simp [splitHorizontalFunction, firstCoordinateLine, ht]
  · refine ⟨WithLp.toLp 2 ![-1, 0], ?_, WithLp.toLp 2 ![1, 0], ?_, ?_, ?_⟩ <;>
      norm_num [splitHorizontalDomain, splitHorizontalFunction]

/-- Connected horizontal fibers are strictly weaker than convexity:
the complement of the horizontal axis has full or empty horizontal fibers. -/
theorem exercise10_weaker_not_convex :
    ∃ E : Set (EuclideanSpace ℝ (Fin 2)), IsOpen E ∧
      (∀ x, IsPreconnected (firstCoordinateLine x ⁻¹' E)) ∧ ¬ Convex ℝ E := by
  let E : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 1 ≠ 0}
  refine ⟨E, isOpen_ne_fun (PiLp.continuous_apply 2 _ 1) continuous_const, ?_, ?_⟩
  · intro x
    by_cases hx : x 1 = 0
    · have he : firstCoordinateLine x ⁻¹' E = ∅ := by
        ext t; simp [E, firstCoordinateLine, hx]
      rw [he]; exact isPreconnected_empty
    · have he : firstCoordinateLine x ⁻¹' E = Set.univ := by
        ext t; simp [E, firstCoordinateLine, hx]
      rw [he]; exact isPreconnected_univ
  · intro hc
    have h := hc (x := WithLp.toLp 2 ![0, -1]) (y := WithLp.toLp 2 ![0, 1])
      (by norm_num [E]) (by norm_num [E])
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    norm_num [E, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply] at h

end Rudin.Chapter09
