module

public import Mathlib
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Chapter 7, Exercise 24
The completion is the closure of the specified distance-difference functions
in bounded continuous complex-valued functions. No separability is required.
Source: book page 170, PDF page 179.
-/

@[expose] public section

open Set Topology
open scoped BoundedContinuousFunction

namespace Rudin.Chapter07

noncomputable section

variable {X : Type*} [MetricSpace X]

/-- The exact function in the source, embedded into `ℂ`. -/
def exercise24Function (a p x : X) : ℂ := (dist x p - dist x a : ℝ)

theorem exercise24_pointwise_bound (a p x : X) :
    ‖exercise24Function a p x‖ ≤ dist a p := by
  change ‖((dist x p - dist x a : ℝ) : ℂ)‖ ≤ dist a p
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [dist_comm p x, dist_comm a x, dist_comm p a] using
    abs_dist_sub_le p a x

theorem exercise24_continuous (a p : X) : Continuous (exercise24Function a p) := by
  unfold exercise24Function
  fun_prop

/-- Membership in the actual supremum-norm function space. -/
def exercise24Embedding (a : X) (p : X) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (exercise24Function a p)
    (exercise24_continuous a p) (dist a p) (exercise24_pointwise_bound a p)

@[simp] theorem exercise24Embedding_apply (a p x : X) :
    exercise24Embedding a p x = (dist x p - dist x a : ℝ) := rfl

theorem exercise24_distance (a p q : X) :
    dist (exercise24Embedding a p) (exercise24Embedding a q) = dist p q := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    simp only [exercise24Embedding_apply, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    simpa only [sub_sub_sub_cancel_right, dist_comm p x, dist_comm q x] using
      abs_dist_sub_le p q x
  · have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := exercise24Embedding a p) (g := exercise24Embedding a q) p
    have he : dist (exercise24Embedding a p p) (exercise24Embedding a q p) = dist p q := by
      simp only [exercise24Embedding_apply, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      rw [sub_sub_sub_cancel_right, dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
    exact he ▸ h

theorem exercise24_norm (a p q : X) :
    ‖exercise24Embedding a p - exercise24Embedding a q‖ = dist p q := by
  rw [← dist_eq_norm, exercise24_distance]

theorem exercise24_isometry (a : X) : Isometry (exercise24Embedding a) :=
  Isometry.of_dist_eq (exercise24_distance a)

/-- The requested completion, as a closed subspace of `C_b(X, ℂ)`. -/
def Exercise24Completion (a : X) := closure (range (exercise24Embedding a))

instance exercise24MetricSpace (a : X) : MetricSpace (Exercise24Completion a) :=
  inferInstanceAs (MetricSpace ↥(closure (range (exercise24Embedding a))))

instance exercise24CompleteSpace (a : X) : CompleteSpace (Exercise24Completion a) :=
  isClosed_closure.completeSpace_coe

/-- The original embedding with its codomain restricted to the closure. -/
def exercise24IntoCompletion (a : X) (p : X) : Exercise24Completion a :=
  ⟨exercise24Embedding a p, subset_closure (mem_range_self p)⟩

theorem exercise24_completion_isometry (a : X) : Isometry (exercise24IntoCompletion a) := by
  apply Isometry.of_dist_eq
  intro p q
  exact exercise24_distance a p q

theorem exercise24_dense_embedding (a : X) : DenseRange (exercise24IntoCompletion a) := by
  rw [DenseRange, Subtype.dense_iff]
  change closure (range (exercise24Embedding a)) ⊆
    closure (Subtype.val '' range (exercise24IntoCompletion a))
  have he : Subtype.val '' range (exercise24IntoCompletion a) =
      range (exercise24Embedding a) := by
    rw [← range_comp]
    rfl
  rw [he]

theorem exercise24_completion (a : X) :
    CompleteSpace (Exercise24Completion a) ∧
    Isometry (exercise24IntoCompletion a) ∧ DenseRange (exercise24IntoCompletion a) :=
  ⟨inferInstance, exercise24_completion_isometry a, exercise24_dense_embedding a⟩

end

end Rudin.Chapter07
