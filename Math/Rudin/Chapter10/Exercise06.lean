module

public import Math.Rudin.Chapter08.Exercise01
public import Math.Rudin.Chapter10.Exercise05
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
noncomputable section
namespace Rudin.Chapter10
open Set Metric
open scoped Topology ContDiff

/-- The positive-side flat function is obtained from the exact Chapter 8 function. -/
theorem exercise06_source_glue (t : ℝ) :
    Chapter08.exercise01_function (Real.sqrt t) = expNegInvGlue t := by
  by_cases ht : 0 ≤ t
  · simp only [Chapter08.exercise01_function, Real.sq_sqrt ht]
  · have hn : t ≤ 0 := (lt_of_not_ge ht).le
    simp [Real.sqrt_eq_zero_of_nonpos hn, Chapter08.exercise01_function,
      expNegInvGlue.zero_of_nonpos hn]

def exercise06_transition (t : ℝ) : ℝ :=
  Chapter08.exercise01_function (Real.sqrt t) /
    (Chapter08.exercise01_function (Real.sqrt t) +
      Chapter08.exercise01_function (Real.sqrt (1-t)))

theorem exercise06_transition_eq : exercise06_transition = Real.smoothTransition := by
  funext t
  simp only [exercise06_transition, exercise06_source_glue, Real.smoothTransition]

/-- This explicit auxiliary function uses the source flat function, not a
classically selected member of the library's bump-function typeclass. -/
def exercise06_auxiliary {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r R : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  exercise06_transition ((R^2 - ‖y-x‖^2) / (R^2-r^2))

theorem exercise06_auxiliary_smooth {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r R : ℝ) :
    ContDiff ℝ ∞ (exercise06_auxiliary x r R) := by
  unfold exercise06_auxiliary
  rw [exercise06_transition_eq]
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const _)

theorem exercise06_bump {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧
      ∃ f : C(EuclideanSpace ℝ (Fin n), ℝ),
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ EqOn f (fun _ => 1) V ∧
        tsupport f ⊆ U ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let f := exercise06_auxiliary x (r/4) (r/2)
  have hc : ContDiff ℝ ∞ f := exercise06_auxiliary_smooth _ _ _
  have hd : 0 < (r/2)^2-(r/4)^2 := by nlinarith [sq_pos_of_pos hr]
  have hzero (y) (hy : r/2 ≤ ‖y-x‖) : f y = 0 := by
    change exercise06_transition _ = 0
    rw [exercise06_transition_eq]
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    nlinarith [sq_nonneg (‖y-x‖-r/2), norm_nonneg (y-x)]
  have ht : tsupport f ⊆ closedBall x (r/2) := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    rw [mem_closedBall_iff_norm]
    by_contra hn
    exact hy (hzero y (le_of_lt (lt_of_not_ge hn)))
  refine ⟨ball x (r/4), isOpen_ball, mem_ball_self (by positivity),
    ⟨f, hc.continuous⟩, ?_, ?_, ?_, hc, ?_⟩
  · intro y
    change exercise06_transition _ ∈ Icc (0:ℝ) 1
    rw [exercise06_transition_eq]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro y hy
    change exercise06_transition _ = 1
    rw [exercise06_transition_eq]
    apply Real.smoothTransition.one_of_one_le
    apply (one_le_div hd).mpr
    have hn : ‖y-x‖ < r/4 := mem_ball_iff_norm.mp hy
    nlinarith [norm_nonneg (y-x), sq_nonneg (r/4-‖y-x‖)]
  · exact ht.trans ((closedBall_subset_ball (by linarith)).trans hsub)
  · exact (isCompact_closedBall x (r/2)).of_isClosed_subset isClosed_closure ht

/-- The ordered-product partition is smooth because it is a finite product. -/
theorem exercise06_product_smooth {X J : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [Fintype J] {K : Set X} (f : BumpCovering J X K)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (j : J) :
    ContDiff ℝ ∞ (f.toPartitionOfUnity j) := by
  classical
  have heq : (f.toPartitionOfUnity j : X → ℝ) = fun x =>
      f j x * ∏ k ∈ Finset.univ with WellOrderingRel k j, (1 - f k x) := by
    funext x
    exact f.toPartitionOfUnity_eq_mul_prod j x Finset.univ (by simp)
  rw [heq]
  exact (hf j).mul (contDiff_prod fun k _ => contDiff_const.sub (hf k))

/-- A finite C-infinity subordinate partition. The same functions are
continuously differentiable and differentiable. The compact set may be empty. -/
theorem exercise06_smooth_partition {n : ℕ} {I : Type*}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (U : I → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (J : Type) (_ : Fintype J) (a : J → I)
      (ψ : J → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ j, ContDiff ℝ ∞ (ψ j)) ∧
      (∀ j, Differentiable ℝ (ψ j)) ∧
      (∀ j, HasCompactSupport (ψ j)) ∧
      (∀ j x, ψ j x ∈ Icc (0 : ℝ) 1) ∧
      (∀ j, tsupport (ψ j) ⊆ U (a j)) ∧
      (∀ x ∈ K, ∑ j, ψ j x = 1) := by
  obtain ⟨J, inst, a, f, hf, hs⟩ := exercise05_finite_bumps hK U
    (fun f => ContDiff ℝ ∞ f ∧ HasCompactSupport f) (by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
      obtain ⟨V, hV, hxV, g, hr, hone, ht, hc, hk⟩ := exercise06_bump (hU i) hi
      exact ⟨i, V, hV, hxV, g, hr, hone, ht, hc, hk⟩)
  let := inst
  have hc := exercise06_product_smooth f (fun j => (hs j).1)
  exact ⟨J, inst, a, fun j => f.toPartitionOfUnity j, hc,
    fun j => (hc j).differentiable (by simp),
    fun j => (hs j).2.mono' ((f.support_toPartitionOfUnity_subset j).trans (subset_tsupport _)),
    fun j x => ⟨f.toPartitionOfUnity.nonneg j x, f.toPartitionOfUnity.le_one j x⟩,
    hf.toPartitionOfUnity, fun x hx => by
      simpa only [finsum_eq_sum_of_fintype] using f.toPartitionOfUnity.sum_eq_one hx⟩

end Rudin.Chapter10
