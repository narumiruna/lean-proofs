module

public import Mathlib

/-! # Exercise 2.10
The zero-one metric (PDF page 53). The conclusions hold for every type,
so in particular for an infinite set. The empty set is included.
-/

@[expose] public section
namespace Rudin.Chapter02

noncomputable def zeroOneDistance {X : Type*} (x y : X) : ℝ :=
  @ite ℝ (x = y) (Classical.propDecidable _) 0 1

/-- The stated distance satisfies all metric axioms. -/
@[instance_reducible]
noncomputable def zeroOneMetric (X : Type*) : MetricSpace X where
  dist := zeroOneDistance
  dist_self x := by simp [zeroOneDistance]
  dist_comm x y := by
    classical
    by_cases h : x = y <;> simp [zeroOneDistance, h, Ne.symm]
  dist_triangle x y z := by
    classical
    by_cases hxy : x = y <;> by_cases hyz : y = z <;>
      by_cases hxz : x = z <;> simp_all [zeroOneDistance]
  eq_of_dist_eq_zero h := by simpa [zeroOneDistance] using h

section
variable {X : Type*}
noncomputable section
local instance : MetricSpace X := zeroOneMetric X

/-- All four metric axioms, with nonnegativity stated explicitly. -/
theorem zeroOneDistance_metric_axioms :
    (∀ x y : X, 0 ≤ zeroOneDistance x y) ∧
    (∀ x y : X, zeroOneDistance x y = 0 ↔ x = y) ∧
    (∀ x y : X, zeroOneDistance x y = zeroOneDistance y x) ∧
    (∀ x y z : X, zeroOneDistance x z ≤ zeroOneDistance x y + zeroOneDistance y z) :=
  ⟨fun x y => @dist_nonneg X _ x y, fun x y => @dist_eq_zero X _ x y,
    fun x y => dist_comm x y, fun x y z => dist_triangle x y z⟩

/-- The topology induced by the zero-one distance is discrete. -/
theorem zeroOne_discreteTopology : DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have h : Metric.ball x (1 / 2) = {x} := by
    ext y
    simp only [Metric.mem_ball, Set.mem_singleton_iff]
    change zeroOneDistance y x < 1 / 2 ↔ y = x
    by_cases hy : y = x <;> norm_num [zeroOneDistance, hy]
  rw [← h]
  exact Metric.isOpen_ball

/-- Every subset is open. -/
theorem zeroOne_isOpen (s : Set X) : IsOpen s := by
  let := zeroOne_discreteTopology (X := X)
  exact isOpen_discrete s

/-- Every subset is closed. -/
theorem zeroOne_isClosed (s : Set X) : IsClosed s := by
  let := zeroOne_discreteTopology (X := X)
  exact isClosed_discrete s

/-- Exactly the finite subsets are compact, including the empty subset. -/
theorem zeroOne_isCompact_iff (s : Set X) : IsCompact s ↔ s.Finite := by
  let := zeroOne_discreteTopology (X := X)
  exact isCompact_iff_finite
end
end
end Rudin.Chapter02
