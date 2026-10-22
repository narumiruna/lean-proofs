module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic

@[expose] public section

namespace Rudin.Chapter04

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- The source's real infimum. Its properties below require a nonempty set. -/
noncomputable def exercise20_rho (E : Set X) (x : X) : ℝ :=
  sInf ((fun z => dist x z) '' E)

/-- The displayed infimum agrees with the library distance to a nonempty set. -/
theorem exercise20_rho_eq_infDist {E : Set X} (hE : E.Nonempty) (x : X) :
    exercise20_rho E x = infDist x E := by
  exact (isGLB_infDist (x := x) hE).csInf_eq (hE.image _)

/-- Part (a): the zero set is the closure, not necessarily the original set. -/
theorem exercise20_a {E : Set X} (hE : E.Nonempty) (x : X) :
    exercise20_rho E x = 0 ↔ x ∈ closure E := by
  rw [exercise20_rho_eq_infDist hE]
  exact (mem_closure_iff_infDist_zero hE).symm

/-- Part (b): the exact 1-Lipschitz inequality. -/
theorem exercise20_b_lipschitz {E : Set X} (hE : E.Nonempty) (x y : X) :
    |exercise20_rho E x - exercise20_rho E y| ≤ dist x y := by
  rw [exercise20_rho_eq_infDist hE, exercise20_rho_eq_infDist hE]
  simpa [Real.dist_eq] using (lipschitz_infDist_pt E).dist_le_mul x y

/-- Part (b): uniform continuity on the entire metric space. -/
theorem exercise20_b_uniform_continuity {E : Set X} (hE : E.Nonempty) :
    UniformContinuous (exercise20_rho E) := by
  have heq : exercise20_rho E = (fun x => infDist x E) :=
    funext (exercise20_rho_eq_infDist hE)
  rw [heq]
  exact uniformContinuous_infDist_pt E

end Rudin.Chapter04
