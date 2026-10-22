module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# R02E08: accumulation points in the Euclidean plane

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 2.8, book page 43 (PDF page 52).

Every member of an open set in the Euclidean plane is an accumulation point.
The closed singleton containing the origin gives a negative answer for closed
sets. `AccPt x (Filter.principal E)` is the accumulation-point predicate for E.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- Every point of an open subset of the Euclidean plane is a limit point. -/
theorem exercise08_open {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : IsOpen E) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ E) :
    AccPt x (Filter.principal E) := by
  let : PerfectSpace (EuclideanSpace ℝ (Fin 2)) := perfectSpace_of_module ℝ _
  exact hE.preperfect x hx

/-- A closed singleton in the Euclidean plane has a member which is not a
limit point, so the corresponding assertion for closed sets is false. -/
theorem exercise08_closed :
    IsClosed ({0} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ ({0} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ¬ AccPt (0 : EuclideanSpace ℝ (Fin 2)) (Filter.principal {0}) := by
  refine ⟨isClosed_singleton, rfl, ?_⟩
  intro h
  obtain ⟨y, hy, hyne⟩ := accPt_iff_nhds.1 h Set.univ Filter.univ_mem
  exact hyne (Set.mem_singleton_iff.1 hy.2)

end Rudin.Chapter02
