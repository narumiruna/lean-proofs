module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Instances.Rat

/-!
# R02E22: a countable dense set in Euclidean space

Source: Rudin, Third Edition, book page 45 (PDF page 54).
The construction uses rational coordinates, with the Euclidean topology.
The proof also covers dimension zero.
-/

@[expose] public section

namespace Rudin.Chapter02

/-- Rational-coordinate points, with the Euclidean norm. -/
def rationalPoints (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
  Set.range (fun q : Fin k → ℚ => WithLp.toLp 2 (fun i => (q i : ℝ)))

theorem exercise22_countable (k : ℕ) : (rationalPoints k).Countable :=
  Set.countable_range _

theorem exercise22_dense (k : ℕ) : Dense (rationalPoints k) := by
  have h : DenseRange (fun q : Fin k → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  exact (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.surjective.denseRange.comp h
    (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.continuous

theorem exercise22 (k : ℕ) :
    ∃ D : Set (EuclideanSpace ℝ (Fin k)), D.Countable ∧ Dense D :=
  ⟨rationalPoints k, exercise22_countable k, exercise22_dense k⟩

end Rudin.Chapter02
