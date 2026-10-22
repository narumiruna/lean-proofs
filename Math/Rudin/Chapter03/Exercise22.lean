module

public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

@[expose] public section

open Set

namespace Rudin.Chapter03

/-- Baire's theorem for the countable family in the exercise. -/
theorem exercise22_baire_dense {X : Type*} [MetricSpace X] [CompleteSpace X]
    (G : ℕ → Set X) (ho : ∀ n, IsOpen (G n)) (hd : ∀ n, Dense (G n)) :
    Dense (⋂ n, G n) :=
  dense_iInter_of_isOpen_nat ho hd

/-- Nonemptiness uses the source assumption that the complete space is nonempty. -/
theorem exercise22_baire_nonempty {X : Type*} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] (G : ℕ → Set X) (ho : ∀ n, IsOpen (G n))
    (hd : ∀ n, Dense (G n)) : (⋂ n, G n).Nonempty :=
  (exercise22_baire_dense G ho hd).nonempty

end Rudin.Chapter03
