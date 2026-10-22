module

public import Mathlib

/-! # Exercise 2.15 (PDF page 53)
The closed rays `[n,∞)` and bounded intervals `(0,1/(n+1))` refute both
versions of Theorem 2.36 and its nested-sequence corollary.
-/

@[expose] public section
namespace Rudin.Chapter02

def closedEscape (n : ℕ) : Set ℝ := Set.Ici (n : ℝ)
def boundedEscape (n : ℕ) : Set ℝ := Set.Ioo 0 (1 / (n + 1 : ℝ))

/-- A finite intersection of a decreasing nonempty sequence is nonempty. -/
theorem antitone_nat_finite_inter_nonempty {A : ℕ → Set ℝ}
    (hA : Antitone A) (hne : ∀ n, (A n).Nonempty) (s : Finset ℕ) :
    (⋂ n ∈ s, A n).Nonempty := by
  obtain ⟨x, hx⟩ := hne (s.sup id)
  refine ⟨x, Set.mem_iInter₂.mpr fun n hn => ?_⟩
  exact hA (Finset.le_sup (f := id) hn) hx

theorem closedEscape_closed (n : ℕ) : IsClosed (closedEscape n) := isClosed_Ici

theorem closedEscape_antitone : Antitone closedEscape := by
  intro m n h x hx
  change (m : ℝ) ≤ x
  exact (Nat.cast_le.mpr h).trans hx

theorem closedEscape_nonempty (n : ℕ) : (closedEscape n).Nonempty :=
  ⟨n, le_rfl⟩

theorem closedEscape_inter_empty : (⋂ n, closedEscape n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact (not_le_of_gt hn) (Set.mem_iInter.mp hx n)

/-- Closed sets: every finite intersection is nonempty, but the total is empty. -/
theorem closed_finite_intersection_counterexample :
    (∀ n, IsClosed (closedEscape n)) ∧
    (∀ s : Finset ℕ, (⋂ n ∈ s, closedEscape n).Nonempty) ∧
    (⋂ n, closedEscape n) = ∅ :=
  ⟨closedEscape_closed,
    antitone_nat_finite_inter_nonempty closedEscape_antitone closedEscape_nonempty,
    closedEscape_inter_empty⟩

/-- Closed sets: the nested nonempty sequence has empty intersection. -/
theorem closed_nested_counterexample :
    (∀ n, IsClosed (closedEscape n) ∧ (closedEscape n).Nonempty) ∧
    Antitone closedEscape ∧ (⋂ n, closedEscape n) = ∅ :=
  ⟨fun n => ⟨closedEscape_closed n, closedEscape_nonempty n⟩,
    closedEscape_antitone, closedEscape_inter_empty⟩

theorem boundedEscape_bounded (n : ℕ) : Bornology.IsBounded (boundedEscape n) :=
  Metric.isBounded_Ioo _ _

theorem boundedEscape_antitone : Antitone boundedEscape := by
  intro m n h x hx
  refine ⟨hx.1, hx.2.trans_le ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

theorem boundedEscape_nonempty (n : ℕ) : (boundedEscape n).Nonempty := by
  exact Set.nonempty_Ioo.mpr (by positivity)

theorem boundedEscape_inter_empty : (⋂ n, boundedEscape n) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h0 : 0 < x := (Set.mem_iInter.mp hx 0).1
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hnx : 1 / x < (n : ℝ) + 1 := by linarith
  have hle : 1 / (n + 1 : ℝ) < x := by
    apply (div_lt_iff₀ hn0).mpr
    have := (div_lt_iff₀ h0).mp hnx
    nlinarith
  exact (not_lt_of_ge hle.le) (Set.mem_iInter.mp hx n).2

/-- Bounded sets: every finite intersection is nonempty, but the total is empty. -/
theorem bounded_finite_intersection_counterexample :
    (∀ n, Bornology.IsBounded (boundedEscape n)) ∧
    (∀ s : Finset ℕ, (⋂ n ∈ s, boundedEscape n).Nonempty) ∧
    (⋂ n, boundedEscape n) = ∅ :=
  ⟨boundedEscape_bounded,
    antitone_nat_finite_inter_nonempty boundedEscape_antitone boundedEscape_nonempty,
    boundedEscape_inter_empty⟩

/-- Bounded sets: the nested nonempty sequence has empty intersection. -/
theorem bounded_nested_counterexample :
    (∀ n, Bornology.IsBounded (boundedEscape n) ∧ (boundedEscape n).Nonempty) ∧
    Antitone boundedEscape ∧ (⋂ n, boundedEscape n) = ∅ :=
  ⟨fun n => ⟨boundedEscape_bounded n, boundedEscape_nonempty n⟩,
    boundedEscape_antitone, boundedEscape_inter_empty⟩
end Rudin.Chapter02
