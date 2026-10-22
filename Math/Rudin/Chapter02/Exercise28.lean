module

public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# R02E28: Cantor–Bendixson decomposition and isolated points

Source: Rudin, Third Edition, book page 45 (PDF page 54).
The source uses “countable” for countably infinite sets. The stronger corrected
corollary for at most countable sets requires nonemptiness. The empty-set test
is retained explicitly. No isolated-point corollary is asserted for arbitrary
separable metric spaces, where it is false.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Filter Topology TopologicalSpace

theorem exercise28_decomposition {X : Type*} [MetricSpace X]
    (hX : ∃ D : Set X, D.Countable ∧ Dense D) {F : Set X} (hF : IsClosed F) :
    ∃ P C : Set X, Perfect P ∧ C.Countable ∧ F = P ∪ C := by
  let : SeparableSpace X := ⟨hX⟩
  let : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  obtain ⟨C, P, hC, hP, h⟩ := exists_countable_union_perfect_of_isClosed hF
  exact ⟨P, C, hP, hC, h.trans (union_comm C P)⟩

theorem exercise28_nonempty {k : ℕ} {F : Set (EuclideanSpace ℝ (Fin k))}
    (hF : IsClosed F) (hc : F.Countable) (hn : F.Nonempty) :
    ∃ x ∈ F, ¬ AccPt x (𝓟 F) := by
  by_contra! h
  have hp : Perfect F := ⟨hF, h⟩
  obtain ⟨f, hf, _, hi⟩ := hp.exists_nat_bool_injection hn
  have hcount : (Set.range f).Countable := hc.mono hf
  have hdom : (Set.univ : Set (ℕ → Bool)).Countable :=
    Set.countable_of_injective_of_countable_image hi.injOn (by simpa using hcount)
  have : Countable (ℕ → Bool) := Set.countable_univ_iff.mp hdom
  obtain ⟨s, hs⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hs (fun n => !(s n n))
  have hd := congrFun hn n
  cases he : s n n <;> simp [he] at hd

/-- Rudin's countably-infinite source corollary excludes the empty set already. -/
theorem exercise28_source {k : ℕ} {F : Set (EuclideanSpace ℝ (Fin k))}
    (hF : IsClosed F) (hc : F.Countable) (hi : F.Infinite) :
    ∃ x ∈ F, ¬ AccPt x (𝓟 F) :=
  exercise28_nonempty hF hc hi.nonempty

/-- Translating “countable” as at most countable without nonemptiness is false. -/
theorem exercise28_empty (k : ℕ) :
    IsClosed (∅ : Set (EuclideanSpace ℝ (Fin k))) ∧
      (∅ : Set (EuclideanSpace ℝ (Fin k))).Countable ∧
      ¬ ∃ x ∈ (∅ : Set (EuclideanSpace ℝ (Fin k))), ¬ AccPt x (𝓟 (∅ : Set (EuclideanSpace ℝ (Fin k)))) :=
  ⟨isClosed_empty, Set.countable_empty, by simp⟩

end Rudin.Chapter02
