module

public import Math.Rudin.Chapter02.Exercise19
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R02E21: separated sets and line segments

Source: Rudin, Third Edition, book pages 44–45 (PDF pages 53–54).
Connectedness in the last part means preconnectedness: the source includes
empty convex sets. The segment is the specified affine parameterization.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set

/-- The source's affine line, defined for all real parameters. -/
def segmentParameter {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) (t : ℝ) :=
  (1 - t) • a + t • b

theorem segmentParameter_continuous {k : ℕ} (a b : EuclideanSpace ℝ (Fin k)) :
    Continuous (segmentParameter a b) := by
  unfold segmentParameter
  fun_prop

theorem exercise21_a {k : ℕ} {A B : Set (EuclideanSpace ℝ (Fin k))}
    (h : separatedSets A B) (a b : EuclideanSpace ℝ (Fin k)) :
    separatedSets (segmentParameter a b ⁻¹' A) (segmentParameter a b ⁻¹' B) := by
  constructor
  · exact (h.1.preimage _).mono_left
      ((segmentParameter_continuous a b).closure_preimage_subset A)
  · exact (h.2.preimage _).mono_right
      ((segmentParameter_continuous a b).closure_preimage_subset B)

theorem exercise21_b {k : ℕ} {A B : Set (EuclideanSpace ℝ (Fin k))}
    (h : separatedSets A B) {a b : EuclideanSpace ℝ (Fin k)} (ha : a ∈ A) (hb : b ∈ B) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, segmentParameter a b t ∉ A ∪ B := by
  by_contra! hn
  have hcover : segmentParameter a b '' Set.Icc (0 : ℝ) 1 ⊆ A ∪ B := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases h0 : t = 0
    · simp [h0, segmentParameter, ha]
    by_cases h1 : t = 1
    · simp [h1, segmentParameter, hb]
    exact hn t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have hc := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).image (segmentParameter a b)
    (segmentParameter_continuous a b).continuousOn
  obtain ⟨x, hx, hxA, hxB⟩ := isPreconnected_closed_iff.mp hc
    (closure A) (closure B) isClosed_closure isClosed_closure
    (hcover.trans (union_subset_union subset_closure subset_closure))
    ⟨a, ⟨0, by norm_num, by simp [segmentParameter]⟩, subset_closure ha⟩
    ⟨b, ⟨1, by norm_num, by simp [segmentParameter]⟩, subset_closure hb⟩
  rcases hcover hx with hxA' | hxB'
  · exact Set.disjoint_left.mp h.2 hxA' hxB
  · exact Set.disjoint_left.mp h.1 hxA hxB'

theorem exercise21_c {k : ℕ} {E : Set (EuclideanSpace ℝ (Fin k))}
    (hE : Convex ℝ E) : IsPreconnected E :=
  hE.isPreconnected

end Rudin.Chapter02
