module

public import Mathlib

/-! # Exercise 2.14 (PDF page 53)
The open rays `(t, ∞)`, indexed by positive real numbers, cover `(0,1)`.
Every finite subfamily misses a positive point smaller than all its indices.
-/

@[expose] public section
namespace Rudin.Chapter02

def intervalOpenCover (t : {t : ℝ // 0 < t}) : Set ℝ := Set.Ioi t.val

theorem intervalOpenCover_isOpen (t : {t : ℝ // 0 < t}) :
    IsOpen (intervalOpenCover t) := isOpen_Ioi

theorem intervalOpenCover_covers :
    Set.Ioo (0 : ℝ) 1 ⊆ ⋃ t, intervalOpenCover t := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨x / 2, by linarith [hx.1]⟩, by
    change x / 2 < x
    linarith [hx.1]⟩

theorem intervalOpenCover_no_finite_subcover
    (s : Finset {t : ℝ // 0 < t}) :
    ¬ Set.Ioo (0 : ℝ) 1 ⊆ ⋃ t ∈ s, intervalOpenCover t := by
  have hsmall : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∀ t ∈ s, x ≤ t.val := by
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
    | @insert t s ht ih =>
      obtain ⟨x, hx, hx1, hs⟩ := ih
      refine ⟨min x t.val / 2, div_pos (lt_min hx t.property) (by norm_num), ?_, ?_⟩
      · have := min_le_left x t.val
        linarith
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · have := min_le_right x u.val
          linarith [u.property]
        · have := min_le_left x t.val
          have := hs u hu
          linarith
  obtain ⟨x, hx, hx1, hs⟩ := hsmall
  intro hcover
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcover ⟨hx, hx1⟩)
  exact (not_lt_of_ge (hs t ht)) hxt

/-- An explicit open cover together with its failure to have a finite subcover. -/
theorem exercise14 :
    (∀ t, IsOpen (intervalOpenCover t)) ∧
    (Set.Ioo (0 : ℝ) 1 ⊆ ⋃ t, intervalOpenCover t) ∧
    (∀ s : Finset {t : ℝ // 0 < t},
      ¬ Set.Ioo (0 : ℝ) 1 ⊆ ⋃ t ∈ s, intervalOpenCover t) :=
  ⟨intervalOpenCover_isOpen, intervalOpenCover_covers,
    intervalOpenCover_no_finite_subcover⟩
end Rudin.Chapter02
