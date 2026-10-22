module

public import Mathlib

@[expose] public section
namespace Rudin.Chapter04
open Set
open scoped Pointwise

/-- This includes zero-dimensional Euclidean space and empty summands. -/
theorem exercise25_a {k : ℕ} {K C : Set (EuclideanSpace ℝ (Fin k))}
    (hK : IsCompact K) (hC : IsClosed C) : IsClosed (K + C) :=
  hC.add_left_of_isCompact hK

def exercise25C1 : Set ℝ := range (fun n : ℤ => (n : ℝ))
def exercise25C2 (α : ℝ) : Set ℝ := range (fun n : ℤ => (n : ℝ) * α)

theorem exercise25_b_first_closed : IsClosed exercise25C1 :=
  Int.isClosedEmbedding_coe_real.isClosed_range

theorem exercise25_b_second_closed {α : ℝ} (hα : Irrational α) :
    IsClosed (exercise25C2 α) := by
  have he := (Homeomorph.mulRight₀ α hα.ne_zero).isClosedMap
  simpa [exercise25C1, exercise25C2, ← range_comp, Function.comp_def] using
    he _ exercise25_b_first_closed

theorem exercise25_sum_eq_range (α : ℝ) :
    exercise25C1 + exercise25C2 α =
      range (fun p : ℤ × ℤ => (p.1 : ℝ) + (p.2 : ℝ) * α) := by
  ext x
  constructor
  · rintro ⟨u, ⟨m, rfl⟩, v, ⟨n, rfl⟩, rfl⟩
    exact ⟨(m, n), rfl⟩
  · rintro ⟨⟨m, n⟩, rfl⟩
    exact ⟨m, ⟨m, rfl⟩, n * α, ⟨n, rfl⟩, rfl⟩

/-- Rudin's countable means countably infinite, not merely at most countable. -/
theorem exercise25_b_countable_sum (α : ℝ) :
    (exercise25C1 + exercise25C2 α).Countable ∧
    (exercise25C1 + exercise25C2 α).Infinite := by
  constructor
  · rw [exercise25_sum_eq_range]; exact countable_range _
  · apply (Set.infinite_range_of_injective (Int.cast_injective (α := ℝ))).mono
    intro x hx
    exact ⟨x, hx, 0, ⟨0, by simp⟩, add_zero x⟩

theorem exercise25_b_dense_sum {α : ℝ} (hα : Irrational α) :
    Dense (exercise25C1 + exercise25C2 α) := by
  have hd : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using hα)
  apply hd.mono
  intro x hx
  rcases AddSubgroup.mem_closure_pair.mp hx with ⟨m, n, rfl⟩
  exact ⟨n, ⟨n, rfl⟩, m * α, ⟨m, rfl⟩, by simp [zsmul_eq_mul, add_comm]⟩

theorem exercise25_b_nonclosed_sum {α : ℝ} (hα : Irrational α) :
    ¬ IsClosed (exercise25C1 + exercise25C2 α) := by
  intro hc
  have he : exercise25C1 + exercise25C2 α = univ :=
    (exercise25_b_dense_sum hα).closure_eq ▸ hc.closure_eq.symm
  have hh := (exercise25_b_countable_sum α).1
  rw [he] at hh
  exact not_countable_univ hh

end Rudin.Chapter04
