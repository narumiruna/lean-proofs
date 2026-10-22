module

public import Mathlib

/-! # Exercise 3.1: convergence of absolute values and failure of the converse. -/

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- Norms converge whenever the original sequence converges; this includes complex absolute values. -/
theorem exercise01_absolute_values {E : Type*} [SeminormedAddCommGroup E]
    {s : ℕ → E} {a : E} (h : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun n => ‖s n‖) atTop (𝓝 ‖a‖) := h.norm

/-- The alternating real sequence has constant absolute value but has no limit. -/
theorem exercise01_converse :
    Tendsto (fun n : ℕ => |(-1 : ℝ) ^ n|) atTop (𝓝 1) ∧
      ¬ ∃ a : ℝ, Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) atTop (𝓝 a) := by
  constructor
  · simp
  · rintro ⟨a, ha⟩
    have he : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
    have h₀ : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 a) := by
      simpa [Function.comp_def, pow_mul] using ha.comp he
    have h₁ : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 a) := by
      simpa [Function.comp_def, pow_add, pow_mul] using ha.comp ho
    have := tendsto_nhds_unique h₀ tendsto_const_nhds
    have := tendsto_nhds_unique h₁ tendsto_const_nhds
    linarith

end Rudin.Chapter03
