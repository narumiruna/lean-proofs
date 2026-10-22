module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Tactic.FinCases

/-!
# Rudin, Chapter 3, Exercise 19

`cantorSet` is the literal middle-thirds set: it is the intersection of
`preCantorSet n`, starting at `[0,1]` and replacing each interval by its left
and right thirds. The digit of index `n` below is Rudin's digit of index `n+1`.
All the terms are nonnegative and bounded by a geometric series. Thus the
use of `Summable` here is justified; ordered partial-sum convergence is also
stated explicitly. Endpoints, including 0 and 1, are not excluded.
-/

@[expose] public section

noncomputable section

open Filter Set Real
open scoped Topology

namespace Rudin.Chapter03

/-- Encode a real zero-or-two digit as a ternary digit. -/
def exercise19_digit (a : ℕ → ℝ) (n : ℕ) : Fin 3 :=
  if a n = 0 then 0 else 2

theorem exercise19_digit_cast (a : ℕ → ℝ) (ha : ∀ n, a n = 0 ∨ a n = 2)
    (n : ℕ) : (exercise19_digit a n : ℝ) = a n := by
  rcases ha n with h | h <;> simp [exercise19_digit, h]

theorem exercise19_term_eq (a : ℕ → ℝ) (ha : ∀ n, a n = 0 ∨ a n = 2) :
    (fun n => a n / 3 ^ (n + 1)) = ofDigitsTerm (exercise19_digit a) := by
  funext n
  simp [ofDigitsTerm, exercise19_digit_cast a ha n, div_eq_mul_inv]

/-- Each prescribed series is summable, its ordered partial sums converge,
and its sum is in the middle-thirds Cantor set. -/
theorem exercise19_digits_in_cantor (a : ℕ → ℝ)
    (ha : ∀ n, a n = 0 ∨ a n = 2) :
    Summable (fun n => a n / 3 ^ (n + 1)) ∧
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n / 3 ^ (n + 1)) atTop
      (𝓝 (∑' n, a n / 3 ^ (n + 1))) ∧
    (∑' n, a n / 3 ^ (n + 1)) ∈ cantorSet := by
  have hs : Summable (fun n => a n / 3 ^ (n + 1)) := by
    rw [exercise19_term_eq a ha]
    exact summable_ofDigitsTerm
  refine ⟨hs, hs.hasSum.tendsto_sum_nat, ?_⟩
  rw [exercise19_term_eq a ha]
  apply ofDigits_zero_two_sequence_mem_cantorSet
  intro n
  by_cases h : a n = 0 <;> simp [exercise19_digit, h]

/-- Every point of the literal Cantor set has zero-or-two digits, with
convergence of the ordered partial sums to that point. -/
theorem exercise19_cantor_has_digits {x : ℝ} (hx : x ∈ cantorSet) :
    ∃ a : ℕ → ℝ, (∀ n, a n = 0 ∨ a n = 2) ∧
      Summable (fun n => a n / 3 ^ (n + 1)) ∧
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n / 3 ^ (n + 1)) atTop (𝓝 x) ∧
      (∑' n, a n / 3 ^ (n + 1)) = x := by
  obtain ⟨d, hd, hdx⟩ := (Set.ext_iff.mp cantorSet_eq_zero_two_ofDigits x).mp hx
  have hd02 : ∀ n, (d n : ℝ) = 0 ∨ (d n : ℝ) = 2 := by
    intro n
    have hn := hd n
    generalize d n = k at hn ⊢
    fin_cases k <;> simp_all
  have heq : (fun n => (d n : ℝ) / 3 ^ (n + 1)) = ofDigitsTerm d := by
    funext n
    simp [ofDigitsTerm, div_eq_mul_inv]
  have hs : Summable (fun n => (d n : ℝ) / 3 ^ (n + 1)) := by
    rw [heq]
    exact summable_ofDigitsTerm
  have hsum : (∑' n, (d n : ℝ) / 3 ^ (n + 1)) = x := by
    rw [heq]
    exact hdx
  exact ⟨fun n => (d n : ℝ), hd02, hs, hsum ▸ hs.hasSum.tendsto_sum_nat, hsum⟩

/-- Equality of the series image and the middle-thirds construction. -/
theorem exercise19_image :
    {x : ℝ | ∃ a : ℕ → ℝ, (∀ n, a n = 0 ∨ a n = 2) ∧
      (∑' n, a n / 3 ^ (n + 1)) = x} = ⋂ n, preCantorSet n := by
  change _ = cantorSet
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (exercise19_digits_in_cantor a ha).2.2
  · intro hx
    obtain ⟨a, ha, _, _, heq⟩ := exercise19_cantor_has_digits hx
    exact ⟨a, ha, heq⟩

end Rudin.Chapter03
