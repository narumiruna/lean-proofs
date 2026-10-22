module

public import Mathlib

/-! # Exercise 2.17

The set consists of actual infinite base-ten expansions with digits 4 and 7.
It is uncountable, not dense in `[0,1]`, compact, and perfect.
Each allowed expansion is unique even among all decimal strings. Thus the
terminating/repeating-nine convention does not change the set.
-/

@[expose] public section
namespace Rudin.Chapter02

open Set Filter Topology Real

/-- The decimal digit selected by a binary choice. -/
def decimal47Digit (b : Bool) : Fin 10 := if b then 7 else 4

/-- The infinite decimal `0.d₀d₁…`, where each `dᵢ` is 4 or 7. -/
noncomputable def decimal47Value (a : ℕ → Bool) : ℝ :=
  Real.ofDigits (fun n => decimal47Digit (a n))

/-- The value is the actual infinite decimal series, not just a coding map. -/
theorem decimal47Value_eq_tsum (a : ℕ → Bool) :
    decimal47Value a = ∑' n, (if a n then (7 : ℝ) else 4) / 10 ^ (n + 1) := by
  unfold decimal47Value Real.ofDigits
  apply tsum_congr
  intro n
  cases h : a n <;> simp [Real.ofDigitsTerm, decimal47Digit, h, div_eq_mul_inv]

/-- The set in the exercise, defined by infinite decimal expansions. -/
def decimal47Set : Set ℝ :=
  {x | ∃ d : ℕ → Fin 10, (∀ n, d n = 4 ∨ d n = 7) ∧ Real.ofDigits d = x}

theorem decimal47Set_eq_range : decimal47Set = range decimal47Value := by
  classical
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun n => decide (d n = 7), ?_⟩
    unfold decimal47Value
    congr 1
    funext n
    rcases hd n with h | h <;> simp [decimal47Digit, h]
  · rintro ⟨a, rfl⟩
    refine ⟨_, fun n => ?_, rfl⟩
    cases a n <;> simp [decimal47Digit]

/-- Every allowed tail is strictly between the two ambiguous endpoint values. -/
theorem decimal47_expansion_bounds {a : ℕ → Fin 10}
    (ha : ∀ n, a n = 4 ∨ a n = 7) :
    0 < Real.ofDigits a ∧ Real.ofDigits a < 1 := by
  rw [Real.ofDigits_eq_sum_add_ofDigits a 1]
  have h0 := Real.ofDigits_nonneg (fun i => a (i + 1))
  have h1 := Real.ofDigits_le_one (fun i => a (i + 1))
  rcases ha 0 with h | h <;> simp [Real.ofDigitsTerm, h] <;> constructor <;> linarith

/-- An allowed string has no second decimal representation, even if the second
string is allowed to use all ten digits. This also excludes endpoint ambiguity. -/
theorem decimal47_expansion_unique_all {a b : ℕ → Fin 10}
    (ha : ∀ n, a n = 4 ∨ a n = 7)
    (h : Real.ofDigits a = Real.ofDigits b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hp : ∑ i ∈ Finset.range n, Real.ofDigitsTerm a i =
        ∑ i ∈ Finset.range n, Real.ofDigitsTerm b i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Real.ofDigitsTerm, ih i (Finset.mem_range.mp hi)]
    have he := h
    rw [Real.ofDigits_eq_sum_add_ofDigits a (n + 1),
      Real.ofDigits_eq_sum_add_ofDigits b (n + 1),
      Finset.sum_range_succ, Finset.sum_range_succ, hp] at he
    have hq : (10 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    have ht : (a n : ℝ) + Real.ofDigits (fun i => a (i + (n + 1))) =
        (b n : ℝ) + Real.ofDigits (fun i => b (i + (n + 1))) := by
      apply (mul_right_inj' (inv_ne_zero hq)).mp
      dsimp [Real.ofDigitsTerm] at he
      nlinarith [he]
    have hta := decimal47_expansion_bounds (fun i => ha (i + (n + 1)))
    have h0b := Real.ofDigits_nonneg (fun i => b (i + (n + 1)))
    have h1b := Real.ofDigits_le_one (fun i => b (i + (n + 1)))
    apply Fin.ext
    apply Nat.le_antisymm
    · by_contra hn
      have hnat : (b n).val + 1 ≤ (a n).val := by omega
      have hreal : (b n : ℝ) + 1 ≤ (a n : ℝ) := by exact_mod_cast hnat
      linarith [hta.1]
    · by_contra hn
      have hnat : (a n).val + 1 ≤ (b n).val := by omega
      have hreal : (a n : ℝ) + 1 ≤ (b n : ℝ) := by exact_mod_cast hnat
      linarith [hta.2]

/-- In particular, two allowed strings have the same value only if they agree. -/
theorem decimal47_expansion_unique {a b : ℕ → Fin 10}
    (ha : ∀ n, a n = 4 ∨ a n = 7) (_hb : ∀ n, b n = 4 ∨ b n = 7)
    (h : Real.ofDigits a = Real.ofDigits b) : a = b :=
  decimal47_expansion_unique_all ha h

theorem decimal47Value_injective : Function.Injective decimal47Value := by
  intro a b h
  have hd := decimal47_expansion_unique
    (a := fun n => decimal47Digit (a n)) (b := fun n => decimal47Digit (b n))
    (fun n => by cases a n <;> simp [decimal47Digit])
    (fun n => by cases b n <;> simp [decimal47Digit]) h
  funext n
  have hn := congrFun hd n
  cases ha : a n <;> cases hb : b n <;> simp_all [decimal47Digit]

theorem decimal47Value_continuous : Continuous decimal47Value :=
  Real.continuous_ofDigits.comp (continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous decimal47Digit).comp (continuous_apply n))

/-- A continuous injective image of binary sequence space is perfect. -/
theorem perfect_range_binary (f : (ℕ → Bool) → ℝ)
    (hc : Continuous f) (hi : Function.Injective f) : Perfect (range f) := by
  refine ⟨?_, ?_⟩
  · simpa only [image_univ] using (isCompact_univ.image hc).isClosed
  rw [preperfect_iff_nhds]
  rintro _ ⟨a, rfl⟩ U hU
  let u : ℕ → (ℕ → Bool) := fun n => Function.update a n (!(a n))
  have hu : Tendsto u atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    simp [u, Function.update_of_ne (ne_of_lt hn)]
  have he : ∀ᶠ n in atTop, f (u n) ∈ U := (hc.tendsto a).comp hu hU
  obtain ⟨n, hn⟩ := he.exists
  refine ⟨f (u n), ⟨hn, mem_range_self _⟩, ?_⟩
  intro he
  have hh := congrFun (hi he) n
  simp [u] at hh

theorem decimal47Set_isCompact : IsCompact decimal47Set := by
  rw [decimal47Set_eq_range]
  simpa only [image_univ] using isCompact_univ.image decimal47Value_continuous

theorem decimal47Set_perfect : Perfect decimal47Set := by
  rw [decimal47Set_eq_range]
  exact perfect_range_binary _ decimal47Value_continuous decimal47Value_injective

theorem decimal47Set_isClosed : IsClosed decimal47Set :=
  decimal47Set_perfect.closed

theorem decimal47Set_no_isolated (x : ℝ) (hx : x ∈ decimal47Set) :
    AccPt x (𝓟 decimal47Set) :=
  decimal47Set_perfect.acc x hx

/-- Cantor's diagonal argument for binary sequences. -/
theorem binary_sequences_not_countable : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨f, hf⟩ := (countable_iff_exists_surjective (α := ℕ → Bool)).mp h
  obtain ⟨n, hn⟩ := hf (fun n => !(f n n))
  have hh := congrFun hn n
  simp at hh

theorem decimal47Set_not_countable : ¬ decimal47Set.Countable := by
  rw [decimal47Set_eq_range]
  intro h
  have := h.to_subtype
  have hi : Function.Injective (fun a =>
      (⟨decimal47Value a, mem_range_self a⟩ : range decimal47Value)) :=
    fun a b hab => decimal47Value_injective (congrArg Subtype.val hab)
  exact binary_sequences_not_countable hi.countable

theorem decimal47Set_subset_unitInterval : decimal47Set ⊆ Icc (0 : ℝ) 1 := by
  rintro x ⟨a, _, rfl⟩
  exact ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

/-- The first digit alone leaves a nonempty interval at the left of the set. -/
theorem decimal47Set_lower_bound {x : ℝ} (hx : x ∈ decimal47Set) : (4 : ℝ) / 10 ≤ x := by
  rcases hx with ⟨a, ha, rfl⟩
  rw [Real.ofDigits_eq_sum_add_ofDigits a 1]
  have ht := Real.ofDigits_nonneg (fun i => a (i + 1))
  rcases ha 0 with h | h <;>
    simp [Real.ofDigitsTerm, h] <;> linarith

theorem decimal47Set_not_dense : ¬ Icc (0 : ℝ) 1 ⊆ closure decimal47Set := by
  intro h
  have hz := h (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  rw [decimal47Set_isCompact.isClosed.closure_eq] at hz
  have := decimal47Set_lower_bound hz
  norm_num at this

/-- The equivalent density statement in the subspace `[0,1]`. -/
theorem decimal47Set_not_dense_subspace :
    ¬ Dense {x : Icc (0 : ℝ) 1 | (x : ℝ) ∈ decimal47Set} := by
  intro h
  have hc : IsClosed {x : Icc (0 : ℝ) 1 | (x : ℝ) ∈ decimal47Set} :=
    decimal47Set_isCompact.isClosed.preimage continuous_subtype_val
  have hz : (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ∈
      {x : Icc (0 : ℝ) 1 | (x : ℝ) ∈ decimal47Set} := by
    rw [← hc.closure_eq]
    exact h _
  have := decimal47Set_lower_bound hz
  norm_num at this

end Rudin.Chapter02
