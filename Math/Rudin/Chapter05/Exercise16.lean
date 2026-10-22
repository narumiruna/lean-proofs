module

public import Math.Rudin.Chapter05.Exercise15

@[expose] public section

namespace Rudin.Chapter05

open Set Filter

/-- Rudin 5.16, in the stronger normed-space form. Only existence of the
    first two derivatives and boundedness of the second derivative are used. -/
theorem exercise16_derivative_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E}
    (hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f₁ x) x)
    (hd₁ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f₁ (f₂ x) x)
    (hbound : ∃ B : ℝ, ∀ x ∈ Ioi (0 : ℝ), ‖f₂ x‖ ≤ B)
    (hf : Tendsto f atTop (nhds 0)) : Tendsto f₁ atTop (nhds 0) := by
  rcases hbound with ⟨B, hB⟩
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 1 (by simp))
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε ^ 2 / (8 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1 hf δ hδ
  refine ⟨max A 0 + 1, fun x hx => ?_⟩
  have ht : ∀ t ∈ Ioi (max A 0), 0 < t := fun t ht => lt_of_le_of_lt (le_max_right _ _) ht
  have hp := exercise15_pointwise_bound
    (fun t ht' => hd t (ht t ht')) (fun t ht' => hd₁ t (ht t ht'))
    (M₀ := δ) (M₂ := B)
    (fun t ht' => by
      have := hA t (le_trans (le_max_left _ _) (le_of_lt ht'))
      simpa [dist_zero_right] using this.le)
    (fun t ht' => hB t (ht t ht')) x (by change max A 0 < x; linarith)
  have hs : 4 * δ * B < ε ^ 2 := by
    dsimp [δ]
    rw [show 4 * (ε ^ 2 / (8 * (B + 1))) * B =
      (4 * ε ^ 2 * B) / (8 * (B + 1)) by ring]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (B + 1))).2
    nlinarith [sq_pos_of_pos hε]
  rw [dist_zero_right]
  nlinarith [norm_nonneg (f₁ x)]

end Rudin.Chapter05
