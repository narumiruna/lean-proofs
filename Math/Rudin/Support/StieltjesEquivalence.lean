module

public import Math.Rudin.Support.StieltjesRefinement

/-!
Equivalence of the tagged refinement criterion and the Darboux definition.
Source: Rudin, Theorems 6.6–6.7, book pages 124–125 (PDF 133–134).
Cell infima and suprema are approximated by tags, not assumed to be attained.
All partitions are the weak partitions of `StieltjesPrototype`; zero increments,
repeated nodes, and singleton intervals require no division by an increment.
-/

@[expose] public section

namespace Rudin.Support.StieltjesEquivalence

open Set StieltjesPrototype StieltjesRefinement

variable {a b : ℝ}

private theorem cell_image_bounds (p : Partition a b) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ Icc a b, |f x| ≤ M) {i : ℕ} (hi : i < p.n) :
    (f '' Icc (p.x i) (p.x (i + 1))).Nonempty ∧
      BddBelow (f '' Icc (p.x i) (p.x (i + 1))) ∧
      BddAbove (f '' Icc (p.x i) (p.x (i + 1))) := by
  refine ⟨⟨_, mem_image_of_mem f (left_isTag p i hi)⟩, ⟨-M, ?_⟩, ⟨M, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hf x (cell_subset p hi hx))).2

/-- Finite tag choices approximate the lower sum, even when an infimum is not attained. -/
theorem exists_taggedSum_near_lowerSum (p : Partition a b) {f α : ℝ → ℝ} {M δ : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hδ : 0 < δ) :
    ∃ tag : ℕ → ℝ, IsTag p tag ∧ lowerSum p f α ≤ taggedSum p f α tag ∧
      taggedSum p f α tag ≤ lowerSum p f α + δ * (α b - α a) := by
  classical
  have hex : ∀ i : Fin p.n, ∃ z : ℝ,
      z ∈ Icc (p.x i) (p.x (i.val + 1)) ∧
        f z ≤ sInf (f '' Icc (p.x i) (p.x (i.val + 1))) + δ := by
    intro i
    have hb := cell_image_bounds p hf i.isLt
    obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hb.1
      (show sInf (f '' Icc (p.x i) (p.x (i.val + 1))) <
        sInf (f '' Icc (p.x i) (p.x (i.val + 1))) + δ by linarith)
    exact ⟨z, hz, hlt.le⟩
  choose cellTag hcellTag using hex
  let tag : ℕ → ℝ := fun i ↦ if hi : i < p.n then cellTag ⟨i, hi⟩ else p.x i
  have htag (i : ℕ) (hi : i < p.n) :
      tag i ∈ Icc (p.x i) (p.x (i + 1)) ∧
        f (tag i) ≤ sInf (f '' Icc (p.x i) (p.x (i + 1))) + δ := by
    simpa only [tag, dite_eq_left hi] using hcellTag ⟨i, hi⟩
  have ht : IsTag p tag := fun i hi ↦ (htag i hi).1
  refine ⟨tag, ht, lowerSum_le_taggedSum p hα hf ht, ?_⟩
  calc
    taggedSum p f α tag ≤ ∑ i ∈ Finset.range p.n,
        (sInf (f '' Icc (p.x i) (p.x (i + 1))) + δ) *
          (α (p.x (i + 1)) - α (p.x i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (htag i (Finset.mem_range.mp hi)).2
        (increment_nonneg p hα (Finset.mem_range.mp hi))
    _ = lowerSum p f α + δ * (α b - α a) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun i ↦ α (p.x i)), p.first, p.last]
      rfl

/-- Finite tag choices approximate the upper sum without an extrema-attainment assumption. -/
theorem exists_taggedSum_near_upperSum (p : Partition a b) {f α : ℝ → ℝ} {M δ : ℝ}
    (hα : MonotoneOn α (Icc a b)) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (hδ : 0 < δ) :
    ∃ tag : ℕ → ℝ, IsTag p tag ∧ taggedSum p f α tag ≤ upperSum p f α ∧
      upperSum p f α - δ * (α b - α a) ≤ taggedSum p f α tag := by
  classical
  have hex : ∀ i : Fin p.n, ∃ z : ℝ,
      z ∈ Icc (p.x i) (p.x (i.val + 1)) ∧
        sSup (f '' Icc (p.x i) (p.x (i.val + 1))) - δ ≤ f z := by
    intro i
    have hb := cell_image_bounds p hf i.isLt
    obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hb.1
      (show sSup (f '' Icc (p.x i) (p.x (i.val + 1))) - δ <
        sSup (f '' Icc (p.x i) (p.x (i.val + 1))) by linarith)
    exact ⟨z, hz, hlt.le⟩
  choose cellTag hcellTag using hex
  let tag : ℕ → ℝ := fun i ↦ if hi : i < p.n then cellTag ⟨i, hi⟩ else p.x i
  have htag (i : ℕ) (hi : i < p.n) :
      tag i ∈ Icc (p.x i) (p.x (i + 1)) ∧
        sSup (f '' Icc (p.x i) (p.x (i + 1))) - δ ≤ f (tag i) := by
    simpa only [tag, dite_eq_left hi] using hcellTag ⟨i, hi⟩
  have ht : IsTag p tag := fun i hi ↦ (htag i hi).1
  refine ⟨tag, ht, taggedSum_le_upperSum p hα hf ht, ?_⟩
  calc
    upperSum p f α - δ * (α b - α a) = ∑ i ∈ Finset.range p.n,
        (sSup (f '' Icc (p.x i) (p.x (i + 1))) - δ) *
          (α (p.x (i + 1)) - α (p.x i)) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun i ↦ α (p.x i)), p.first, p.last]
      rfl
    _ ≤ taggedSum p f α tag := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (htag i (Finset.mem_range.mp hi)).2
        (increment_nonneg p hα (Finset.mem_range.mp hi))

/-- One tagged-criterion partition has lower and upper sums arbitrarily close to the value.
The error scale is `ε / 2 / (α b - α a + 1)`, never a quotient by the total increment. -/
theorem hasRSIntegral_small_darboux_sums {f α : ℝ → ℝ} {value ε : ℝ}
    (h : HasRSIntegral f α a b value) (hε : 0 < ε) :
    ∃ p : Partition a b, value - ε < lowerSum p f α ∧ upperSum p f α < value + ε := by
  obtain ⟨M, hf⟩ := h.2.1
  obtain ⟨p, hp⟩ := h.2.2 (ε / 2) (by linarith)
  have hab : a ≤ b := endpoints_le p
  have hΔ : 0 ≤ α b - α a := sub_nonneg.mpr
    (h.1 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hden : 0 < α b - α a + 1 := by linarith
  let δ := (ε / 2) / (α b - α a + 1)
  have hδ : 0 < δ := div_pos (by linarith) hden
  have hscale : δ * (α b - α a + 1) = ε / 2 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have herror : δ * (α b - α a) < ε / 2 := by nlinarith
  obtain ⟨lowTag, hlowTag, _, hlow⟩ := exists_taggedSum_near_lowerSum p h.1 hf hδ
  obtain ⟨upTag, hupTag, _, hup⟩ := exists_taggedSum_near_upperSum p h.1 hf hδ
  have hl := (abs_lt.mp (hp p (refines_refl p) lowTag hlowTag)).1
  have hu := (abs_lt.mp (hp p (refines_refl p) upTag hupTag)).2
  exact ⟨p, by linarith, by linarith⟩

/-- The tagged refinement criterion implies the literal Darboux definition on `a ≤ b`. -/
theorem hasDarbouxRSIntegral_of_hasRSIntegral (hab : a ≤ b) {f α : ℝ → ℝ} {value : ℝ}
    (h : HasRSIntegral f α a b value) : HasDarbouxRSIntegral f α a b value := by
  obtain ⟨M, hf⟩ := h.2.1
  let L := sSup (Set.range fun p : Partition a b ↦ lowerSum p f α)
  let U := sInf (Set.range fun p : Partition a b ↦ upperSum p f α)
  have hLU : L ≤ U := lowerIntegral_le_upperIntegral hab h.1 hf
  have hvL : value ≤ L := by
    by_contra hn
    have hgap : 0 < value - L := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨p, hp, _⟩ := hasRSIntegral_small_darboux_sums h hgap
    have hpL : lowerSum p f α ≤ L :=
      le_csSup (lowerSum_range_bounded h.1 hf).2 ⟨p, rfl⟩
    linarith
  have hUv : U ≤ value := by
    by_contra hn
    have hgap : 0 < U - value := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨p, _, hp⟩ := hasRSIntegral_small_darboux_sums h hgap
    have hUp : U ≤ upperSum p f α :=
      csInf_le (upperSum_range_bounded h.1 hf).1 ⟨p, rfl⟩
    linarith
  exact ⟨h.1, ⟨M, hf⟩, le_antisymm (hLU.trans hUv) hvL,
    le_antisymm hUv (hvL.trans hLU)⟩

/-- Tagged refinement convergence and Darboux integrability have the same value,
including singleton intervals and partitions with repeated nodes. -/
theorem hasRSIntegral_iff_hasDarbouxRSIntegral (hab : a ≤ b) {f α : ℝ → ℝ} {value : ℝ} :
    HasRSIntegral f α a b value ↔ HasDarbouxRSIntegral f α a b value :=
  ⟨hasDarbouxRSIntegral_of_hasRSIntegral hab,
    hasRSIntegral_of_hasDarbouxRSIntegral hab⟩

end Rudin.Support.StieltjesEquivalence
