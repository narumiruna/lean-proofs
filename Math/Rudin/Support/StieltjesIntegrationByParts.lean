module

public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComposition
public import Math.Rudin.Chapter05.Exercise08

/-!
# Integration by parts for a raw monotone integrator

The proof uses actual tagged sums and discrete summation by parts. Uniform
within-interval differentiation controls the remainder. No continuity of the
integrator, measure normalization, or integration-by-parts identity is assumed.
Source: Rudin, Chapter 6, Exercise 17, book page 141 (PDF 150).
-/

@[expose] public section

namespace Rudin.Support.StieltjesIntegrationByParts

open Set StieltjesPrototype StieltjesRefinement StieltjesEquivalence
open StieltjesIntegralLaws StieltjesMeasureBridge StieltjesComposition RiemannIntegrability

variable {a b : ℝ}

/-- Uniform grids make every closed cell short, including on singleton intervals. -/
theorem exists_fine_partition (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : Partition a b, ∀ i < p.n, p.x (i + 1) - p.x i < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : 0 < n := by
    have hnonneg : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.mpr hab) hδ.le
    exact_mod_cast lt_of_le_of_lt hnonneg hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hm : (b - a) / n < δ := by
    apply (div_lt_iff₀ hnreal).mpr
    have hh := (div_lt_iff₀ hδ).mp hn
    nlinarith
  exact ⟨uniformGrid hab n hnpos, fun i _ => (uniformGrid_cell_length hab n hnpos i).trans_lt hm⟩

/-- Vertex-subset refinement cannot enlarge a cell. Repeated vertices are allowed. -/
theorem refinement_mesh_lt {fine coarse : Partition a b} (h : Refines fine coarse)
    {δ : ℝ} (hm : ∀ i < coarse.n, coarse.x (i + 1) - coarse.x i < δ) :
    ∀ j < fine.n, fine.x (j + 1) - fine.x j < δ := by
  intro j hj
  have hj' : j ∈ Ico (refinementIndex fine coarse 0)
      (refinementIndex fine coarse coarse.n) := by simpa using And.intro (Nat.zero_le j) hj
  obtain ⟨i, hi, hji⟩ := Set.mem_iUnion₂.mp
    (Ico_subset_biUnion_Ico coarse.n (refinementIndex fine coarse) hj')
  have hi' := Finset.mem_range.mp hi
  have hs := refinement_cell_subset h hi' (Finset.mem_Ico.mpr hji)
  have hl := hs (left_isTag fine j hj)
  have hu := hs (show fine.x (j + 1) ∈ Icc (fine.x j) (fine.x (j + 1)) from
    ⟨(left_isTag fine j hj).2, le_rfl⟩)
  linarith [hm i hi', hl.1, hu.2]

/-- The exact finite summation-by-parts identity for the actual partition nodes. -/
theorem discrete_parts (p : Partition a b) (G α : ℝ → ℝ) :
    taggedSum p G α (fun i => p.x (i + 1)) +
      (∑ i ∈ Finset.range p.n, α (p.x i) * (G (p.x (i + 1)) - G (p.x i))) =
        G b * α b - G a * α a := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ Finset.range p.n,
        (G (p.x (i + 1)) * α (p.x (i + 1)) - G (p.x i) * α (p.x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_range_sub (fun i => G (p.x i) * α (p.x i)), p.first, p.last]

/-- Uniform differentiation bounds the actual discrete remainder, not just
its formal coefficients. Zero-length cells give exactly zero error. -/
theorem discrete_remainder_le (p : Partition a b) {G g α : ℝ → ℝ} {C ε δ : ℝ}
    (hC : 0 ≤ C)
    (hα : ∀ x ∈ Icc a b, |α x| ≤ C)
    (hm : ∀ i < p.n, p.x (i + 1) - p.x i < δ)
    (hd : ∀ x ∈ Icc a b, ∀ t ∈ Icc a b,
      0 < |t - x| → |t - x| < δ → |(G t - G x) / (t - x) - g x| < ε) :
    |(∑ i ∈ Finset.range p.n, α (p.x i) * (G (p.x (i + 1)) - G (p.x i))) -
      taggedSum p (fun x => α x * g x) id p.x| ≤ C * ε * (b - a) := by
  have hc (i : ℕ) (hi : i < p.n) :
      |α (p.x i) * (G (p.x (i + 1)) - G (p.x i)) -
        (α (p.x i) * g (p.x i)) * (p.x (i + 1) - p.x i)| ≤
          C * ε * (p.x (i + 1) - p.x i) := by
    have hxl := cell_subset p hi (left_isTag p i hi)
    have hxu := cell_subset p hi (show p.x (i + 1) ∈ Icc (p.x i) (p.x (i + 1)) from
      ⟨(left_isTag p i hi).2, le_rfl⟩)
    have hw : 0 ≤ p.x (i + 1) - p.x i := sub_nonneg.mpr (left_isTag p i hi).2
    by_cases hz : p.x (i + 1) - p.x i = 0
    · have he : p.x (i + 1) = p.x i := sub_eq_zero.mp hz
      simp only [he, sub_self, mul_zero, abs_zero, le_refl]
    · have hp : 0 < p.x (i + 1) - p.x i := lt_of_le_of_ne hw (Ne.symm hz)
      have hd' := hd (p.x i) hxl (p.x (i + 1)) hxu
        (by simpa only [abs_of_nonneg hw] using hp)
        (by simpa only [abs_of_nonneg hw] using hm i hi)
      have he : G (p.x (i + 1)) - G (p.x i) - g (p.x i) * (p.x (i + 1) - p.x i) =
          ((G (p.x (i + 1)) - G (p.x i)) / (p.x (i + 1) - p.x i) - g (p.x i)) *
            (p.x (i + 1) - p.x i) := by field_simp
      have herr : |G (p.x (i + 1)) - G (p.x i) - g (p.x i) * (p.x (i + 1) - p.x i)| ≤
          ε * (p.x (i + 1) - p.x i) := by
        rw [he, abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_right hd'.le hw
      calc
        _ = |α (p.x i)| * |G (p.x (i + 1)) - G (p.x i) -
            g (p.x i) * (p.x (i + 1) - p.x i)| := by rw [← abs_mul]; congr 1; ring
        _ ≤ C * (ε * (p.x (i + 1) - p.x i)) :=
          mul_le_mul (hα (p.x i) hxl) herr (abs_nonneg _) hC
        _ = _ := by ring
  unfold taggedSum
  simp only [id_eq]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range p.n,
        |α (p.x i) * (G (p.x (i + 1)) - G (p.x i)) -
          (α (p.x i) * g (p.x i)) * (p.x (i + 1) - p.x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range p.n, C * ε * (p.x (i + 1) - p.x i) :=
      Finset.sum_le_sum (fun i hi => hc i (Finset.mem_range.mp hi))
    _ = _ := by simpa only [taggedSum, id_eq] using taggedSum_const p id (C * ε) p.x

/-- The value identity follows from actual integral convergence and genuine
within derivatives. The integral-existence theorem below supplies both values. -/
theorem parts_of_integrals {G g α : ℝ → ℝ} {A B : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (g x) (Icc a b) x)
    (hA : HasRSIntegral (fun x => α x * g x) id a b A)
    (hB : HasRSIntegral G α a b B) :
    A + B = G b * α b - G a * α a := by
  let C := |α a| + |α b| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hα : ∀ x ∈ Icc a b, |α x| ≤ C := by
    intro x hx
    have hl := hB.1 ⟨le_rfl, hab⟩ hx hx.1
    have hu := hB.1 hx ⟨hab, le_rfl⟩ hx.2
    apply abs_le.mpr
    constructor <;> dsimp only [C] <;>
      linarith [neg_abs_le (α a), le_abs_self (α b), abs_nonneg (α a), abs_nonneg (α b)]
  by_contra hne
  have hpos : 0 < |A + B - (G b * α b - G a * α a)| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  let ε := |A + B - (G b * α b - G a * α a)| / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab
  let η := ε / ((C + 1) * (b - a + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hscale : η * ((C + 1) * (b - a + 1)) = ε := by
    exact div_mul_cancel₀ _ (by positivity)
  have hsmall : C * η * (b - a) < ε := by
    nlinarith [mul_nonneg hη.le hC, mul_nonneg hη.le hL]
  obtain ⟨δ, hδ, hmod⟩ := Rudin.Chapter05.exercise08_uniform_differentiability hG hg hη
  obtain ⟨r, hr⟩ := exists_fine_partition hab hδ
  obtain ⟨p, hp⟩ := common_control hA hB (ε := ε) (δ := ε) hε hε
  let q := commonRefinement p r
  have hqp : Refines q p := commonRefinement_refines_left p r
  have hqr : Refines q r := commonRefinement_refines_right p r
  have hmesh := refinement_mesh_lt hqr hr
  have htleft : IsTag q q.x := fun i hi => left_isTag q i hi
  have htright : IsTag q (fun i => q.x (i + 1)) := fun i hi =>
    ⟨(left_isTag q i hi).2, le_rfl⟩
  let L := taggedSum q (fun x => α x * g x) id q.x
  let R := taggedSum q G α (fun i => q.x (i + 1))
  let T := ∑ i ∈ Finset.range q.n, α (q.x i) * (G (q.x (i + 1)) - G (q.x i))
  have h₁ : |L - A| < ε := (hp q hqp q.x htleft).1
  have h₂ : |R - B| < ε := (hp q hqp (fun i => q.x (i + 1)) htright).2
  have h₃ : |T - L| ≤ C * η * (b - a) := discrete_remainder_le q hC hα hmesh hmod
  have he : R + T = G b * α b - G a * α a := discrete_parts q G α
  have heq : A + B - (G b * α b - G a * α a) = (A - L) + (B - R) + (L - T) := by
    linarith
  have htri : |(A - L) + (B - R) + (L - T)| ≤ |A - L| + |B - R| + |L - T| := by
    linarith [abs_add_le ((A - L) + (B - R)) (L - T), abs_add_le (A - L) (B - R)]
  have h₁' : |A - L| < ε := by simpa only [abs_sub_comm] using h₁
  have h₂' : |B - R| < ε := by simpa only [abs_sub_comm] using h₂
  have h₃' : |L - T| < ε := by
    rw [abs_sub_comm]
    exact h₃.trans_lt hsmall
  rw [← heq] at htri
  dsimp only [ε] at h₁' h₂' h₃'
  linarith

/-- Both integrals exist, and their values satisfy the raw integration-by-parts
identity. The monotone integrator may be discontinuous, including at endpoints. -/
theorem stieltjes_parts {G g α : ℝ → ℝ} (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (g x) (Icc a b) x) :
    ∃ A B : ℝ, HasDarbouxRSIntegral (fun x => α x * g x) id a b A ∧
      HasDarbouxRSIntegral G α a b B ∧ A = G b * α b - G a * α a - B := by
  have hαR := hasDarbouxRSIntegral_of_monotoneOn hab hα
  obtain ⟨v, hv⟩ := StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab
    (show MonotoneOn id (Icc a b) from fun _ _ _ _ h => h) hg
  obtain ⟨A, hA⟩ := StieltjesComposition.exists_product hab hαR hv
  have hGc : ContinuousOn G (Icc a b) := fun x hx => (hG x hx).continuousWithinAt
  obtain ⟨B, hB⟩ := StieltjesMeasureBridge.exists_hasDarbouxRSIntegral hab hα hGc
  have he := parts_of_integrals hab hg hG
    (hasRSIntegral_of_hasDarbouxRSIntegral hab hA) (hasRSIntegral_of_hasDarbouxRSIntegral hab hB)
  exact ⟨A, B, hA, hB, by linarith⟩

end Rudin.Support.StieltjesIntegrationByParts
