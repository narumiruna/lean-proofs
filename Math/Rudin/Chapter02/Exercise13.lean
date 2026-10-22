module

public import Math.Rudin.Chapter02.Exercise12
public import Mathlib.Topology.Sequences

/-!
# R02E13: a compact set with countably infinitely many accumulation points

Source: Rudin, Exercise 2.13, book page 44 (PDF page 53).
Let A be zero together with the positive reciprocals, and let K = A + A.
The continuous addition map on A × A proves compactness. The exact derived
set of K is A. In the upper inclusion, compactness gives convergent
subsequences of both summands. If both limits are nonzero, the summands
are eventually constant, contrary to accumulation.
-/

@[expose] public section

open Set Filter Topology

namespace Rudin.Chapter02

/-- Sums of two elements of the reciprocal set. -/
def doubleReciprocalSet : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 + p.2) '' (reciprocalSet ×ˢ reciprocalSet)

/-- Compactness follows from the compact product and continuity of addition. -/
theorem doubleReciprocalSet_compact : IsCompact doubleReciprocalSet :=
  (exercise12.prod exercise12).image (continuous_fst.add continuous_snd)

/-- A convergent sequence in the reciprocal set is eventually constant if its limit is nonzero. -/
theorem reciprocalSet_eventually_eq {u : ℕ → ℝ} {a : ℝ}
    (hu : Tendsto u atTop (𝓝 a)) (hmem : ∀ n, u n ∈ reciprocalSet) (ha : a ≠ 0) :
    ∀ᶠ n in atTop, u n = a := by
  have hna : ¬AccPt a (𝓟 reciprocalSet) := by
    change a ∉ derivedSet reciprocalSet
    simpa [derivedSet_reciprocalSet] using ha
  rw [accPt_iff_nhds] at hna
  push Not at hna
  obtain ⟨U, hU, hisol⟩ := hna
  filter_upwards [show ∀ᶠ n in atTop, u n ∈ U from hu hU] with n hn
  exact hisol (u n) ⟨hn, hmem n⟩

/-- Every accumulation point of the sum set is in the reciprocal set. -/
theorem derivedSet_doubleReciprocalSet_subset :
    derivedSet doubleReciprocalSet ⊆ reciprocalSet := by
  intro x hx
  have hc : x ∈ closure (doubleReciprocalSet \ {x}) :=
    (accPt_principal_iff_clusterPt.mp hx).mem_closure
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hc
  have hdecomp (n : ℕ) : ∃ p : ℝ × ℝ,
      p ∈ reciprocalSet ×ˢ reciprocalSet ∧ p.1 + p.2 = u n := (hu n).1
  choose v hv hvu using hdecomp
  obtain ⟨p, hp, φ, hφ, hvp⟩ := (exercise12.prod exercise12).tendsto_subseq hv
  have h₁ : Tendsto (fun n => (v (φ n)).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hvp
  have h₂ : Tendsto (fun n => (v (φ n)).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hvp
  have hsum : Tendsto (fun n => u (φ n)) atTop (𝓝 (p.1 + p.2)) := by
    simpa only [hvu] using h₁.add h₂
  have hpx : p.1 + p.2 = x :=
    tendsto_nhds_unique hsum (hux.comp hφ.tendsto_atTop)
  by_cases hp₁ : p.1 = 0
  · rw [← hpx, hp₁, zero_add]
    exact hp.2
  by_cases hp₂ : p.2 = 0
  · rw [← hpx, hp₂, add_zero]
    exact hp.1
  have he₁ := reciprocalSet_eventually_eq h₁ (fun n => (hv (φ n)).1) hp₁
  have he₂ := reciprocalSet_eventually_eq h₂ (fun n => (hv (φ n)).2) hp₂
  obtain ⟨n, hn₁, hn₂⟩ := (he₁.and he₂).exists
  exact False.elim (((hu (φ n)).2) (by rw [← hvu, hn₁, hn₂, hpx]; rfl))

/-- Every reciprocal, including zero, is an accumulation point of the sum set. -/
theorem reciprocalSet_subset_derivedSet_doubleReciprocalSet :
    reciprocalSet ⊆ derivedSet doubleReciprocalSet := by
  intro a ha
  have ht : Tendsto (fun n => a + reciprocalTerm n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add reciprocalTerm_tendsto
  have hd := limit_mem_derivedSet_range ht (fun n => by
    have := reciprocalTerm_pos n
    linarith)
  apply derivedSet_mono _ _ ?_ hd
  rintro y ⟨n, rfl⟩
  exact ⟨(a, reciprocalTerm n), ⟨ha, mem_insert_of_mem _ (mem_range_self n)⟩, rfl⟩

/-- The derived set is exactly zero together with the positive reciprocals. -/
theorem derivedSet_doubleReciprocalSet :
    derivedSet doubleReciprocalSet = reciprocalSet :=
  Subset.antisymm derivedSet_doubleReciprocalSet_subset
    reciprocalSet_subset_derivedSet_doubleReciprocalSet

/-- The exact derived set is countably infinite. -/
theorem doubleReciprocalSet_derived_countably_infinite :
    (derivedSet doubleReciprocalSet).Countable ∧ (derivedSet doubleReciprocalSet).Infinite := by
  rw [derivedSet_doubleReciprocalSet]
  exact ⟨reciprocalSet_countable, reciprocalSet_infinite⟩

/-- An explicit compact real set with the specified countably infinite derived set. -/
theorem exercise13 : IsCompact doubleReciprocalSet ∧
    derivedSet doubleReciprocalSet = reciprocalSet ∧
    (derivedSet doubleReciprocalSet).Countable ∧ (derivedSet doubleReciprocalSet).Infinite :=
  ⟨doubleReciprocalSet_compact, derivedSet_doubleReciprocalSet,
    doubleReciprocalSet_derived_countably_infinite⟩

end Rudin.Chapter02
