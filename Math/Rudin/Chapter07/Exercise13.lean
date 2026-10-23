module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter07

/-- At a continuity point of the proposed limit, convergence on rational arguments
extends to convergence of monotone functions at that point. -/
theorem exercise13_squeeze_at {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hm : ∀ n, Monotone (f n)) (hc : ContinuousAt g x)
    (hq : ∀ q : ℚ, Tendsto (fun n => f n q) atTop (𝓝 (g q))) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (g x - a) (sub_pos.mpr ha)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x - δ < x by linarith)
    have hqd : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hq₂)]
      linarith
    have hga : a < g q := by
      have := (abs_lt.mp (show |g q - g x| < g x - a from hd hqd)).1
      linarith
    filter_upwards [(hq q).eventually (Ioi_mem_nhds hga)] with n hn
    exact hn.trans_le (hm n hq₂.le)
  · intro b hb
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (b - g x) (sub_pos.mpr hb)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x < x + δ by linarith)
    have hqd : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq₁)]
      linarith
    have hgb : g q < b := by
      have := (abs_lt.mp (show |g q - g x| < b - g x from hd hqd)).2
      linarith
    filter_upwards [(hq q).eventually (Iio_mem_nhds hgb)] with n hn
    exact (hm n hq₁.le).trans_lt hn

/-- Helly selection on the whole real line. The selected sequence converges at every
point, including every discontinuity of its monotone limit. -/
theorem exercise13_helly_selection {f : ℕ → ℝ → ℝ}
    (hm : ∀ n, Monotone (f n)) (hb : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ g : ℝ → ℝ,
      Monotone g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x, Tendsto (fun n => f (k n) x) atTop (𝓝 (g x)) := by
  classical
  have hcompact : IsCompact (Set.pi univ (fun _ : ℝ => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨g, hg, hcluster⟩ := hcompact.exists_mapClusterPt
    (show map f atTop ≤ 𝓟 (Set.pi univ (fun _ : ℝ => Icc (0 : ℝ) 1)) from
      Filter.tendsto_principal.mpr (Eventually.of_forall (fun n x _ => hb n x)))
  have hgm : Monotone g := isClosed_monotone.mem_of_mapClusterPt hcluster
    (Eventually.of_forall hm)
  let D : Set ℝ := range (fun q : ℚ => (q : ℝ)) ∪ {x | ¬ ContinuousAt g x}
  have hD : D.Countable := (countable_range _).union hgm.countable_not_continuousAt
  let : Countable D := hD.to_subtype
  have hc : Continuous (fun h : ℝ → ℝ => fun x : D => h x) :=
    continuous_pi (fun x => continuous_apply x.val)
  obtain ⟨k, hk, hkg⟩ := (hcluster.continuousAt_comp hc.continuousAt).tendsto_subseq
  have hDlim : ∀ x : D, Tendsto (fun n => f (k n) x) atTop (𝓝 (g x)) :=
    fun x => (tendsto_pi_nhds.mp hkg) x
  refine ⟨k, hk, g, hgm, fun x => hg x (mem_univ x), fun x => ?_⟩
  by_cases hx : ContinuousAt g x
  · apply exercise13_squeeze_at (fun n => hm (k n)) hx
    intro q
    exact hDlim ⟨q, Or.inl (mem_range_self q)⟩
  · exact hDlim ⟨x, Or.inr hx⟩

/-- A continuous pointwise limit of functions monotone in the real argument is a
locally uniform limit. No monotonicity in the sequence index is assumed. -/
theorem exercise13_locally_uniform {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hm : ∀ n, Monotone (f n)) (hc : Continuous g)
    (hp : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoLocallyUniformly f g atTop := by
  apply Metric.tendstoLocallyUniformly_iff.mpr
  intro ε hε x
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := x))
    (ε / 3) (by positivity)
  have hl : dist (g (x - δ / 2)) (g x) < ε / 3 := hd (by
    rw [Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg,
      abs_of_pos (by positivity : 0 < δ / 2)]
    linarith)
  have hr : dist (g (x + δ / 2)) (g x) < ε / 3 := hd (by
    rw [Real.dist_eq, show x + δ / 2 - x = δ / 2 by ring,
      abs_of_pos (by positivity : 0 < δ / 2)]
    linarith)
  refine ⟨Ioo (x - δ / 2) (x + δ / 2), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  have hleft := (tendsto_order.mp (hp (x - δ / 2))).1
    (g (x - δ / 2) - ε / 3) (by linarith)
  have hright := (tendsto_order.mp (hp (x + δ / 2))).2
    (g (x + δ / 2) + ε / 3) (by linarith)
  filter_upwards [hleft, hright] with n hn₁ hn₂ y hy
  have hyd : dist y x < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hgy := hd hyd
  have hm₁ := hm n hy.1.le
  have hm₂ := hm n hy.2.le
  rw [Real.dist_eq, abs_lt] at hl hr hgy ⊢
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2, hgy.1, hgy.2]

/-- The selected sequence converges uniformly on every compact subset whenever its
limit is continuous. This theorem also applies to any other pointwise convergent subsequence. -/
theorem exercise13_uniform_on_compact {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hm : ∀ n, Monotone (f n)) {k : ℕ → ℕ} (hc : Continuous g)
    (hp : ∀ x, Tendsto (fun n => f (k n) x) atTop (𝓝 (g x)))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => f (k n)) g atTop K :=
  tendstoLocallyUniformly_iff_forall_isCompact.mp
    (exercise13_locally_uniform (fun n => hm (k n)) hc hp) K hK

/-- Both parts of the source selection theorem in one statement. -/
theorem exercise13 {f : ℕ → ℝ → ℝ}
    (hm : ∀ n, Monotone (f n)) (hb : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ g : ℝ → ℝ,
      (∀ x, Tendsto (fun n => f (k n) x) atTop (𝓝 (g x))) ∧
      (Continuous g → ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n => f (k n)) g atTop K) := by
  obtain ⟨k, hk, g, _, _, hp⟩ := exercise13_helly_selection hm hb
  exact ⟨k, hk, g, hp, fun hc K hK => exercise13_uniform_on_compact hm hc hp K hK⟩

end Rudin.Chapter07
