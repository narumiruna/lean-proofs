module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# R02E30: Baire's theorem in Euclidean space

Source: Rudin, Third Edition, book page 46 (PDF page 55).
The families are indexed from zero: `F n` and `G n` denote the source's
`F_{n+1}` and `G_{n+1}`. No restriction on the dimension is imposed.

The proof constructs positive-radius nested closed balls inside each prescribed
open set, then applies the compact nested-set theorem, as in Theorem 2.43.
It does not assume a Baire-space instance or invoke a Baire theorem.
-/

@[expose] public section

namespace Rudin.Chapter02

open Set Metric Topology

/-- The nested balls used in the proof. The first ball lies in an arbitrary
nonempty open set `U`; each next ball lies in the preceding ball and in `G n`. -/
theorem exercise30_nested_balls {k : ℕ}
    (G : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (ho : ∀ n, IsOpen (G n)) (hd : ∀ n, Dense (G n))
    {U : Set (EuclideanSpace ℝ (Fin k))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (c : ℕ → EuclideanSpace ℝ (Fin k)) (r : ℕ → ℝ),
      (∀ n, 0 < r n) ∧ closedBall (c 0) (r 0) ⊆ U ∧
      ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆
        closedBall (c n) (r n) ∩ G n := by
  classical
  let E := EuclideanSpace ℝ (Fin k)
  have small_ball : ∀ V : Set E, IsOpen V → V.Nonempty →
      ∃ p : E × ℝ, 0 < p.2 ∧ closedBall p.1 p.2 ⊆ V := by
    intro V hV ⟨x, hx⟩
    obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
    exact ⟨(x, r), hr, hsub⟩
  let B := {p : E × ℝ // 0 < p.2}
  obtain ⟨p₀, hp₀, hpU⟩ := small_ball U hU hne
  have step : ∀ (n : ℕ) (p : B), ∃ q : B,
      closedBall q.1.1 q.1.2 ⊆ closedBall p.1.1 p.1.2 ∩ G n := by
    intro n p
    have hne' : (ball p.1.1 p.1.2 ∩ G n).Nonempty :=
      (hd n).inter_open_nonempty _ isOpen_ball ⟨p.1.1, mem_ball_self p.2⟩
    obtain ⟨q, hq, hsub⟩ :=
      small_ball _ (isOpen_ball.inter (ho n)) hne'
    exact ⟨⟨q, hq⟩, fun x hx =>
      ⟨ball_subset_closedBall (hsub hx).1, (hsub hx).2⟩⟩
  choose next hnext using step
  let b : ℕ → B := Nat.rec ⟨p₀, hp₀⟩ next
  exact ⟨fun n => (b n).1.1, fun n => (b n).1.2,
    fun n => (b n).2, hpU, fun n => hnext n (b n)⟩

/-- R02E30.open_intersection_dense: the nested compact balls have a common point
in `U ∩ ⋂ n, G n`, for every nonempty open `U`. -/
theorem exercise30_open_intersection_dense {k : ℕ}
    (G : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (ho : ∀ n, IsOpen (G n)) (hd : ∀ n, Dense (G n)) :
    Dense (⋂ n, G n) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨c, r, hr, hU₀, hstep⟩ := exercise30_nested_balls G ho hd hU hne
  have hcommon : (⋂ n, closedBall (c n) (r n)).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => (hstep n).trans inter_subset_left)
      (fun n => ⟨c n, mem_closedBall_self (hr n).le⟩)
      (isCompact_closedBall _ _) (fun _ => isClosed_closedBall)
  obtain ⟨x, hx⟩ := hcommon
  have hxball : ∀ n, x ∈ closedBall (c n) (r n) := mem_iInter.mp hx
  exact ⟨x, hU₀ (hxball 0), mem_iInter.mpr
    (fun n => (hstep n (hxball (n + 1))).2)⟩

/-- R02E30.open_intersection_nonempty. Euclidean space contains zero even when
`k = 0`, so density gives nonemptiness in every dimension. -/
theorem exercise30_open_intersection_nonempty {k : ℕ}
    (G : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (ho : ∀ n, IsOpen (G n)) (hd : ∀ n, Dense (G n)) :
    (⋂ n, G n).Nonempty :=
  (exercise30_open_intersection_dense G ho hd).nonempty

/-- R02E30.closed_cover: if every closed member had empty interior, the nested
balls for their open complements would give a point outside the cover. -/
theorem exercise30_closed_cover {k : ℕ}
    (F : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (hc : ∀ n, IsClosed (F n)) (hcover : (⋃ n, F n) = univ) :
    ∃ n, (interior (F n)).Nonempty := by
  classical
  by_contra h
  have hempty : ∀ n, interior (F n) = ∅ := by
    intro n
    exact Set.not_nonempty_iff_eq_empty.mp (fun hn => h ⟨n, hn⟩)
  have hd : ∀ n, Dense (F n)ᶜ := fun n =>
    interior_eq_empty_iff_dense_compl.mp (hempty n)
  obtain ⟨x, hx⟩ := exercise30_open_intersection_nonempty
    (fun n => (F n)ᶜ) (fun n => (hc n).isOpen_compl) hd
  have hxcover : x ∈ ⋃ n, F n := hcover ▸ mem_univ x
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxcover
  exact (mem_iInter.mp hx n) hn

end Rudin.Chapter02
