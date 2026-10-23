module

public import Math.Rudin.Support.StieltjesComplex
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Ring.Periodic

/-!
# Literal Riemann transport under translation and reflection

The proofs transport actual weak partitions and closed-cell tags. They do not
infer Riemann integrability from Bochner integrability. Repeated nodes and
singleton intervals are retained. The integrator in the transport results is
`id`; no right normalization of a Stieltjes integrator is used.
-/

@[expose] public section

noncomputable section

namespace Rudin.Support.RiemannAffine

open Set StieltjesPrototype StieltjesRefinement StieltjesEquivalence
open StieltjesIntegralLaws StieltjesComplex

variable {a b c d v : ℝ} {f : ℝ → ℝ}

/-- Translate nodes, retaining every cell, including zero-length cells. -/
def translatePartition (p : Partition a b) (k : ℝ)
    (hc : c + k = a) (hd : d + k = b) : Partition c d where
  n := p.n
  pos := p.pos
  x := fun i => p.x i - k
  first := by rw [p.first]; linarith
  last := by rw [p.last]; linarith
  increasing := fun _ hi _ hj hij => sub_le_sub_right (p.increasing hi hj hij) k

/-- Reverse the nodes and reflect their values. -/
def reflectPartition (p : Partition a b) (k : ℝ)
    (hc : k - d = a) (hd : k - c = b) : Partition c d where
  n := p.n
  pos := p.pos
  x := fun i => k - p.x (p.n - i)
  first := by simp only [Nat.sub_zero, p.last]; linarith
  last := by simp only [Nat.sub_self, p.first]; linarith
  increasing := by
    intro i hi j hj hij
    exact sub_le_sub_left (p.increasing (Nat.sub_le _ _) (Nat.sub_le _ _)
      (Nat.sub_le_sub_left hij _)) k

/-- Translation preserves the actual tagged criterion and its value. -/
theorem hasRSIntegral_translate (hf : HasRSIntegral f id a b v) (k : ℝ)
    (hc : c + k = a) (hd : d + k = b) :
    HasRSIntegral (fun t => f (t + k)) id c d v := by
  obtain ⟨M, hM⟩ := hf.2.1
  refine ⟨monotone_id.monotoneOn _, ⟨M, ?_⟩, ?_⟩
  · intro t ht
    apply hM
    constructor <;> linarith [ht.1, ht.2]
  · intro ε hε
    obtain ⟨p, hp⟩ := hf.2.2 ε hε
    refine ⟨translatePartition p k hc hd, ?_⟩
    intro q hq tag ht
    let r : Partition a b := translatePartition q (-k) (by linarith) (by linarith)
    have hr : Refines r p := by
      rintro _ ⟨i, hi, rfl⟩
      have hnode : p.x i - k ∈ q.x '' Iic q.n :=
        hq ⟨i, hi, rfl⟩
      obtain ⟨j, hj, he⟩ := hnode
      refine ⟨j, hj, ?_⟩
      change q.x j - -k = p.x i
      linarith
    have htag : IsTag r (fun i => tag i + k) := by
      intro i hi
      have h := ht i hi
      change q.x i - -k ≤ tag i + k ∧ tag i + k ≤ q.x (i + 1) - -k
      constructor <;> linarith [h.1, h.2]
    have he : taggedSum r f id (fun i => tag i + k) =
        taggedSum q (fun t => f (t + k)) id tag := by
      unfold taggedSum
      apply Finset.sum_congr rfl
      intro i _
      dsimp [r, translatePartition]
      congr 1; ring
    simpa only [he] using hp r hr _ htag

/-- Reflection reverses the cell order, not the sign of the ordered integral. -/
theorem hasRSIntegral_reflect (hf : HasRSIntegral f id a b v) (k : ℝ)
    (hc : k - d = a) (hd : k - c = b) :
    HasRSIntegral (fun t => f (k - t)) id c d v := by
  obtain ⟨M, hM⟩ := hf.2.1
  refine ⟨monotone_id.monotoneOn _, ⟨M, ?_⟩, ?_⟩
  · intro t ht
    apply hM
    constructor <;> linarith [ht.1, ht.2]
  · intro ε hε
    obtain ⟨p, hp⟩ := hf.2.2 ε hε
    refine ⟨reflectPartition p k hc hd, ?_⟩
    intro q hq tag ht
    let r : Partition a b := reflectPartition q k (by linarith) (by linarith)
    have hr : Refines r p := by
      rintro _ ⟨i, hi, rfl⟩
      have hidx : p.n - (p.n - i) = i := by change i ≤ p.n at hi; omega
      have hnode : k - p.x i ∈ q.x '' Iic q.n := by
        apply hq
        exact ⟨p.n - i, Nat.sub_le _ _, by dsimp [reflectPartition]; rw [hidx]⟩
      obtain ⟨j, hj, he⟩ := hnode
      refine ⟨q.n - j, Nat.sub_le _ _, ?_⟩
      change k - q.x (q.n - (q.n - j)) = p.x i
      rw [Nat.sub_sub_self hj]
      linarith
    have htag : IsTag r (fun i => k - tag (q.n - 1 - i)) := by
      intro i hi
      change i < q.n at hi
      have hj : q.n - 1 - i < q.n := by omega
      have h := ht _ hj
      change k - q.x (q.n - i) ≤ k - tag (q.n - 1 - i) ∧
        k - tag (q.n - 1 - i) ≤ k - q.x (q.n - (i + 1))
      have he₁ : q.n - 1 - i + 1 = q.n - i := by omega
      have he₂ : q.n - (i + 1) = q.n - 1 - i := by omega
      rw [he₁] at h
      rw [he₂]
      constructor <;> linarith [h.1, h.2]
    have he : taggedSum r f id (fun i => k - tag (q.n - 1 - i)) =
        taggedSum q (fun t => f (k - t)) id tag := by
      unfold taggedSum
      change (∑ i ∈ Finset.range q.n,
        f (k - tag (q.n - 1 - i)) *
          ((k - q.x (q.n - (i + 1))) - (k - q.x (q.n - i)))) = _
      rw [← Finset.sum_range_reflect (fun i => f (k - tag i) *
        (id (q.x (i + 1)) - id (q.x i))) q.n]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have he₁ : q.n - 1 - i + 1 = q.n - i := by omega
      have he₂ : q.n - (i + 1) = q.n - 1 - i := by omega
      rw [he₁, he₂]
      dsimp
      ring
    simpa only [he] using hp r hr _ htag

/-- Translation also preserves the literal lower/upper integral definition. -/
theorem hasDarbouxRSIntegral_translate (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f id a b v) (k : ℝ)
    (hc : c + k = a) (hd : d + k = b) :
    HasDarbouxRSIntegral (fun t => f (t + k)) id c d v :=
  hasDarbouxRSIntegral_of_hasRSIntegral (by linarith)
    (hasRSIntegral_translate (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) k hc hd)

/-- Reflection preserves the literal Darboux value on the reflected ordered interval. -/
theorem hasDarbouxRSIntegral_reflect (hab : a ≤ b)
    (hf : HasDarbouxRSIntegral f id a b v) (k : ℝ)
    (hc : k - d = a) (hd : k - c = b) :
    HasDarbouxRSIntegral (fun t => f (k - t)) id c d v :=
  hasDarbouxRSIntegral_of_hasRSIntegral (by linarith)
    (hasRSIntegral_reflect (hasRSIntegral_of_hasDarbouxRSIntegral hab hf) k hc hd)

/-- Complex norm convergence follows from the transported real components. -/
theorem hasComplexRSIntegral_translate {f : ℝ → ℂ} {z : ℂ}
    (hf : HasComplexRSIntegral f id a b z) (k : ℝ)
    (hc : c + k = a) (hd : d + k = b) :
    HasComplexRSIntegral (fun t => f (t + k)) id c d z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  exact hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_translate hr k hc hd, hasRSIntegral_translate hi k hc hd⟩

/-- Reflection of a complex literal integral, including endpoint tags. -/
theorem hasComplexRSIntegral_reflect {f : ℝ → ℂ} {z : ℂ}
    (hf : HasComplexRSIntegral f id a b z) (k : ℝ)
    (hc : k - d = a) (hd : k - c = b) :
    HasComplexRSIntegral (fun t => f (k - t)) id c d z := by
  obtain ⟨hr, hi⟩ := hasComplexRSIntegral_iff.mp hf
  exact hasComplexRSIntegral_iff.mpr
    ⟨hasRSIntegral_reflect hr k hc hd, hasRSIntegral_reflect hi k hc hd⟩

/-- Restriction to any closed subinterval constructs a literal integral value. -/
theorem exists_hasComplexRSIntegral_subinterval {f : ℝ → ℂ} {z : ℂ}
    (hf : HasComplexRSIntegral f id a b z) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    ∃ w, HasComplexRSIntegral f id c d w := by
  obtain ⟨_, r, _, hr, _⟩ := hasComplexRSIntegral_split hac (hcd.trans hdb) hf
  obtain ⟨l, _, hl, _, _⟩ := hasComplexRSIntegral_split hcd hdb hr
  exact ⟨l, hl⟩

/-- Join finitely many complete periods. No matching one-sided limits are required. -/
theorem periodic_hasComplexRSIntegral_nat {f : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hp : Function.Periodic f T)
    (hf : ∃ z, HasComplexRSIntegral f id a (a + T) z) (n : ℕ) :
    ∃ z, HasComplexRSIntegral f id a (a + n * T) z := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact hasComplexRSIntegral_iff.mpr
        ⟨hasRSIntegral_self _ _ _, hasRSIntegral_self _ _ _⟩
  | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨z, hz⟩ := hf
      have hs : HasComplexRSIntegral (fun t => f (t + -(n * T))) id
          (a + n * T) (a + (n + 1) * T) z :=
        hasComplexRSIntegral_translate hz (-(n * T)) (by ring) (by ring)
      have he : HasComplexRSIntegral f id (a + n * T) (a + (n + 1) * T) z :=
        hasComplexRSIntegral_congr hs (fun t _ => by
          simpa only [← sub_eq_add_neg] using (hp.nat_mul n).sub_eq t)
      refine ⟨u + z, ?_⟩
      simpa only [Nat.cast_succ] using hasComplexRSIntegral_join
        (show a ≤ a + n * T from le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hT.le))
        (show a + n * T ≤ a + (n + 1) * T by linarith) hu he

/-- One literal period implies literal integrability on every ordered interval.
Two finite cuts retain the values at the new endpoints, including singleton cuts. -/
theorem periodic_hasComplexRSIntegral {f : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hp : Function.Periodic f T)
    (hf : ∃ z, HasComplexRSIntegral f id a (a + T) z) (hcd : c ≤ d) :
    ∃ z, HasComplexRSIntegral f id c d z := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((a - c) / T)
  have hn' : a - c < n * T := (div_lt_iff₀ hT).mp hn
  let l := a - n * T
  have hlc : l ≤ c := by dsimp [l]; linarith
  obtain ⟨z, hz⟩ := hf
  have hs : HasComplexRSIntegral (fun t => f (t + n * T)) id l (l + T) z :=
    hasComplexRSIntegral_translate hz (n * T) (by dsimp [l]; ring) (by dsimp [l]; ring)
  have hl : HasComplexRSIntegral f id l (l + T) z :=
    hasComplexRSIntegral_congr hs (fun t _ => hp.nat_mul n t)
  obtain ⟨m, hm⟩ := exists_nat_gt ((d - l) / T)
  have hm' : d - l < m * T := (div_lt_iff₀ hT).mp hm
  obtain ⟨w, hw⟩ := periodic_hasComplexRSIntegral_nat hT hp ⟨z, hl⟩ m
  exact exists_hasComplexRSIntegral_subinterval hw hlc hcd (by linarith)

/-- The translated reflection needed for a periodic convolution has a literal
complex tagged integral on any ordered cut, not only a Bochner integral. -/
theorem periodic_hasComplexRSIntegral_reflected {f : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hp : Function.Periodic f T)
    (hf : ∃ z, HasComplexRSIntegral f id a (a + T) z) (x : ℝ) (hcd : c ≤ d) :
    ∃ z, HasComplexRSIntegral (fun t => f (x - t)) id c d z := by
  obtain ⟨z, hz⟩ := periodic_hasComplexRSIntegral hT hp hf
    (show x - d ≤ x - c by linarith)
  exact ⟨z, hasComplexRSIntegral_reflect hz x rfl rfl⟩

end Rudin.Support.RiemannAffine
