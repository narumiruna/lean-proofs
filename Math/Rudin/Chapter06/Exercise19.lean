module

public import Math.Rudin.Support.StieltjesPrototype
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# R06E19: increasing continuous reparameterization

Length is the supremum of finite ordered partition chord sums (Definition 6.26),
with values in `ℝ≥0∞`. Repeated nodes contribute zero. The comparison with
`eVariationOn` below includes the insertion of both interval endpoints.
The metric-space statements apply in particular to `EuclideanSpace ℝ (Fin k)`
and to the complex plane with its usual norm.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set
open scoped ENNReal
open Rudin.Support.StieltjesPrototype

variable {E : Type*} [PseudoMetricSpace E]

/-- The sum of Euclidean chord lengths for a source partition. -/
noncomputable def curveChordSum {a b : ℝ} (γ : ℝ → E) (p : Partition a b) : ℝ :=
  ∑ i ∈ Finset.range p.n, dist (γ (p.x (i + 1))) (γ (p.x i))

/-- Source length, including infinite length and the empty interval. -/
noncomputable def curveLength (γ : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : Partition a b, ENNReal.ofReal (curveChordSum γ p)

/-- Rectifiability means that the source length is finite. -/
def CurveRectifiable (γ : ℝ → E) (a b : ℝ) : Prop := curveLength γ a b ≠ ⊤

/-- An arc is a continuous injective mapping of the parameter interval. -/
def CurveArc (γ : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧ InjOn γ (Icc a b)

/-- A closed curve is continuous and has equal endpoint values. -/
def CurveClosed (γ : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧ γ a = γ b

theorem curveChordSum_nonneg {a b : ℝ} (γ : ℝ → E) (p : Partition a b) :
    0 ≤ curveChordSum γ p := Finset.sum_nonneg fun _ _ => dist_nonneg

theorem curveChordSum_edist {a b : ℝ} (γ : ℝ → E) (p : Partition a b) :
    ENNReal.ofReal (curveChordSum γ p) =
      ∑ i ∈ Finset.range p.n, edist (γ (p.x (i + 1))) (γ (p.x i)) := by
  simp [curveChordSum, ENNReal.ofReal_sum_of_nonneg, dist_nonneg, edist_dist]

private theorem curvePartition_mem {a b : ℝ} (p : Partition a b) {i : ℕ}
    (hi : i ≤ p.n) : p.x i ∈ Icc a b := by
  constructor
  · simpa only [p.first] using p.increasing (by simp) hi (Nat.zero_le i)
  · simpa only [p.last] using p.increasing hi (by simp) hi

/-- Add the two endpoints to an arbitrary finite increasing list. -/
private def enclosePartition {a b : ℝ} (hab : a ≤ b) (n : ℕ) (u : ℕ → ℝ)
    (hu : Monotone u) (hs : ∀ i, u i ∈ Icc a b) : Partition a b where
  n := n + 2
  pos := by omega
  x := fun i => if i = 0 then a else if i ≤ n + 1 then u (i - 1) else b
  first := by simp
  last := by simp
  increasing := by
    intro i hi j hj hij
    dsimp
    split_ifs <;> first
      | exact le_rfl
      | exact hab
      | exact (hs _).1
      | exact (hs _).2
      | exact hu (by omega)
      | omega

/-- The source supremum agrees with variation, not merely with a renamed length. -/
theorem curveLength_eq_eVariationOn (γ : ℝ → E) (a b : ℝ) :
    curveLength γ a b = eVariationOn γ (Icc a b) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    rw [curveChordSum_edist]
    exact eVariationOn.sum_le_of_monotoneOn_Iic p.increasing
      (fun _ hi => curvePartition_mem p hi)
  · by_cases hab : a ≤ b
    · unfold eVariationOn
      apply iSup_le
      rintro ⟨n, u, hu, hs⟩
      let p := enclosePartition hab n u hu hs
      have hp : ∀ i, i ≤ n → p.x (i + 1) = u i := by
        intro i hi
        simp [p, enclosePartition, show i + 1 ≤ n + 1 by omega]
      calc
        (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i)))
            ≤ ∑ i ∈ Finset.range (n + 1), edist (γ (p.x (i + 2))) (γ (p.x (i + 1))) := by
              rw [Finset.sum_range_succ]
              refine le_trans ?_ (le_add_right le_rfl)
              exact le_of_eq (Finset.sum_congr rfl fun i hi => by
                rw [show i + 2 = (i + 1) + 1 by omega, hp (i + 1) (by
                  have := Finset.mem_range.mp hi; omega), hp i (by
                  have := Finset.mem_range.mp hi; omega)])
        _ ≤ ∑ i ∈ Finset.range (n + 2), edist (γ (p.x (i + 1))) (γ (p.x i)) := by
              rw [Finset.sum_range_succ' (fun i => edist (γ (p.x (i + 1))) (γ (p.x i))) (n + 1)]
              simpa only [Nat.add_assoc, Nat.zero_add] using
                (self_le_add_right (∑ i ∈ Finset.range (n + 1),
                  edist (γ (p.x (i + 2))) (γ (p.x (i + 1))))
                  (edist (γ (p.x 1)) (γ (p.x 0))))
        _ = ENNReal.ofReal (curveChordSum γ p) := (curveChordSum_edist γ p).symm
        _ ≤ curveLength γ a b := by
              unfold curveLength
              exact le_iSup (fun q : Partition a b => ENNReal.ofReal (curveChordSum γ q)) p
    · have hz : eVariationOn γ (Icc a b) = 0 := by
        rw [eVariationOn.eq_zero_iff, Icc_eq_empty_of_lt (lt_of_not_ge hab)]
        simp
      rw [hz]
      exact bot_le

/-- Empty and singleton intervals have zero length. -/
theorem curveLength_eq_zero_of_ge (γ : ℝ → E) {a b : ℝ} (hba : b ≤ a) :
    curveLength γ a b = 0 := by
  rw [curveLength_eq_eVariationOn]
  exact eVariationOn.subsingleton γ (Set.subsingleton_Icc_of_ge hba)

/-- On normed spaces the chord sums use the actual norm of each chord. -/
theorem curveChordSum_eq_norm {F : Type*} [NormedAddCommGroup F] {a b : ℝ}
    (γ : ℝ → F) (p : Partition a b) :
    curveChordSum γ p = ∑ i ∈ Finset.range p.n, ‖γ (p.x (i + 1)) - γ (p.x i)‖ := by
  simp only [curveChordSum, dist_eq_norm]

/-- Deleting repeated nodes gives the same supremum: strict finite lists suffice.
The endpoint insertion in `curveLength_eq_eVariationOn` supplies full partitions. -/
theorem curveLength_eq_strictLists (γ : ℝ → E) (a b : ℝ) :
    curveLength γ a b =
      ⨆ p : (n : ℕ) × {u : ℕ → ℝ //
        StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ Icc a b},
        ∑ i ∈ Finset.range p.1, edist (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) := by
  rw [curveLength_eq_eVariationOn, eVariationOn.eVariationOn_eq_strictMonoOn]

/-- Continuity and the specified first endpoint force increasing orientation. -/
theorem reparam_strictMono {a b c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc c d)) (hbij : BijOn φ (Icc c d) (Icc a b))
    (hfirst : φ c = a) : StrictMonoOn φ (Icc c d) := by
  apply hφ.strictMonoOn_of_injOn_Icc hcd _ hbij.injOn
  rw [hfirst]
  exact (hbij.mapsTo (right_mem_Icc.mpr hcd)).1

/-- The second endpoint is also preserved, including singleton intervals. -/
theorem reparam_last {a b c d : ℝ} {φ : ℝ → ℝ} (hcd : c ≤ d)
    (hφ : ContinuousOn φ (Icc c d)) (hbij : BijOn φ (Icc c d) (Icc a b))
    (hfirst : φ c = a) : φ d = b := by
  have hm := (reparam_strictMono hcd hφ hbij hfirst).monotoneOn
  have hd := hbij.mapsTo (right_mem_Icc.mpr hcd)
  have hab : a ≤ b := (hbij.mapsTo (left_mem_Icc.mpr hcd)).1.trans
    (hbij.mapsTo (left_mem_Icc.mpr hcd)).2
  obtain ⟨s, hs, hsb⟩ := hbij.surjOn (right_mem_Icc.mpr hab)
  exact le_antisymm hd.2 (by rw [← hsb]; exact hm hs (right_mem_Icc.mpr hcd) hs.2)

/-- The reparameterized mapping is an actual continuous curve. -/
theorem reparam_continuous {a b c d : ℝ} {φ : ℝ → ℝ} {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc a b)) (hφ : ContinuousOn φ (Icc c d))
    (hbij : BijOn φ (Icc c d) (Icc a b)) :
    ContinuousOn (γ ∘ φ) (Icc c d) := hγ.comp hφ hbij.mapsTo

/-- R06E19.arc. -/
theorem exercise19_arc {a b c d : ℝ} {φ : ℝ → ℝ} {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc a b)) (hφ : ContinuousOn φ (Icc c d))
    (hbij : BijOn φ (Icc c d) (Icc a b)) :
    CurveArc (γ ∘ φ) c d ↔ CurveArc γ a b := by
  have hc := reparam_continuous hγ hφ hbij
  simp only [CurveArc, hc, hγ, true_and]
  constructor
  · intro h x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := hbij.surjOn hx
    obtain ⟨t, ht, rfl⟩ := hbij.surjOn hy
    exact congrArg φ (h hs ht hxy)
  · intro h x hx y hy heq
    exact hbij.injOn hx hy (h (hbij.mapsTo hx) (hbij.mapsTo hy) heq)

/-- R06E19.closed_curve. -/
theorem exercise19_closed_curve {a b c d : ℝ} {φ : ℝ → ℝ} {γ : ℝ → E}
    (hcd : c ≤ d) (hγ : ContinuousOn γ (Icc a b))
    (hφ : ContinuousOn φ (Icc c d)) (hbij : BijOn φ (Icc c d) (Icc a b))
    (hfirst : φ c = a) : CurveClosed (γ ∘ φ) c d ↔ CurveClosed γ a b := by
  have hc := reparam_continuous hγ hφ hbij
  simp only [CurveClosed, hc, hγ, true_and, Function.comp_apply,
    hfirst, reparam_last hcd hφ hbij hfirst]

/-- R06E19.length: equality in the extended nonnegative reals includes infinity. -/
theorem exercise19_length {a b c d : ℝ} {φ : ℝ → ℝ} (γ : ℝ → E)
    (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hbij : BijOn φ (Icc c d) (Icc a b)) (hfirst : φ c = a) :
    curveLength (γ ∘ φ) c d = curveLength γ a b := by
  simp only [curveLength_eq_eVariationOn]
  rw [eVariationOn.comp_eq_of_monotoneOn γ φ
    (reparam_strictMono hcd hφ hbij hfirst).monotoneOn, hbij.image_eq]

/-- R06E19.rectifiability. -/
theorem exercise19_rectifiability {a b c d : ℝ} {φ : ℝ → ℝ} (γ : ℝ → E)
    (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hbij : BijOn φ (Icc c d) (Icc a b)) (hfirst : φ c = a) :
    CurveRectifiable (γ ∘ φ) c d ↔ CurveRectifiable γ a b := by
  simp only [CurveRectifiable, exercise19_length γ hcd hφ hbij hfirst]

/-- The complete source statement for the true Euclidean metric. No finiteness
hypothesis is imposed on length; the equality also holds when both lengths are infinite. -/
theorem exercise19_euclidean {k : ℕ} {a b c d : ℝ} {φ : ℝ → ℝ}
    (γ : ℝ → EuclideanSpace ℝ (Fin k)) (hcd : c ≤ d)
    (hγ : ContinuousOn γ (Icc a b)) (hφ : ContinuousOn φ (Icc c d))
    (hbij : BijOn φ (Icc c d) (Icc a b)) (hfirst : φ c = a) :
    ContinuousOn (γ ∘ φ) (Icc c d) ∧
    (CurveArc (γ ∘ φ) c d ↔ CurveArc γ a b) ∧
    (CurveClosed (γ ∘ φ) c d ↔ CurveClosed γ a b) ∧
    (CurveRectifiable (γ ∘ φ) c d ↔ CurveRectifiable γ a b) ∧
    curveLength (γ ∘ φ) c d = curveLength γ a b :=
  ⟨reparam_continuous hγ hφ hbij, exercise19_arc hγ hφ hbij,
    exercise19_closed_curve hcd hγ hφ hbij hfirst,
    exercise19_rectifiability γ hcd hφ hbij hfirst,
    exercise19_length γ hcd hφ hbij hfirst⟩

end Rudin.Chapter06
