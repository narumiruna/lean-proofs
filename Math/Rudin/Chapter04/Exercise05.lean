module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter04

/-- Tietze's theorem supplies a real continuous extension, also for the empty
set and the arbitrary metric domains stated in the source's final sentence. -/
theorem exercise05_real_extension {X : Type*} [MetricSpace X] {E : Set X} (hE : IsClosed E)
    {f : E → ℝ} (hf : Continuous f) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x : E, g x = f x := by
  obtain ⟨g, hg⟩ := (ContinuousMap.mk f hf).exists_restrict_eq hE
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact congrArg (fun u : C(E, ℝ) => u x) hg

/-- On the nonclosed positive half-line the reciprocal has no continuous extension. -/
theorem exercise05_nonclosed_failure :
    ¬ IsClosed (Ioi (0 : ℝ)) ∧
      Continuous (fun x : Ioi (0 : ℝ) => (x : ℝ)⁻¹) ∧
      ¬ ∃ g : ℝ → ℝ, Continuous g ∧
        ∀ x : Ioi (0 : ℝ), g x = (x : ℝ)⁻¹ := by
  have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact le_refl 0
  refine ⟨?_, continuous_subtype_val.inv₀ (fun x => ne_of_gt x.property), ?_⟩
  · intro hc
    have : (0 : ℝ) ∈ Ioi (0 : ℝ) := hc.closure_eq ▸ hz
    exact (lt_irrefl 0) this
  · rintro ⟨g, hg, he⟩
    have hclosed : IsClosed {x : ℝ | x * g x = 1} :=
      isClosed_eq (continuous_id.mul hg) continuous_const
    have hsub : Ioi (0 : ℝ) ⊆ {x : ℝ | x * g x = 1} := by
      intro x hx
      change x * g (⟨x, hx⟩ : Ioi (0 : ℝ)) = 1
      rw [he]
      exact mul_inv_cancel₀ (ne_of_gt hx)
    have hzero := closure_minimal hsub hclosed hz
    norm_num at hzero

/-- Extend each coordinate and assemble them using the Euclidean topology.
The dimension can be zero, and the closed domain can be empty. -/
theorem exercise05_vector_extension {X : Type*} [MetricSpace X] {E : Set X}
    (hE : IsClosed E) (k : ℕ) {f : E → EuclideanSpace ℝ (Fin k)} (hf : Continuous f) :
    ∃ g : X → EuclideanSpace ℝ (Fin k), Continuous g ∧
      ∀ x : E, g x = f x := by
  have hfi (i : Fin k) : Continuous (fun x : E => f x i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp hf
  choose g hg he using fun i : Fin k => exercise05_real_extension hE (hfi i)
  refine ⟨fun x => WithLp.toLp 2 (fun i => g i x), ?_, ?_⟩
  · exact (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp (continuous_pi hg)
  · intro x
    ext i
    exact he i x

end Rudin.Chapter04
