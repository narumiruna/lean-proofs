module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter05

/-- Exercise 2: positive derivative implies strict increase on the stated
open interval. No continuity of the derivative is assumed. -/
theorem exercise02_strict_increase (f : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) : StrictMonoOn f (Ioo a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · simpa only [interior_Ioo] using hp

/-- An ambient extension of the inverse. Its values outside the exact image
have no role in any inverse identity or derivative assertion. -/
noncomputable def exercise02_inverse (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  Function.invFunOn f (Ioo a b)

/-- The inverse as a map from the exact image to the exact source interval. -/
noncomputable def exercise02_inverseOn (f : ℝ → ℝ) (a b : ℝ) :
    (f '' Ioo a b) → Ioo a b :=
  fun y => ⟨exercise02_inverse f a b y, Function.invFunOn_mem y.property⟩

theorem exercise02_inverse_right (f : ℝ → ℝ) (a b : ℝ)
    {y : ℝ} (hy : y ∈ f '' Ioo a b) : f (exercise02_inverse f a b y) = y :=
  Function.invFunOn_eq hy

theorem exercise02_inverse_left (f : ℝ → ℝ) (a b : ℝ)
    (hm : StrictMonoOn f (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    exercise02_inverse f a b (f x) = x :=
  hm.injOn.leftInvOn_invFunOn hx

/-- Both inverse identities for the map with the exact subtype domains. -/
theorem exercise02_inverse_identities (f : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    (∀ x : Ioo a b, exercise02_inverseOn f a b ⟨f x, ⟨x, x.property, rfl⟩⟩ = x) ∧
    (∀ y : f '' Ioo a b, f (exercise02_inverseOn f a b y) = y) := by
  constructor
  · intro x
    apply Subtype.ext
    exact exercise02_inverse_left f a b (exercise02_strict_increase f a b hd hp) x.property
  · intro y
    exact exercise02_inverse_right f a b y.property

/-- The image contains a neighborhood of each image point. The proof uses
continuity of `f`, not continuity of its derivative. -/
theorem exercise02_image_mem_nhds (f : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Ioo a b)) (hm : StrictMonoOn f (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) : f '' Ioo a b ∈ 𝓝 (f x) := by
  let l := (a + x) / 2
  let r := (x + b) / 2
  have hl : l ∈ Ioo a b := by dsimp [l]; constructor <;> linarith [hx.1, hx.2]
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith [hx.1, hx.2]
  have hlx : l < x := by dsimp [l]; linarith [hx.1]
  have hxr : x < r := by dsimp [r]; linarith [hx.2]
  have hsub : Icc l r ⊆ Ioo a b := fun t ht =>
    ⟨hl.1.trans_le ht.1, ht.2.trans_lt hr.2⟩
  have heq := ContinuousOn.image_Ioo_of_strictMonoOn (hlx.trans hxr).le
    (hc.mono hsub) (hm.mono hsub)
  have hn : f '' Ioo l r ∈ 𝓝 (f x) := by
    rw [heq]
    exact Ioo_mem_nhds (hm hl hx hlx) (hm hx hr hxr)
  exact mem_of_superset hn (image_mono (Ioo_subset_Icc_self.trans hsub))

theorem exercise02_image_open (f : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) : IsOpen (f '' Ioo a b) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  exact exercise02_image_mem_nhds f a b
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (exercise02_strict_increase f a b hd hp) hx

/-- Continuity of the actual inverse at every point of the exact image. -/
theorem exercise02_inverse_continuousAt (f : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Ioo a b)) (hm : StrictMonoOn f (Ioo a b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    ContinuousAt (exercise02_inverse f a b) (f x) := by
  have hi : StrictMonoOn (exercise02_inverse f a b) (f '' Ioo a b) := by
    rintro y ⟨u, hu, rfl⟩ z ⟨v, hv, rfl⟩ huv
    rw [exercise02_inverse_left f a b hm hu, exercise02_inverse_left f a b hm hv]
    by_contra hn
    exact (not_le.mpr huv) (hm.monotoneOn hv hu (le_of_not_gt hn))
  apply hi.continuousAt_of_image_mem_nhds (exercise02_image_mem_nhds f a b hc hm hx)
  rw [exercise02_inverse_left f a b hm hx]
  apply mem_of_superset (Ioo_mem_nhds hx.1 hx.2)
  intro u hu
  exact ⟨f u, ⟨u, hu, rfl⟩, exercise02_inverse_left f a b hm hu⟩

/-- Exercise 2: the inverse has reciprocal derivative at every `f x` in the
image. This is an ambient derivative because that exact image is open. -/
theorem exercise02_inverse_hasDerivAt (f : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (exercise02_inverse f a b) (1 / deriv f x) (f x) := by
  have hm := exercise02_strict_increase f a b hd hp
  have hcont := exercise02_inverse_continuousAt f a b
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) hm hx
  have hf : HasDerivAt f (deriv f x) (exercise02_inverse f a b (f x)) := by
    rw [exercise02_inverse_left f a b hm hx]
    exact (hd x hx).hasDerivAt
  have hright : ∀ᶠ y in 𝓝 (f x), f (exercise02_inverse f a b y) = y := by
    filter_upwards [exercise02_image_mem_nhds f a b
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) hm hx] with y hy
    exact exercise02_inverse_right f a b hy
  simpa only [one_div] using hf.of_local_left_inverse hcont (ne_of_gt (hp x hx)) hright

/-- Differentiability throughout the exact image and the requested formula. -/
theorem exercise02_inverse_derivative (f : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    (∀ y ∈ f '' Ioo a b, DifferentiableAt ℝ (exercise02_inverse f a b) y) ∧
    (∀ x ∈ Ioo a b, deriv (exercise02_inverse f a b) (f x) = 1 / deriv f x) := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact (exercise02_inverse_hasDerivAt f a b hd hp hx).differentiableAt
  · intro x hx
    exact (exercise02_inverse_hasDerivAt f a b hd hp hx).deriv

end Rudin.Chapter05
