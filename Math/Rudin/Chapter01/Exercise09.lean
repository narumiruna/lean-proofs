module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic

/-! # R01E09
Rudin, book page 22 (PDF page 31). The lexicographic order is pulled back
from the real and imaginary coordinates. It is not installed globally.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The linear order defined by real coordinate first, imaginary coordinate second. -/
noncomputable abbrev exercise09Order : LinearOrder ℂ :=
  LinearOrder.lift' (fun z : ℂ => toLex (z.re, z.im)) (by
    intro z w h
    have hp : (z.re, z.im) = (w.re, w.im) := congrArg ofLex h
    exact Complex.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp))

attribute [local instance] exercise09Order

/-- The strict order is exactly the one specified in the exercise. -/
theorem exercise09_lt_iff (z w : ℂ) :
    z < w ↔ z.re < w.re ∨ z.re = w.re ∧ z.im < w.im :=
  Prod.Lex.toLex_lt_toLex

/-- The associated non-strict order. -/
theorem exercise09_le_iff (z w : ℂ) :
    z ≤ w ↔ z.re < w.re ∨ z.re = w.re ∧ z.im ≤ w.im :=
  Prod.Lex.toLex_le_toLex

/-- Irreflexivity, transitivity and trichotomy of the specified strict order. -/
theorem exercise09_linear_order :
    (∀ z : ℂ, ¬ z < z) ∧
    (∀ x y z : ℂ, x < y → y < z → x < z) ∧
    (∀ z w : ℂ, z < w ∨ z = w ∨ w < z) :=
  ⟨lt_irrefl, fun _ _ _ => lt_trans, lt_trichotomy⟩

/-- The imaginary axis, with all imaginary coordinates allowed. -/
def exercise09Set : Set ℂ := {z | z.re = 0}

/-- Its upper bounds are precisely the complex numbers with positive real part. -/
theorem exercise09_upperBounds (u : ℂ) :
    u ∈ upperBounds exercise09Set ↔ 0 < u.re := by
  constructor
  · intro hu
    have h := hu (show (⟨0, u.im + 1⟩ : ℂ) ∈ exercise09Set from rfl)
    rw [exercise09_le_iff] at h
    change 0 < u.re ∨ 0 = u.re ∧ u.im + 1 ≤ u.im at h
    rcases h with h | ⟨_, h⟩
    · exact h
    · linarith
  · intro hu z hz
    exact (exercise09_le_iff z u).2 (Or.inl (by
      change z.re = 0 at hz
      simpa [hz] using hu))

/-- A nonempty bounded-above set with no least upper bound in this linear order. -/
theorem exercise09_no_lub :
    exercise09Set.Nonempty ∧ BddAbove exercise09Set ∧
      ¬ ∃ u : ℂ, IsLUB exercise09Set u := by
  refine ⟨⟨0, rfl⟩, ⟨1, (exercise09_upperBounds 1).2 (by norm_num)⟩, ?_⟩
  rintro ⟨u, hu⟩
  have hp := (exercise09_upperBounds u).1 hu.1
  let v : ℂ := ⟨u.re, u.im - 1⟩
  have hv : v ∈ upperBounds exercise09Set := (exercise09_upperBounds v).2 hp
  have h := (exercise09_le_iff u v).1 (hu.2 hv)
  change u.re < u.re ∨ u.re = u.re ∧ u.im ≤ u.im - 1 at h
  rcases h with h | ⟨_, h⟩ <;> linarith

end Rudin.Chapter01
