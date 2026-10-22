module

public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

/-- The upper limits are extended real numbers. Only opposite infinities are excluded. -/
theorem exercise05_limsup_sum (a b : ℕ → ℝ)
    (h : limsup (fun n => (a n : EReal)) atTop ≠ ⊥ ∨
      limsup (fun n => (b n : EReal)) atTop ≠ ⊤)
    (h' : limsup (fun n => (a n : EReal)) atTop ≠ ⊤ ∨
      limsup (fun n => (b n : EReal)) atTop ≠ ⊥) :
    limsup (fun n => ((a n + b n : ℝ) : EReal)) atTop ≤
      limsup (fun n => (a n : EReal)) atTop +
        limsup (fun n => (b n : EReal)) atTop := by
  have hadd : (fun n => ((a n + b n : ℝ) : EReal)) =
      (fun n => (a n : EReal)) + (fun n => (b n : EReal)) := by
    funext n
    exact EReal.coe_add (a n) (b n)
  rw [hadd]
  exact EReal.limsup_add_le h h'

end Rudin.Chapter03
