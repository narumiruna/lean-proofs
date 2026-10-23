module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-! # Chapter 11, Exercise 14

Complex measurability means measurability of both real coordinates.
It is equivalent to measurable preimages of every open planar set.
-/

@[expose] public section

namespace Rudin.Chapter11

open Set

variable {X : Type*} [MeasurableSpace X] {f : X → ℂ}

theorem exercise14_open_preimages
    (hre : Measurable (fun x ↦ (f x).re))
    (him : Measurable (fun x ↦ (f x).im)) :
    ∀ V : Set ℂ, IsOpen V → MeasurableSet (f ⁻¹' V) := by
  have hf : Measurable f := measurable_of_re_im hre him
  intro V hV
  exact hf hV.measurableSet

theorem exercise14_coordinate_measurability
    (h : ∀ V : Set ℂ, IsOpen V → MeasurableSet (f ⁻¹' V)) :
    Measurable (fun x ↦ (f x).re) ∧ Measurable (fun x ↦ (f x).im) := by
  have hf : Measurable f := measurable_of_isOpen h
  exact ⟨hf.re, hf.im⟩

theorem exercise14 :
    (Measurable (fun x ↦ (f x).re) ∧ Measurable (fun x ↦ (f x).im)) ↔
      ∀ V : Set ℂ, IsOpen V → MeasurableSet (f ⁻¹' V) :=
  ⟨fun h ↦ exercise14_open_preimages h.1 h.2, exercise14_coordinate_measurability⟩

end Rudin.Chapter11
