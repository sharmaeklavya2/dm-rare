module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic

@[expose] public section

open Finset

/-! ### Scaled simplices -/

/-- The scaled simplex `βΔ_m = {x ∈ ℝ_{≥0}^m : ∑ⱼ xⱼ = β}`.
For `β = 1` this is Mathlib's `stdSimplex ℝ G`. -/
def scaledSimplex (G : Type*) [Fintype G] (β : ℝ) : Set (G → ℝ) :=
  {x | 0 ≤ x ∧ ∑ j, x j = β}

/-- The relative interior `βΔ_m^∘ = {x ∈ ℝ_{>0}^m : ∑ⱼ xⱼ = β}` of the scaled simplex. -/
def openScaledSimplex (G : Type*) [Fintype G] (β : ℝ) : Set (G → ℝ) :=
  {x | (∀ j, 0 < x j) ∧ ∑ j, x j = β}
