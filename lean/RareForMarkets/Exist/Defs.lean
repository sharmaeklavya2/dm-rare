module

public import RareForMarkets.Defs.Market
public import Mathlib.Analysis.Convex.Function

/-!
## Security and overpricing parameters

Properties of the constants `σ_j`, `ρ_j`, `L_j` from `\cref{sec:exist:overpricing}`.
-/

@[expose] public section

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Market

variable (M : Market B G)

/-- `(σ, ρ)` are security parameters for seller `j` (`\cref{thm:security}`):
`σ, ρ > 0`, and pricing at `σ` guarantees revenue at least `ρ`, whatever the others charge. -/
structure IsSecurity [DecidableEq G] (r : Rivalry) (j : G) (σ ρ : ℝ) : Prop where
  σ_pos : 0 < σ
  ρ_pos : 0 < ρ
  le_revenue : ∀ q : G → ℝ, 0 ≤ q → ∀ x ∈ M.dem r (Function.update q j σ),
    ρ ≤ revenue (Function.update q j σ) x j

/-- `L` is an overpricing parameter for seller `j` with security parameters `(σ, ρ)`
(`\cref{thm:overpricing}`): `L ≥ max(B, σ)`, and
if `q_j > L` and `max_{k ≠ j} q_k = B`, then `j` earns at most `ρ / (2κ)`. -/
structure IsOverpricing (r : Rivalry) (j : G) (σ ρ L : ℝ) : Prop where
  max_le : max M.totalBudget σ ≤ L
  revenue_le : ∀ q : G → ℝ, 0 ≤ q → ∀ x ∈ M.dem r q, L < q j →
    (∀ k ≠ j, q k ≤ M.totalBudget) → (∃ k ≠ j, q k = M.totalBudget) →
      2 * (M.kappa r) * (revenue q x j) ≤ ρ

/-! ## Welfare function -/

/-- The `W`-rivalrous demand
`Dem^W(p) = argmax_{x ∈ Aff^R(p)} W(u₁(x₁), …, uₙ(xₙ))` for a welfare function `W`. -/
def welfareDem (W : (B → ℝ) → ℝ) (p : G → ℝ) : Set (B → G → ℝ) :=
  {x ∈ M.rivalAff p | IsMaxOn (fun y ↦ W (fun i ↦ M.util i (y i))) (M.rivalAff p) x}

end Market

/-- A *nice* welfare function `W : ℝ_{≥0}^n → ℝ` is continuous, strictly monotone, and concave. -/
structure IsNiceWelfare (W : (B → ℝ) → ℝ) : Prop where
  continuousOn : ContinuousOn W (Set.Ici 0)
  strictMonoOn : StrictMonoOn W (Set.Ici 0)
  concaveOn : ConcaveOn ℝ (Set.Ici 0) W

end
