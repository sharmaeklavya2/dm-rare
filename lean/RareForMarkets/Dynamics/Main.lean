module

import Mathlib.Data.Real.Archimedean
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Rare
public import RareForMarkets.Dynamics.Defs
import RareForMarkets.Dynamics.Proofs

/-! Main results from `\cref{sec:dynamics}` in the paper. -/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G] [DecidableEq G]

/-- Throughout the dynamic, every seller sells out: `R^A_j(p^{(t)}) = ν p^{(t)}_j`. -/
public theorem dynamics_sellout [Nonempty B] [Nonempty G] (M : Market B G) (r : Rivalry)
    (A : M.AllocRule r) (hA : ContinuousOn A (Set.Ici 0))
    (p : ℕ → G → ℝ) (S : ℕ → Set G) (hdyn : M.IsDynamic A p S)
    (t : ℕ) (j : G) :
    A.revenue (p t) j = Market.nu (B := B) r * p t j :=
  hdyn.revenue_eq hA t j

/-- `\label{thm:dynamics-convergence}`: if each `S t` contains a most unsatisfied seller
(maximizing `V^A_j((p t)_{-j}) / (κν) - p t j`), then for any `δ > 0`,
1. some `p t` with `t ≤ ⌊B / δ⌋` is a `δ`-additive `κ`-RARE, and
2. `p t` is a `δ`-additive `κ`-RARE for all large enough `t`. -/
public theorem dynamics_convergence [Nonempty B] [Nonempty G] (M : Market B G) (r : Rivalry)
    (A : M.AllocRule r) (hA : ContinuousOn A (Set.Ici 0))
    (p : ℕ → G → ℝ) (S : ℕ → Set G) (hdyn : M.IsDynamic A p S)
    (hmax : ∀ t, (Market.unsatisfied A (p t)).Nonempty → ∃ j ∈ S t, ∀ k,
      optDevRevenue A k (p t) - p t k * (M.kappa r * Market.nu (B := B) r) ≤
        optDevRevenue A j (p t) - p t j * (M.kappa r * Market.nu (B := B) r))
    {δ : ℝ} (hδ : 0 < δ) :
    (∃ t ≤ ⌊M.totalBudget / δ⌋₊, IsRare A δ (M.kappa r) (p t)) ∧
      ∃ T, ∀ t > T, IsRare A δ (M.kappa r) (p t) :=
  hdyn.convergence hA hmax hδ
