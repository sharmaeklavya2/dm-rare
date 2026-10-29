module

import Mathlib.Data.Real.Archimedean
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Rare

/-! Definitions from `\cref{sec:dynamics}` in the paper. -/

@[expose] public section

open Finset

variable {B G : Type*} [Fintype B] [Fintype G] [DecidableEq G]

namespace Market

variable {M : Market B G} {r : Rivalry}

/-- The sellers `J = {j : V^A_j(p_{-j}) / (κν) > p_j}` who want to raise their prices. -/
def unsatisfied (A : M.AllocRule r) (p : G → ℝ) : Set G :=
  {j | p j * M.kappa r * nu (B := B) r < optDevRevenue A j p }

/-- `(p, S)` is a run of the dynamic for the allocation rule `A`:
`p 0 = 0`, and at each step `t`, a subset `S t` of the unsatisfied sellers `J` at `p t`,
non-empty if `J` is, raise their prices to `V^A_j((p t)_{-j}) / (κν)`; the others keep theirs.

Indices are shifted by one from the paper: our `p t`, `S t` are its `p^{(t)}`, `S^{(t+1)}`.
(If `J = ∅`, then `S t = ∅` and the prices don't change.) -/
structure IsDynamic (A : M.AllocRule r) (p : ℕ → G → ℝ) (S : ℕ → Set G) : Prop where
  zero : p 0 = 0
  subset : ∀ t, S t ⊆ unsatisfied A (p t)
  nonempty : ∀ t, (unsatisfied A (p t)).Nonempty → (S t).Nonempty
  update_mem : ∀ t, ∀ j ∈ S t,
    p (t + 1) j * (M.kappa r) * (nu (B := B) r) = optDevRevenue A j (p t)
  update_not_mem : ∀ t, ∀ j ∉ S t, p (t + 1) j = p t j

end Market

end
