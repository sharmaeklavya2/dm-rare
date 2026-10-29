module

public import RareForMarkets.Defs.Market

/-! Definitions from `\cref{sec:nasheq-uncommon}` in the paper. -/

@[expose] public section

open Finset

variable {B G : Type*} [Fintype B] [Fintype G] [DecidableEq G]

/-- `\label{defn:nasheq}`: `p` is a Nash equilibrium under `A`,
writing `R^A_j(p) = R_j(p, A(p))`, if `p ≥ 0` and for any seller `j` and any deviation `s ≥ 0`,
we have `R^A_j((s, p_{-j})) ≤ R^A_j(p)`.

As for `IsRare`, `A` can be any function from prices to allocations; the paper only uses
allocation rules (`Market.AllocRule`), for which one writes `IsNashEq A p`. -/
def IsNashEq (A : (G → ℝ) → (B → G → ℝ)) (p : G → ℝ) : Prop :=
  0 ≤ p ∧ ∀ j, ∀ s, 0 ≤ s →
    revenue (Function.update p j s) (A (Function.update p j s)) j ≤ revenue p (A p) j

/-! Definitions from `\cref{sec:lin-nonrival-to-splc-rival}` in the paper. -/

/-- `u` is SPLC (separable piecewise-linear concave) on `cube G`:
`u(z) = ∑ⱼ fⱼ(zⱼ)`, where each `fⱼ` is a concave piecewise-linear function,
i.e., a minimum of finitely many (here `k + 1`) affine functions `t ↦ a_{j,l} t + c_{j,l}`. -/
def IsSPLC (u : (G → ℝ) → ℝ) : Prop :=
  ∃ (k : ℕ) (a c : G → Fin (k + 1) → ℝ),
    ∀ z ∈ cube G, u z = ∑ j, ⨅ l, (a j l * z j + c j l)

/-- The smallest utility coefficient `u_min = min_{i,j} u_{i,j}`. -/
noncomputable def minWeight (w : B → G → ℝ) : ℝ := ⨅ i, ⨅ j, w i j

/-- The largest utility coefficient `u_max = max_{i,j} u_{i,j}`. -/
noncomputable def maxWeight (w : B → G → ℝ) : ℝ := ⨆ i, ⨆ j, w i j

/-- The utility `û(z) = ∑ⱼ (wⱼ min(n zⱼ, 1) + ε max(0, n zⱼ - 1))`,
i.e., `wⱼ n zⱼ` if `zⱼ ≤ 1/n` and `wⱼ + ε(n zⱼ - 1)` if `zⱼ > 1/n`. -/
def rivalizeUtil (n ε : ℝ) (w : G → ℝ) (z : G → ℝ) : ℝ :=
  ∑ j, (w j * min (n * z j) 1 + ε * max (n * z j - 1) 0)

end
