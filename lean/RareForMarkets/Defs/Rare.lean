module

public import RareForMarkets.Defs.Market

@[expose] public section

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

/-! ### RARE -/

/-- `p` is a `δ`-additive `κ`-multiplicative Response-Aware Rational Equilibrium
(`δ`-additive `κ`-RARE) under the allocation function `A`, writing `R^A_j(p) = R_j(p, A(p))`, if
`p ≥ 0` and for any seller `j` and any deviation `q_j ≥ 0`,
there is a response `q_{-j} ≥ 0` (here: a price vector `q ≥ 0` with `q j = q_j`) such that
1. `R^A_j(q) ≤ κ R^A_j(p) + δ`, i.e., seller `j` cannot gain much by deviating if others respond;
2. `R^A_k(q) ≥ R^A_k((q_j, p_{-j}))` for each responder `k ≠ j`, i.e., no responder loses.

`A` can be any function from prices to allocations. The paper only uses allocation rules
(`Market.AllocRule`), which map prices to the demand set; for those, write `IsRare A δ κ p`.

The paper takes `δ ≥ 0` and `κ ≥ 1`, writes `κ`-RARE when `δ = 0`,
and RARE when also `κ = 1`. -/
def IsRare [DecidableEq G] (A : (G → ℝ) → (B → G → ℝ)) (δ κ : ℝ) (p : G → ℝ) : Prop :=
  0 ≤ p ∧ ∀ j, ∀ qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧
    revenue q (A q) j ≤ κ * revenue p (A p) j + δ ∧
    ∀ k ≠ j, revenue (Function.update p j qj) (A (Function.update p j qj)) k ≤
      revenue q (A q) k

variable [DecidableEq G]

/-! ### Limiting RARE -/

/-- The individually rational (IR) responses `IR^A_j(q_j, p_{-j})` to seller `j` deviating to
`q_j`: responses `q_{-j} ≥ 0` where no responder `k ≠ j` earns less than at `(q_j, p_{-j})`. -/
def irResponses (A : (G → ℝ) → (B → G → ℝ)) (j : G) (qj : ℝ) (p : G → ℝ) : Set (G → ℝ) :=
  {q | 0 ≤ q ∧ q j = qj ∧ ∀ k ≠ j,
    revenue (Function.update p j qj) (A (Function.update p j qj)) k ≤ revenue q (A q) k}

/-- Seller `j`'s worst-case revenue at deviation `q_j`:
`D^A_j(q_j, p_{-j}) = inf_{q_{-j} ∈ IR^A_j(q_j, p_{-j})} R^A_j(q)`.
(Lean's `sInf` is `0` on sets unbounded below,
which doesn't happen for allocation rules since revenues are non-negative.) -/
noncomputable def worstRevenue (A : (G → ℝ) → B → G → ℝ) (j : G) (qj : ℝ) (p : G → ℝ) : ℝ :=
  sInf ((fun q ↦ revenue q (A q) j) '' irResponses A j qj p)

/-- Seller `j`'s optimal deviation revenue `V^A_j(p_{-j}) = sup_{q_j ≥ 0} D^A_j(q_j, p_{-j})`.
(Lean's `sSup` is `0` on sets unbounded above,
which doesn't happen for allocation rules since revenues are at most `B`.) -/
noncomputable def optDevRevenue (A : (G → ℝ) → (B → G → ℝ)) (j : G) (p : G → ℝ) : ℝ :=
  sSup ((fun qj ↦ worstRevenue A j qj p) '' Set.Ici 0)

/-- `\label{defn:lim-RARE}`: `p` is a `δ`-additive `κ`-limiting-RARE under `A` if
`p ≥ 0` and `R^A_j(p) ≥ (V^A_j(p_{-j}) - δ) / κ` for every seller `j`.
The paper takes `δ ≥ 0` and `κ ≥ 1`. -/
private def IsLimRare (A : (G → ℝ) → (B → G → ℝ)) (δ κ : ℝ) (p : G → ℝ) : Prop :=
  0 ≤ p ∧ ∀ j, optDevRevenue A j p ≤ κ * revenue p (A p) j + δ
