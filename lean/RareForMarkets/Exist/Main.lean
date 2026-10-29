module


public import RareForMarkets.Defs.Misc
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Rare
public import RareForMarkets.Exist.Defs
import RareForMarkets.Exist.Continuous
import RareForMarkets.Exist.Corollary
import RareForMarkets.Exist.Unique
import RareForMarkets.Exist.Concave

/-!
Main results (theorems and corollaries) from `\cref{sec:exist}` in the paper.

Continuity of an allocation rule `A : ℝ_{≥0}^m → [0, 1]^{n × m}` is `ContinuousOn A (Set.Ici 0)`.
-/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]


/-- `\label{thm:rare-exists-continuous}`: for a continuous allocation rule `A` and
security/overpricing parameters `σ`, `ρ`, `L`, there are prices `p ∈ βΔ_m` such that every
seller `j` sells out with `p_j ≥ βρ_j / B`, and every deviation `q_j` has a response
`q_{-j} ∈ ∏_{k ≠ j} [p_k, L_k]` after which `j` earns at most `κνp_j`
and each responder `k` earns at least `νp_k ≥ R^A_k((q_j, p_{-j}))`.

The parameters are inputs (not obtained inside) so that callers can use the same ones
across several markets, as `\cref{thm:nonrival-rare-exists}` does. -/
public theorem rare_exists_continuous [DecidableEq G] [Nonempty B] [Nonempty G]
    (M : Market B G) (r : Rivalry) (A : M.AllocRule r) (hA : ContinuousOn A (Set.Ici 0))
    (σ ρ L : G → ℝ) (hsec : ∀ j, M.IsSecurity r j (σ j) (ρ j))
    (hover : ∀ j, M.IsOverpricing r j (σ j) (ρ j) (L j)) :
    ∃ p ∈ scaledSimplex G (M.beta r), ∀ j,
      (A.revenue p j = Market.nu (B := B) r * p j ∧ M.beta r * ρ j ≤ p j * M.totalBudget) ∧
      ∀ qj, 0 ≤ qj → ∃ q : G → ℝ, q j = qj ∧
        (∀ k ≠ j, q k ∈ Set.Icc (p k) (L k)) ∧
        A.revenue q j ≤ p j * (M.kappa r) * (Market.nu (B := B) r) ∧
        ∀ k ≠ j, Market.nu (B := B) r * p k ≤ A.revenue q k ∧
          A.revenue (Function.update p j qj) k ≤ Market.nu (B := B) r * p k :=
  A.rare_exists_continuous_aux hA σ ρ L hsec hover

/-- `\label{thm:rare-exists-continuous-corr}`:
for any continuous allocation rule `A`, there is a `κ`-RARE `p` with `R_all(p) = B / κ`. -/
public theorem rare_exists_continuous_corr [DecidableEq G] [Nonempty B] [Nonempty G]
    (M : Market B G) (r : Rivalry)
    (A : M.AllocRule r) (hA : ContinuousOn A (Set.Ici 0)) :
    ∃ p, IsRare A 0 (M.kappa r) p ∧ M.revenueAll r p = M.totalBudget / M.kappa r :=
  A.rare_exists_continuous_corr_aux hA

/-- `\label{thm:unique-nr-demand}`: for strictly concave utilities,
`Dem^NR(p)` is a singleton for every `p ≥ 0`,
and the unique allocation rule is continuous. -/
public theorem unique_nr_demand (M : Market B G)
    (hu : ∀ i, StrictConcaveOn ℝ (cube G) (M.util i)) :
    (∀ p : G → ℝ, 0 ≤ p → ∃! x, x ∈ M.nonRivalDem p) ∧
      ∃ A : M.AllocRule .nonRival, ContinuousOn A (Set.Ici 0) :=
  Market.unique_nr_demand_family (fun _ ↦ M) (fun _ ↦ rfl) M.continuousOn_util_const
    ⟨le_rfl, zero_le_one⟩ hu

/-- `\label{thm:nonrival-rare-exists}`: `(b_avg / b_min)`-RARE for non-rivalrous markets
with concave utilities, where the allocation `x ∈ Dem^NR(q)` may be picked per deviation. -/
public theorem nonrival_rare_exists [Nonempty B] [Nonempty G] (M : Market B G)
    (hu : ∀ i, ConcaveOn ℝ (cube G) (M.util i)) :
    ∃ p ∈ openScaledSimplex G M.minBudget, 1 ∈ M.nonRivalDem p ∧
      ∀ j qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧ ∃ x ∈ M.nonRivalDem q,
        revenue q x j ≤ M.avgBudget / M.minBudget * revenue p (1 : B → G → ℝ) j ∧
        revenue p (1 : B → G → ℝ) j = Fintype.card B * p j ∧
        ∀ k ≠ j, Fintype.card B * p k ≤ revenue q x k :=
  M.nonrival_rare_exists_aux hu

/-- `\label{thm:unique-rival-demand}`: for strictly concave utilities and a nice
welfare function `W`, `Dem^W(p)` is a singleton for every `p ≥ 0`,
and the unique allocation rule is continuous. -/
public theorem unique_rival_demand (M : Market B G)
    (hu : ∀ i, StrictConcaveOn ℝ (cube G) (M.util i)) (W : (B → ℝ) → ℝ)
    (hW : IsNiceWelfare W) :
    (∀ p : G → ℝ, 0 ≤ p → ∃! x, x ∈ M.welfareDem W p) ∧
      ∃ A : M.AllocRule .rival, ContinuousOn A (Set.Ici 0) ∧
        ∀ p, 0 ≤ p → A p ∈ M.welfareDem W p :=
  Market.unique_rival_demand_family (fun _ ↦ M) (fun _ ↦ rfl) M.continuousOn_util_const hW
    ⟨le_rfl, zero_le_one⟩ hu

/-- `\label{thm:rival-rare-exists}`: RARE for rivalrous markets with concave utilities,
where the allocation `z ∈ Dem^W(q)` may be picked per deviation. -/
public theorem rival_rare_exists [Nonempty G] [Nonempty B] (M : Market B G)
    (hu : ∀ i, ConcaveOn ℝ (cube G) (M.util i)) (W : (B → ℝ) → ℝ)
    (hW : IsNiceWelfare W) :
    ∃ p ∈ openScaledSimplex G M.totalBudget, ∃ x ∈ M.welfareDem W p,
      ∀ j qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧ ∃ z ∈ M.welfareDem W q,
        revenue q z j ≤ revenue p x j ∧ revenue p x j = p j ∧
        ∀ k ≠ j, p k ≤ revenue q z k :=
  M.rival_rare_exists_aux hu W hW
