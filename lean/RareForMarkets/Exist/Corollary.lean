module

public import RareForMarkets.Defs.Rare
public import RareForMarkets.Defs.Market
import RareForMarkets.Exist.Continuous
import RareForMarkets.Exist.Params

/-!
# `\cref{thm:rare-exists-continuous-corr}`
-/

open Set Finset

variable {B G : Type*} [Fintype B] [Fintype G] [DecidableEq G] [Nonempty B] [Nonempty G]

namespace Market.AllocRule

variable {M : Market B G} {r : Rivalry} (A : M.AllocRule r)

/-- Every price vector `p` from `\cref{thm:rare-exists-continuous}` is a `κ`-RARE with
`R_all(p) = B / κ`. -/
public theorem rare_exists_continuous_corr_aux (hA : ContinuousOn A (Ici 0)) :
    ∃ p, IsRare A 0 (M.kappa r) p ∧ M.revenueAll r p = M.totalBudget / M.kappa r := by
  obtain ⟨σ, ρ, L, hsec, hover⟩ := M.exists_params r
  obtain ⟨p, hpS, hp⟩ := A.rare_exists_continuous_aux hA σ ρ L hsec hover
  have hp0 : 0 ≤ p := hpS.1
  refine ⟨p, ⟨hp0, fun j qj hqj ↦ ?_⟩, ?_⟩
  · obtain ⟨q, hqj', hqk, hRj, hRk⟩ := (hp j).2 qj hqj
    have hq0 : 0 ≤ q := fun k ↦ by
      by_cases hk : k = j
      · rw [hk, hqj']; exact hqj
      · exact (hp0 k).trans (hqk k hk).1
    refine ⟨q, hq0, hqj', ?_, fun k hk ↦ ((hRk k hk).2.trans (hRk k hk).1)⟩
    have h := (hp j).1.1
    change A.revenue q j ≤ M.kappa r * A.revenue p j + 0
    rw [h]
    linarith
  · have hκ := M.kappa_pos r
    rw [← A.sum_revenue_eq_revenueAll hp0, eq_div_iff hκ.ne', ← M.kappa_mul_nu_mul_beta r,
      sum_congr rfl fun j _ ↦ (hp j).1.1, ← mul_sum, hpS.2]
    ring

end Market.AllocRule
