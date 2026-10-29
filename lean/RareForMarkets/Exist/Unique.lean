module

public import RareForMarkets.Exist.Demand
public import RareForMarkets.Defs.Market
public import RareForMarkets.Exist.Defs

/-!
# Unique continuous allocation rules
(`\cref{thm:unique-nr-demand,thm:unique-rival-demand}`)

Stated for a member `M ε` of a family of markets, so that they also apply to perturbed markets.
-/

open Set

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Market

variable (Mf : ℝ → Market B G) (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget)
  (hcont : ∀ i, ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (Mf x.1).util i x.2) (Icc 0 1 ×ˢ cube G))
include hb hcont

/-- `\label{thm:unique-nr-demand}` (for a family of markets) -/
public theorem unique_nr_demand_family {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hu : ∀ i, StrictConcaveOn ℝ (cube G) ((Mf ε).util i)) :
    (∀ p : G → ℝ, 0 ≤ p → ∃! x, x ∈ (Mf ε).nonRivalDem p) ∧
      ∃ A : (Mf ε).AllocRule .nonRival, ContinuousOn A (Ici 0) := by
  obtain ⟨huniq, f, hf, hfc⟩ := exists_continuous_argmax (Y := nonRivalY B G)
    (b := (Mf 0).budget) isClosed_Icc shrinkClosed_nonRivalY (Mf 0).budget_pos subset_rfl
    ⟨le_rfl, zero_le_one⟩ convex_nonRivalY
    (continuousOn_welfareObj hcont isNiceWelfare_sum.continuousOn subset_rfl) hε
    ((Mf ε).strictConcaveOn_welfare hu isNiceWelfare_sum convex_nonRivalY subset_rfl)
  have hiff := fun {p : G → ℝ} (hp : 0 ≤ p) {x} ↦ mem_nonRivalDem_iff Mf hb hε hp (x := x)
  refine ⟨fun p hp ↦ ?_, ⟨f, fun p hp ↦ (hiff hp).mpr (hf p hp)⟩, hfc⟩
  obtain ⟨x, hx, hxu⟩ := huniq p hp
  exact ⟨x, (hiff hp).mpr hx, fun y hy ↦ hxu y ((hiff hp).mp hy)⟩

/-- `\label{thm:unique-rival-demand}` (for a family of markets) -/
public theorem unique_rival_demand_family {W : (B → ℝ) → ℝ} (hW : IsNiceWelfare W) {ε : ℝ}
    (hε : ε ∈ Icc (0 : ℝ) 1) (hu : ∀ i, StrictConcaveOn ℝ (cube G) ((Mf ε).util i)) :
    (∀ p : G → ℝ, 0 ≤ p → ∃! x, x ∈ (Mf ε).welfareDem W p) ∧
      ∃ A : (Mf ε).AllocRule .rival, ContinuousOn A (Ici 0) ∧
        ∀ p, 0 ≤ p → A p ∈ (Mf ε).welfareDem W p := by
  have hYc : rivalY B G ⊆ Icc 0 1 := fun x hx ↦ hx.1
  obtain ⟨huniq, f, hf, hfc⟩ := exists_continuous_argmax (Y := rivalY B G)
    (b := (Mf 0).budget) isClosed_rivalY shrinkClosed_rivalY (Mf 0).budget_pos hYc
    zero_mem_rivalY convex_rivalY (continuousOn_welfareObj hcont hW.continuousOn hYc) hε
    ((Mf ε).strictConcaveOn_welfare hu hW convex_rivalY hYc)
  have hiff := fun {p : G → ℝ} (hp : 0 ≤ p) {x} ↦ mem_welfareDem_iff Mf hb W hε hp (x := x)
  refine ⟨fun p hp ↦ ?_, ⟨f, fun p hp ↦ (Mf ε).welfareDem_subset_rivalDem hW.strictMonoOn p
    ((hiff hp).mpr (hf p hp))⟩, hfc, fun p hp ↦ (hiff hp).mpr (hf p hp)⟩
  obtain ⟨x, hx, hxu⟩ := huniq p hp
  exact ⟨x, (hiff hp).mpr hx, fun y hy ↦ hxu y ((hiff hp).mp hy)⟩

end Market

omit [Fintype B] [Fintype G] in
/-- The constant family `ε ↦ M`. -/
public theorem Market.continuousOn_util_const (M : Market B G) (i : B) :
    ContinuousOn (fun x : ℝ × (G → ℝ) ↦ ((fun _ : ℝ ↦ M) x.1).util i x.2)
      (Icc 0 1 ×ˢ cube G) :=
  (M.util_continuousOn i).comp continuousOn_snd fun _ hx ↦ hx.2
