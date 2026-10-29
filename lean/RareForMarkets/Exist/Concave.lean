module

public import RareForMarkets.Exist.Limit
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Misc
public import RareForMarkets.Exist.Defs
import RareForMarkets.Exist.Unique
import RareForMarkets.Exist.Perturb
import RareForMarkets.Exist.Params

/-!
# RARE for concave utilities (`\cref{thm:nonrival-rare-exists,thm:rival-rare-exists}`)
-/

open Set

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Market

variable (M : Market B G)

omit [Fintype B] in
/-- If `∑ⱼ pⱼ = b_min`, every buyer can buy every good completely. -/
private theorem one_mem_nonRivalDem [Finite B] {p : G → ℝ} (hsum : ∑ j, p j = M.minBudget) :
    (1 : B → G → ℝ) ∈ M.nonRivalDem p := by
  intro i
  have h1 : (1 : B → G → ℝ) i ∈ M.budgetSet i p :=
    ⟨⟨fun _ ↦ zero_le_one, le_rfl⟩, by simpa [hsum] using M.minBudget_le i⟩
  exact ⟨h1, fun z hz ↦ (M.util_strictMonoOn i).monotoneOn hz.1 h1.1 hz.1.2⟩

private theorem one_div_succ_mem_Icc (t : ℕ) : 1 / ((t : ℝ) + 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨by positivity, (div_le_one (by positivity)).mpr (by simp)⟩

/-- `\label{thm:nonrival-rare-exists}` -/
public theorem nonrival_rare_exists_aux [Nonempty B] [Nonempty G]
    (hu : ∀ i, ConcaveOn ℝ (cube G) (M.util i)) :
    ∃ p ∈ openScaledSimplex G M.minBudget, 1 ∈ M.nonRivalDem p ∧
      ∀ j qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧ ∃ x ∈ M.nonRivalDem q,
        revenue q x j ≤ M.avgBudget / M.minBudget * revenue p (1 : B → G → ℝ) j ∧
        revenue p (1 : B → G → ℝ) j = Fintype.card B * p j ∧
        ∀ k ≠ j, Fintype.card B * p k ≤ revenue q x k := by
  classical
  have hb : ∀ ε, (M.perturb ε).budget = (M.perturb 0).budget := fun _ ↦ rfl
  have hcont := M.continuousOn_perturb
  obtain ⟨σ, ρ, L, hpar⟩ := exists_params_family M.perturb hb hcont .nonRival
  have hΓ := isClosed_argmaxGraph isClosed_Icc shrinkClosed_nonRivalY
    (M.perturb 0).budget_pos (continuousOn_welfareObj hcont isNiceWelfare_sum.continuousOn
      (Y := nonRivalY B G) subset_rfl)
  choose A hA using fun t : ℕ ↦ (unique_nr_demand_family M.perturb hb hcont
    (one_div_succ_mem_Icc t) fun i ↦ M.strictConcaveOn_perturb (hu i) (by positivity)).2
  obtain ⟨p, hpS, x, -, hpx, hdev⟩ := limit_rare M.perturb hb .nonRival σ ρ L
    (fun ε hε j ↦ (hpar ε hε).1 j) (fun ε hε j ↦ (hpar ε hε).2 j) _ hΓ A hA
    (fun t p hp ↦ (mem_nonRivalDem_iff M.perturb hb (one_div_succ_mem_Icc t) hp).mp
      ((A t).mem_dem p hp))
  have hρ : ∀ j, 0 < ρ j := fun j ↦ ((hpar 0 ⟨le_rfl, zero_le_one⟩).1 j).ρ_pos
  rw [M.perturb_zero] at hpS hpx hdev
  refine ⟨p, ⟨fun j ↦ ?_, hpS.2⟩, M.one_mem_nonRivalDem hpS.2, fun j qj hqj ↦ ?_⟩
  · have h := (hpx j).2
    have hβ := M.beta_pos .nonRival
    have hB := M.totalBudget_pos
    by_contra hpj
    nlinarith [mul_pos hβ (hρ j), mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hpj) hB.le]
  obtain ⟨q, hq0, hqj', z, hzΓ, hRj, hRk⟩ := hdev j qj hqj
  have hz := (mem_nonRivalDem_iff M.perturb hb ⟨le_rfl, zero_le_one⟩ hq0).mpr hzΓ
  rw [M.perturb_zero] at hz
  have h1 : revenue p (1 : B → G → ℝ) j = Fintype.card B * p j := by
    simp [revenue, mul_comm]
  refine ⟨q, hq0, hqj', z, hz, ?_, h1, fun k hk ↦ hRk k hk⟩
  rw [h1]
  calc revenue q z j ≤ p j * M.kappa .nonRival * nu (B := B) .nonRival := hRj
    _ = _ := by simp only [kappa, nu]; ring

/-- `\label{thm:rival-rare-exists}` -/
public theorem rival_rare_exists_aux [Nonempty G] [Nonempty B]
    (hu : ∀ i, ConcaveOn ℝ (cube G) (M.util i)) (W : (B → ℝ) → ℝ) (hW : IsNiceWelfare W) :
    ∃ p ∈ openScaledSimplex G M.totalBudget, ∃ x ∈ M.welfareDem W p,
      ∀ j qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧ ∃ z ∈ M.welfareDem W q,
        revenue q z j ≤ revenue p x j ∧ revenue p x j = p j ∧
        ∀ k ≠ j, p k ≤ revenue q z k := by
  classical
  have hb : ∀ ε, (M.perturb ε).budget = (M.perturb 0).budget := fun _ ↦ rfl
  have hcont := M.continuousOn_perturb
  obtain ⟨σ, ρ, L, hpar⟩ := exists_params_family M.perturb hb hcont .rival
  have hΓ := isClosed_argmaxGraph isClosed_rivalY shrinkClosed_rivalY
    (M.perturb 0).budget_pos (continuousOn_welfareObj hcont hW.continuousOn
      (Y := rivalY B G) fun x hx ↦ hx.1)
  choose A hAc hAw using fun t : ℕ ↦ (unique_rival_demand_family M.perturb hb hcont hW
    (one_div_succ_mem_Icc t) fun i ↦ M.strictConcaveOn_perturb (hu i) (by positivity)).2
  obtain ⟨p, hpS, x, hxΓ, hpx, hdev⟩ := limit_rare M.perturb hb .rival σ ρ L
    (fun ε hε j ↦ (hpar ε hε).1 j) (fun ε hε j ↦ (hpar ε hε).2 j) _ hΓ A hAc
    (fun t p hp ↦ (mem_welfareDem_iff M.perturb hb W (one_div_succ_mem_Icc t) hp).mp
      (hAw t p hp))
  have hρ : ∀ j, 0 < ρ j := fun j ↦ ((hpar 0 ⟨le_rfl, zero_le_one⟩).1 j).ρ_pos
  have hx := (mem_welfareDem_iff M.perturb hb W ⟨le_rfl, zero_le_one⟩ hpS.1).mpr hxΓ
  rw [M.perturb_zero] at hpS hpx hdev hx
  simp only [beta, kappa, nu, one_mul, mul_one] at hpS hpx hdev
  refine ⟨p, ⟨fun j ↦ ?_, hpS.2⟩, x, hx, fun j qj hqj ↦ ?_⟩
  · have h := (hpx j).2
    have hB := M.totalBudget_pos
    by_contra hpj
    nlinarith [mul_pos hB (hρ j), mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hpj) hB.le]
  obtain ⟨q, hq0, hqj', z, hzΓ, hRj, hRk⟩ := hdev j qj hqj
  have hz := (mem_welfareDem_iff M.perturb hb W ⟨le_rfl, zero_le_one⟩ hq0).mpr hzΓ
  rw [M.perturb_zero] at hz
  exact ⟨q, hq0, hqj', z, hz, by rw [(hpx j).1]; exact hRj, (hpx j).1, hRk⟩

end Market
