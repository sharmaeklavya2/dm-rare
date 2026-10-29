module

public import RareForMarkets.Dynamics.Defs
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Rare
import RareForMarkets.Exist.Continuous
import RareForMarkets.Exist.Params
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Proofs for `\cref{sec:dynamics}`
-/

open Set Finset Filter Topology

variable {B G : Type*} [Fintype B] [Fintype G] [DecidableEq G]

/-! ### Worst-case and optimal deviation revenues -/

namespace Market.AllocRule

variable {M : Market B G} {r : Rivalry} (A : M.AllocRule r)

private theorem update_mem_irResponses {p : G → ℝ} (hp : 0 ≤ p) (j : G) {qj : ℝ} (hqj : 0 ≤ qj) :
    Function.update p j qj ∈ irResponses A j qj p := by
  refine ⟨fun k ↦ ?_, by simp, fun k _ ↦ le_rfl⟩
  by_cases hk : k = j
  · subst hk; simpa using hqj
  · simpa [hk] using hp k

private theorem worstRevenue_le {p : G → ℝ} {j : G} {qj : ℝ} {q : G → ℝ}
    (hq : q ∈ irResponses A j qj p) : worstRevenue A j qj p ≤ A.revenue q j :=
  csInf_le ⟨0, by rintro _ ⟨q', hq', rfl⟩; exact A.revenue_nonneg hq'.1 j⟩ ⟨q, hq, rfl⟩

private theorem worstRevenue_le_totalBudget {p : G → ℝ} (hp : 0 ≤ p) (j : G) {qj : ℝ}
    (hqj : 0 ≤ qj) : worstRevenue A j qj p ≤ M.totalBudget :=
  (A.worstRevenue_le (A.update_mem_irResponses hp j hqj)).trans
    (A.revenue_le_totalBudget (A.update_mem_irResponses hp j hqj).1 j)

private theorem worstRevenue_le_optDevRevenue {p : G → ℝ} (hp : 0 ≤ p) (j : G) {qj : ℝ}
    (hqj : 0 ≤ qj) : worstRevenue A j qj p ≤ optDevRevenue A j p :=
  le_csSup ⟨M.totalBudget, by
    rintro _ ⟨qj', hqj', rfl⟩; exact A.worstRevenue_le_totalBudget hp j hqj'⟩ ⟨qj, hqj, rfl⟩

private theorem optDevRevenue_le {p : G → ℝ} {j : G} {c : ℝ}
    (h : ∀ qj, 0 ≤ qj → worstRevenue A j qj p ≤ c) : optDevRevenue A j p ≤ c :=
  csSup_le ⟨_, 0, Set.mem_Ici.mpr le_rfl, rfl⟩ fun _ ⟨qj, hqj, h'⟩ ↦ h' ▸ h qj hqj

/-- If every seller's optimal deviation revenue is less than `κ R_j(p) + δ`,
then `p` is a `δ`-additive `κ`-RARE. -/
private theorem isRare_of_optDevRevenue_lt {p : G → ℝ} (hp : 0 ≤ p) {δ κ : ℝ}
    (h : ∀ j, optDevRevenue A j p < κ * A.revenue p j + δ) : IsRare A δ κ p := by
  refine ⟨hp, fun j qj hqj ↦ ?_⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
    (Set.Nonempty.image _ ⟨_, A.update_mem_irResponses hp j hqj⟩)
    ((A.worstRevenue_le_optDevRevenue hp j hqj).trans_lt (h j))
  exact ⟨q, hq.1, hq.2.1, hlt.le, hq.2.2⟩

/-! ### `\cref{thm:vbound-pstar}` -/

local notation "ν" => Market.nu (B := B) r
local notation "β" => Market.beta M r
local notation "κ" => Market.kappa M r

/-- `\label{thm:vbound-pstar}` -/
private theorem exists_vbound [Nonempty B] [Nonempty G] (hA : ContinuousOn A (Ici 0)) :
    ∃ ps ∈ scaledSimplex G β, ∀ p, 0 ≤ p → p ≤ ps → ∀ j,
      optDevRevenue A j p ≤ ps j * κ * ν := by
  obtain ⟨σ, ρ, L, hsec, hover⟩ := M.exists_params r
  obtain ⟨ps, hpS, hps⟩ := A.rare_exists_continuous_aux hA σ ρ L hsec hover
  refine ⟨ps, hpS, fun p hp hpps j ↦ A.optDevRevenue_le fun qj hqj ↦ ?_⟩
  obtain ⟨q, hqj', hqk, hRj, hRk⟩ := (hps j).2 qj hqj
  have hq0 : 0 ≤ q := fun k ↦ by
    by_cases hk : k = j
    · rw [hk, hqj']; exact hqj
    · exact (hpS.1 k).trans (hqk k hk).1
  refine (A.worstRevenue_le ⟨hq0, hqj', fun k hk ↦ ?_⟩).trans hRj
  have hupd0 := (A.update_mem_irResponses hp j hqj).1
  calc A.revenue (Function.update p j qj) k ≤ ν * Function.update p j qj k :=
        A.revenue_le_nu hupd0 k
    _ = ν * p k := by simp [hk]
    _ ≤ ν * ps k := mul_le_mul_of_nonneg_left (hpps k) (Market.nu_pos r).le
    _ ≤ _ := (hRk k hk).1

end Market.AllocRule

/-! ### The dynamic -/

namespace Market.IsDynamic

variable [Nonempty B] {M : Market B G} {r : Rivalry} {A : M.AllocRule r}
  {p : ℕ → G → ℝ} {S : ℕ → Set G}

local notation "ν" => Market.nu (B := B) r
local notation "β" => Market.beta M r
local notation "κ" => Market.kappa M r

/-- Prices never decrease. -/
private theorem le_succ (hdyn : M.IsDynamic A p S) (t : ℕ) (j : G) : p t j ≤ p (t + 1) j := by
  by_cases hj : j ∈ S t
  · have h1 := hdyn.subset t hj
    have h2 := hdyn.update_mem t j hj
    simp only [unsatisfied, mem_setOf_eq] at h1
    rw [← h2] at h1
    have h1' : p t j * (κ * ν) < p (t + 1) j * (κ * ν) := by simpa only [mul_assoc] using h1
    exact (lt_of_mul_lt_mul_right h1'
      (mul_pos (M.kappa_pos r) (Market.nu_pos r)).le).le
  · rw [hdyn.update_not_mem t j hj]

/-- Prices stay between `0` and `p*`. -/
public theorem bounds [Nonempty G] (hdyn : M.IsDynamic A p S) {ps : G → ℝ}
    (hps : ∀ q, 0 ≤ q → q ≤ ps → ∀ j, optDevRevenue A j q ≤ ps j * κ * ν) (hps0 : 0 ≤ ps)
    (t : ℕ) : 0 ≤ p t ∧ p t ≤ ps := by
  have hκν : 0 < κ * ν := mul_pos (M.kappa_pos r) (Market.nu_pos r)
  induction t with
  | zero => rw [hdyn.zero]; exact ⟨le_rfl, hps0⟩
  | succ t ih =>
    refine ⟨fun j ↦ (ih.1 j).trans (hdyn.le_succ t j), fun j ↦ ?_⟩
    by_cases hj : j ∈ S t
    · have h := hdyn.update_mem t j hj
      have h' := hps (p t) ih.1 ih.2 j
      rw [← h, mul_assoc, mul_assoc] at h'
      exact le_of_mul_le_mul_right h' hκν
    · rw [hdyn.update_not_mem t j hj]; exact ih.2 j

/-- Throughout the dynamic, every seller sells out. -/
public theorem revenue_eq [Nonempty G] (hdyn : M.IsDynamic A p S) (hA : ContinuousOn A (Ici 0))
    (t : ℕ) (j : G) : A.revenue (p t) j = ν * p t j := by
  obtain ⟨ps, hpS, hps⟩ := A.exists_vbound hA
  have hb := hdyn.bounds hps hpS.1 t
  exact A.revenue_eq_of_sum_le hb.1 (hpS.2 ▸ sum_le_sum fun k _ ↦ hb.2 k) j

/-- `\label{thm:dynamics-convergence}` -/
public theorem convergence [Nonempty G] (hdyn : M.IsDynamic A p S) (hA : ContinuousOn A (Ici 0))
    (hmax : ∀ t, (unsatisfied A (p t)).Nonempty → ∃ j ∈ S t, ∀ k,
      optDevRevenue A k (p t) - p t k * (κ * ν) ≤ optDevRevenue A j (p t) - p t j * (κ * ν))
    {δ : ℝ} (hδ : 0 < δ) :
    (∃ t ≤ ⌊M.totalBudget / δ⌋₊, IsRare A δ κ (p t)) ∧ ∃ T, ∀ t > T, IsRare A δ κ (p t) := by
  obtain ⟨ps, hpS, hps⟩ := A.exists_vbound hA
  have hb := hdyn.bounds hps hpS.1
  have hκν : 0 < κ * ν := mul_pos (M.kappa_pos r) (Market.nu_pos r)
  -- The total price increase `h t` in round `t`, scaled by `κν`.
  let h : ℕ → ℝ := fun t ↦ κ * ν * ∑ k, (p (t + 1) k - p t k)
  have hh0 : ∀ t, 0 ≤ h t := fun t ↦
    mul_nonneg hκν.le (sum_nonneg fun k _ ↦ sub_nonneg.mpr (hdyn.le_succ t k))
  have hsum : ∀ T, ∑ t ∈ range T, h t ≤ M.totalBudget := by
    intro T
    have : ∑ t ∈ range T, h t = κ * ν * ∑ k, p T k := by
      simp only [h, ← mul_sum]
      rw [sum_comm]
      congr 1
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sum_range_sub (fun t ↦ p t k), hdyn.zero, Pi.zero_apply, sub_zero]
    rw [this, ← M.kappa_mul_nu_mul_beta r, ← hpS.2]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun k _ ↦ (hb T).2 k) hκν.le
  -- Each seller's dissatisfaction is at most `h t`.
  have hd : ∀ t j, optDevRevenue A j (p t) - p t j * (κ * ν) ≤ h t := by
    intro t j
    rcases (unsatisfied A (p t)).eq_empty_or_nonempty with he | hne
    · have : j ∉ unsatisfied A (p t) := by rw [he]; exact Set.notMem_empty j
      simp only [unsatisfied, mem_setOf_eq, not_lt] at this
      linarith [hh0 t]
    · obtain ⟨j', hj'S, hj'⟩ := hmax t hne
      calc _ ≤ _ := hj' j
        _ = κ * ν * (p (t + 1) j' - p t j') := by
          rw [← hdyn.update_mem t j' hj'S]; ring
        _ ≤ h t := mul_le_mul_of_nonneg_left
          (single_le_sum (fun k _ ↦ sub_nonneg.mpr (hdyn.le_succ t k)) (mem_univ j')) hκν.le
  have hrare : ∀ t, h t < δ → IsRare A δ κ (p t) := by
    intro t ht
    refine A.isRare_of_optDevRevenue_lt (hb t).1 fun j ↦ ?_
    rw [hdyn.revenue_eq hA t j]
    have := hd t j
    nlinarith
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    set T := ⌊M.totalBudget / δ⌋₊
    have hge : ∀ t ∈ range (T + 1), δ ≤ h t := fun t ht ↦
      not_lt.mp fun hlt ↦ hcon t (Nat.lt_succ_iff.mp (mem_range.mp ht)) (hrare t hlt)
    have h1 := sum_le_sum hge
    simp only [sum_const, card_range, nsmul_eq_mul] at h1
    have h2 : M.totalBudget / δ < T + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hδ] at h2
    push_cast at h1
    linarith [hsum (T + 1)]
  · have hs : Summable h := summable_of_sum_range_le hh0 hsum
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      (hs.tendsto_atTop_zero.eventually (gt_mem_nhds hδ))
    exact ⟨T, fun t ht ↦ hrare t (hT t ht.le)⟩

end Market.IsDynamic
