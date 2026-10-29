module

public import RareForMarkets.Prelims
public import RareForMarkets.Defs.Market
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Monoid

/-!
# Market parameters and `\cref{thm:accounting}`

Basic facts about `ν`, `β`, `κ` and the accounting identities for revenues.
-/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Market

variable (M : Market B G)

/-! ### The parameters `ν`, `β`, `κ` -/

omit [Fintype G] in
public theorem nu_pos [Nonempty B] (r : Rivalry) : 0 < nu (B := B) r := by
  cases r
  · simp [nu]
  · simp [nu, Fintype.card_pos]

omit [Fintype G] in
public theorem beta_pos [Nonempty B] (r : Rivalry) : 0 < M.beta r := by
  cases r
  exacts [M.totalBudget_pos, M.minBudget_pos]

omit [Fintype G] in
public theorem nu_mul_beta_le (r : Rivalry) : nu (B := B) r * M.beta r ≤ M.totalBudget := by
  cases r
  · simp [nu, beta]
  · simpa [nu, beta, totalBudget] using
      sum_le_sum fun i (_ : i ∈ univ) ↦ M.minBudget_le i

omit [Fintype G] in
public theorem beta_le_totalBudget [Nonempty B] (r : Rivalry) : M.beta r ≤ M.totalBudget := by
  have h1 : 1 ≤ nu (B := B) r := by
    cases r
    · simp [nu]
    · simpa [nu] using Fintype.card_pos (α := B)
  nlinarith [M.nu_mul_beta_le r, M.beta_pos r]

omit [Fintype G] in
/-- `κνβ = B`. -/
public theorem kappa_mul_nu_mul_beta [Nonempty B] (r : Rivalry) :
    M.kappa r * nu (B := B) r * M.beta r = M.totalBudget := by
  have := mul_pos (nu_pos (B := B) r) (M.beta_pos r)
  rw [M.kappa_eq r, mul_assoc, div_mul_cancel₀ _ this.ne']

omit [Fintype G] in
public theorem kappa_pos [Nonempty B] (r : Rivalry) : 0 < M.kappa r := by
  rw [M.kappa_eq r]
  exact div_pos M.totalBudget_pos (mul_pos (nu_pos r) (M.beta_pos r))

omit [Fintype G] in
public theorem one_le_kappa [Nonempty B] (r : Rivalry) : 1 ≤ M.kappa r := by
  rw [M.kappa_eq r, one_le_div (mul_pos (nu_pos r) (M.beta_pos r))]
  exact M.nu_mul_beta_le r

omit [Fintype G] in
/-- The parameters only depend on the budgets. -/
public theorem kappa_congr {M' : Market B G} (h : M.budget = M'.budget) (r : Rivalry) :
    M.kappa r = M'.kappa r := by
  cases r <;> simp [kappa, avgBudget, minBudget, totalBudget, h]

omit [Fintype G] in
public theorem beta_congr {M' : Market B G} (h : M.budget = M'.budget) (r : Rivalry) :
    M.beta r = M'.beta r := by
  cases r <;> simp [beta, minBudget, totalBudget, h]

omit [Fintype G] in
public theorem totalBudget_congr {M' : Market B G} (h : M.budget = M'.budget) :
    M.totalBudget = M'.totalBudget := by
  simp [totalBudget, h]

/-! ### `\cref{thm:accounting}` -/

public theorem revenue_nonneg {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ} (hx : x ∈ M.nonRivalAff p)
    (j : G) : 0 ≤ revenue p x j :=
  mul_nonneg (hp j) (sum_nonneg fun i _ ↦ (hx i).1.1 j)

public theorem revenue_nonneg_of_mem_dem {r : Rivalry} {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.dem r p) (j : G) : 0 ≤ revenue p x j :=
  M.revenue_nonneg hp (M.dem_subset_nonRivalAff r p hx) j

/-- `R_j(p, x) ≤ ν pⱼ`. -/
public theorem revenue_le_nu {r : Rivalry} {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.dem r p) (j : G) : revenue p x j ≤ nu (B := B) r * p j := by
  cases r
  · simpa [nu] using mul_le_of_le_one_right (hp j) (hx.1.1 j)
  · have : ∑ i, x i j ≤ Fintype.card B := by
      simpa using sum_le_sum fun i (_ : i ∈ univ) ↦ (hx i).1.1.2 j
    simpa [nu, revenue, mul_comm] using mul_le_mul_of_nonneg_left this (hp j)

/-- `R_all(p) ≤ B`. -/
public theorem revenueAll_le (r : Rivalry) (p : G → ℝ) : M.revenueAll r p ≤ M.totalBudget := by
  cases r
  · exact min_le_left _ _
  · exact (M.F_le _).trans (min_le_left _ _)

public theorem revenue_le_totalBudget {r : Rivalry} {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.dem r p) (j : G) : revenue p x j ≤ M.totalBudget := by
  have h := M.sum_revenue_eq_revenueAll hp hx
  have : revenue p x j ≤ ∑ k, revenue p x k :=
    single_le_sum (fun k _ ↦ M.revenue_nonneg_of_mem_dem hp hx k) (mem_univ j)
  linarith [M.revenueAll_le r p]

omit [Fintype G] in
/-- If `∑ⱼ pⱼ ≤ β`, then `R_all(p) = ν ∑ⱼ pⱼ`. -/
private theorem revenueAll_eq_of_sum_le [Nonempty B] {r : Rivalry} {s : ℝ} (hs : s ≤ M.beta r) :
    (match r with
      | .rival => min M.totalBudget s
      | .nonRival => M.F s) = nu (B := B) r * s := by
  cases r
  · simpa [nu] using hs.trans (M.beta_le_totalBudget .rival)
  · simp only [F, nu]
    rw [sum_congr rfl fun i _ ↦ min_eq_right (hs.trans (M.minBudget_le i))]
    simp

/-- `∑ⱼ pⱼ ≤ β ⟹ R_j(p, x) = ν pⱼ`. -/
public theorem revenue_eq_of_sum_le [Nonempty B] {r : Rivalry} {p : G → ℝ} (hp : 0 ≤ p)
    {x : B → G → ℝ} (hx : x ∈ M.dem r p) (hsum : ∑ j, p j ≤ M.beta r) (j : G) :
    revenue p x j = nu (B := B) r * p j := by
  have hall := M.sum_revenue_eq_revenueAll hp hx
  have hall' : M.revenueAll r p = ∑ k, nu (B := B) r * p k := by
    rw [← mul_sum]
    cases r
    exacts [M.revenueAll_eq_of_sum_le (r := .rival) hsum,
      M.revenueAll_eq_of_sum_le (r := .nonRival) hsum]
  rw [hall'] at hall
  exact (sum_eq_sum_iff_of_le fun k _ ↦ M.revenue_le_nu hp hx k).mp hall j (mem_univ j)

omit [Fintype G] in
/-- `∑ⱼ pⱼ ≥ β ⟹ R_all(p) ≥ νβ`. -/
private theorem nu_mul_beta_le_revenueAll' [Nonempty B] {r : Rivalry} {s : ℝ} (hs : M.beta r ≤ s) :
    nu (B := B) r * M.beta r ≤
      (match r with
        | .rival => min M.totalBudget s
        | .nonRival => M.F s) := by
  cases r
  · simpa [nu, beta] using hs
  · simp only [F, nu, beta] at hs ⊢
    simpa using sum_le_sum fun i (_ : i ∈ univ) ↦ le_min (M.minBudget_le i) hs

public theorem nu_mul_beta_le_revenueAll [Nonempty B] {r : Rivalry} {p : G → ℝ}
    (hs : M.beta r ≤ ∑ j, p j) : nu (B := B) r * M.beta r ≤ M.revenueAll r p := by
  cases r
  exacts [M.nu_mul_beta_le_revenueAll' (r := .rival) hs,
    M.nu_mul_beta_le_revenueAll' (r := .nonRival) hs]

end Market

/-! ### Continuity of revenues -/

omit [Fintype G] in
public theorem continuous_revenue (j : G) :
    Continuous fun px : (G → ℝ) × (B → G → ℝ) ↦ revenue px.1 px.2 j := by
  unfold revenue
  fun_prop

namespace Market.AllocRule

variable {M : Market B G} {r : Rivalry}

public theorem continuousOn_revenue (A : M.AllocRule r) (hA : ContinuousOn A (Set.Ici 0)) (j : G) :
    ContinuousOn (fun q ↦ A.revenue q j) (Set.Ici 0) :=
  (continuous_revenue j).comp_continuousOn (continuousOn_id.prodMk hA)

end Market.AllocRule
