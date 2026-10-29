module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import RareForMarkets.Defs.Market

/-!
Results from `\cref{sec:prelims,sec:revenue-props}` in the paper,
except the subsection on the simplex and the KKM lemma.
-/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

omit [Fintype G] in
/-- `StrictMonoOn f (cube G)` is exactly the paper's strict monotonicity: for any two distinct
`x, y ∈ [0, 1]^m` with `xⱼ ≤ yⱼ` for all `j`, we have `f(x) < f(y)`. -/
public theorem strictMonoOn_cube_iff {f : (G → ℝ) → ℝ} :
    StrictMonoOn f (cube G) ↔
      ∀ x ∈ cube G, ∀ y ∈ cube G, x ≠ y → (∀ j, x j ≤ y j) → f x < f y := by
  refine ⟨fun h x hx y hy hne hle ↦ h hx hy (lt_of_le_of_ne hle hne),
    fun h x hx y hy hlt ↦ h x hx y hy hlt.ne hlt.le⟩

namespace Market

variable (M : Market B G)

omit [Fintype B] [Fintype G] in
public theorem util_nonneg (i : B) {z : G → ℝ} (hz : z ∈ cube G) : 0 ≤ M.util i z := by
  have h0 : (0 : G → ℝ) ∈ cube G := ⟨le_rfl, zero_le_one⟩
  simpa [M.util_zero] using (M.util_strictMonoOn i).monotoneOn h0 hz hz.1

/-! ### Budgets -/

omit [Fintype B] [Fintype G] in
public theorem minBudget_le [Finite B] (i : B) : M.minBudget ≤ M.budget i :=
  ciInf_le (Set.finite_range _).bddBelow i

omit [Fintype B] [Fintype G] in
public theorem minBudget_pos [Finite B] [Nonempty B] : 0 < M.minBudget := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := M.budget)
  rw [minBudget, ← hi]
  exact M.budget_pos i

omit [Fintype G] in
public theorem totalBudget_pos [Nonempty B] : 0 < M.totalBudget :=
  sum_pos (fun i _ ↦ M.budget_pos i) univ_nonempty

omit [Fintype G] in
/-- `κ = B / (νβ)`. -/
public theorem kappa_eq [Nonempty B] (r : Rivalry) :
    M.kappa r = M.totalBudget / (nu (B := B) r * M.beta r) := by
  cases r
  · simp [kappa, nu, beta, M.totalBudget_pos.ne']
  · simp [kappa, nu, beta, avgBudget, div_div]

/-! ### Demand -/

private theorem rivalAff_subset_nonRivalAff (p : G → ℝ) : M.rivalAff p ⊆ M.nonRivalAff p :=
  fun _ hx ↦ hx.2

omit [Fintype B] in
public theorem nonRivalDem_subset_nonRivalAff (p : G → ℝ) : M.nonRivalDem p ⊆ M.nonRivalAff p :=
  fun _ hx i ↦ (hx i).1

public theorem dem_subset_nonRivalAff (r : Rivalry) (p : G → ℝ) : M.dem r p ⊆ M.nonRivalAff p := by
  cases r
  exacts [fun _ hx ↦ M.rivalAff_subset_nonRivalAff p hx.1, M.nonRivalDem_subset_nonRivalAff p]

omit [Fintype B] in
/-- Observation (unlabeled): `Dem^NR(p) = PO(Aff^NR(p))`. -/
private theorem nonRivalDem_eq_paretoOpt (p : G → ℝ) :
    M.nonRivalDem p = M.paretoOpt (M.nonRivalAff p) := by
  classical
  ext x
  refine ⟨fun hx ↦ ⟨M.nonRivalDem_subset_nonRivalAff p hx, ?_⟩, fun ⟨hx, hPO⟩ i ↦ ⟨hx i, ?_⟩⟩
  · -- No affordable allocation can make a buyer strictly better off than her demanded bundle.
    rintro y hy ⟨-, i, hi⟩
    exact (hi.trans_le ((hx i).2 (hy i))).false
  · -- Otherwise, replacing `x i` by a better affordable bundle `z` Pareto dominates `x`.
    intro z hz
    change M.util i z ≤ M.util i (x i)
    by_contra! hlt
    refine hPO (Function.update x i z) (fun k ↦ ?_) ⟨fun k ↦ ?_, i, by simpa using hlt⟩
    · rcases eq_or_ne k i with rfl | hk
      · simpa using hz
      · simpa [hk] using hx k
    · rcases eq_or_ne k i with rfl | hk
      · simpa using hlt.le
      · simp [hk]

/-- When there is only one buyer, the rivalrous and non-rivalrous settings coincide. -/
private theorem rivalDem_eq_nonRivalDem [Subsingleton B] (p : G → ℝ) :
    M.rivalDem p = M.nonRivalDem p := by
  have hAff : M.rivalAff p = M.nonRivalAff p := by
    refine (M.rivalAff_subset_nonRivalAff p).antisymm fun x hx ↦ ⟨fun j ↦ ?_, hx⟩
    cases isEmpty_or_nonempty B with
    | inl _ => simp
    | inr h =>
      obtain ⟨i⟩ := h
      rw [Fintype.sum_subsingleton _ i]
      exact (hx i).1.2 j
  rw [rivalDem, hAff, nonRivalDem_eq_paretoOpt]

end Market

/-! ### Linear utilities -/

/-- Spending on `z + ε eⱼ` at prices `p`. -/
private theorem sum_mul_add_single [DecidableEq G] (p z : G → ℝ) (j : G) (ε : ℝ) :
    ∑ l, p l * (z + Pi.single j ε : G → ℝ) l = ∑ l, p l * z l + p j * ε := by
  simp [mul_add, sum_add_distrib, Pi.single_apply]

omit [Fintype G] in
/-- `z + ε eⱼ` stays in the cube if `z` does and `ε ∈ [0, 1 - zⱼ]`. -/
private theorem add_single_mem_cube [DecidableEq G] {z : G → ℝ} (hz : z ∈ cube G) {j : G}
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 - z j) : z + Pi.single j ε ∈ cube G := by
  have h0 : ∀ l, 0 ≤ z l := hz.1
  refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩ <;> by_cases hl : l = j
  · subst hl; simp; linarith [h0 l]
  · simpa [hl] using h0 l
  · subst hl; simp; linarith
  · simpa [hl] using hz.2 l

omit [Fintype G] in
/-- `z < z + ε eⱼ` when `ε > 0`. -/
private theorem lt_add_single [DecidableEq G] (z : G → ℝ) (j : G) {ε : ℝ} (hε : 0 < ε) :
    z < z + Pi.single j ε :=
  Pi.lt_def.mpr ⟨fun l ↦ by by_cases hl : l = j <;> simp [hl, hε.le], j, by simpa using hε⟩

omit [Fintype B] in
/-- bang-per-buck ordering: for linear utilities, every demanded bundle buys a good `j`
completely before buying any good `k` with a worse price-to-utility ratio. -/
public theorem Market.bangPerBuck (M : Market B G) {i : B} {w : G → ℝ}
    (hu : M.util i = linearUtil w) (hw : ∀ j, 0 < w j) {p : G → ℝ} (hp : 0 ≤ p)
    {z : G → ℝ} (hz : z ∈ M.demand i p) {j k : G} (hjk : p j / w j < p k / w k) :
    z j = 1 ∨ z k = 0 := by
  classical
  -- Otherwise, move money from good `k` to good `j`: raise `z j` by `ε` and lower `z k` by
  -- `c = ε pⱼ / pₖ`. This costs nothing and strictly increases utility.
  by_contra! h
  obtain ⟨hj1, hk0⟩ := h
  obtain ⟨⟨hz0, hz1⟩, hzb⟩ := hz.1
  have hp : ∀ l, 0 ≤ p l := hp
  have hz0 : ∀ l, 0 ≤ z l := hz0
  have hz1 : ∀ l, z l ≤ 1 := hz1
  have hjk' : p j * w k < w j * p k := by
    rwa [div_lt_div_iff₀ (hw j) (hw k), mul_comm (p k)] at hjk
  have hne : j ≠ k := by rintro rfl; exact hjk.false
  have hpk : 0 < p k := by
    by_contra! h; nlinarith [hw j, hw k, hp k, hp j]
  have hzj1 : z j < 1 := lt_of_le_of_ne (hz1 j) hj1
  have hzk0 : 0 < z k := lt_of_le_of_ne (hz0 k) (Ne.symm hk0)
  set μ := min (1 - z j) (z k) with hμ
  have hμ0 : 0 < μ := lt_min (by linarith) hzk0
  set ε := μ * p k / (p j + p k) with hε
  set c := ε * p j / p k with hc
  have hpjk : 0 < p j + p k := by linarith [hp j]
  have hε0 : 0 < ε := by positivity
  have hεj : ε ≤ 1 - z j := by
    rw [hε, div_le_iff₀ hpjk]
    nlinarith [min_le_left (1 - z j) (z k), hp j]
  have hck : c ≤ z k := by
    have hc' : c = μ * p j / (p j + p k) := by
      rw [hc, hε]; field_simp
    rw [hc', div_le_iff₀ hpjk]
    nlinarith [min_le_right (1 - z j) (z k), hp j]
  have hc0 : 0 ≤ c := by have := hp j; positivity
  let z' : G → ℝ := z + Pi.single j ε - Pi.single k c
  have hz'j : z' j = z j + ε := by simp [z', hne]
  have hz'k : z' k = z k - c := by simp [z', hne.symm]
  have hz'l : ∀ l, l ≠ j → l ≠ k → z' l = z l := by intro l hj hk; simp [z', hj, hk]
  have hmem : z' ∈ M.budgetSet i p := by
    refine ⟨⟨fun l ↦ ?_, fun l ↦ ?_⟩, ?_⟩
    · by_cases hl : l = j
      · subst hl; rw [Pi.zero_apply, hz'j]; linarith [hz0 l]
      by_cases hl' : l = k
      · subst hl'; rw [Pi.zero_apply, hz'k]; linarith
      rw [hz'l l hl hl']; exact hz0 l
    · by_cases hl : l = j
      · subst hl; rw [Pi.one_apply, hz'j]; linarith
      by_cases hl' : l = k
      · subst hl'; rw [Pi.one_apply, hz'k]; linarith [hz1 l]
      rw [hz'l l hl hl']; exact hz1 l
    · have : ∑ l, p l * z' l = ∑ l, p l * z l + p j * ε - p k * c := by
        simp [z', mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, Pi.single_apply]
      rw [this, hc, mul_div_cancel₀ _ hpk.ne']
      linarith
  have hutil : M.util i z' = M.util i z + (w j * ε - w k * c) := by
    simp only [hu, linearUtil, z']
    simp [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, Pi.single_apply]
    ring
  have hgain : 0 < w j * ε - w k * c := by
    have : w j * ε - w k * c = ε * (w j * p k - p j * w k) / p k := by
      rw [hc]; field_simp
    rw [this]
    exact div_pos (mul_pos hε0 (by linarith)) hpk
  have hle : M.util i z' ≤ M.util i z := hz.2 hmem
  linarith

/-! ### Sellers' revenues -/

omit [Fintype G] in
/-- The total revenue of a set `S` of sellers equals the buyers' total spending on `S`. -/
private theorem sum_revenue_eq (p : G → ℝ) (x : B → G → ℝ) (S : Finset G) :
    ∑ j ∈ S, revenue p x j = ∑ i, ∑ j ∈ S, p j * x i j := by
  simp_rw [revenue, mul_sum]
  exact sum_comm

namespace Market

variable (M : Market B G)

/-- `∑ⱼ R_j(p, x) ≤ B` for affordable allocations (`pᵀxᵢ ≤ bᵢ` for every buyer `i`). -/
private theorem sum_revenue_le_totalBudget {p : G → ℝ} {x : B → G → ℝ} (hx : x ∈ M.nonRivalAff p) :
    ∑ j, revenue p x j ≤ M.totalBudget := by
  rw [sum_revenue_eq, totalBudget]
  exact sum_le_sum fun i _ ↦ (hx i).2

omit [Fintype G] in
public theorem F_le (y : ℝ) : M.F y ≤ min M.totalBudget (Fintype.card B * y) := by
  refine le_min (sum_le_sum fun i _ ↦ min_le_left _ _) ?_
  simpa using sum_le_sum fun i (_ : i ∈ univ) ↦ min_le_right (M.budget i) y

omit [Fintype B] in
/-- A buyer spends at most `min(bᵢ, ∑_{j ∈ S} pⱼ)` on any set `S` of goods. -/
private theorem sum_mul_le_min {p : G → ℝ} (hp : 0 ≤ p) {i : B} {z : G → ℝ}
    (hz : z ∈ M.budgetSet i p) (S : Finset G)
    : ∑ j ∈ S, p j * z j ≤ min (M.budget i) (∑ j ∈ S, p j) := by
  obtain ⟨⟨hz0, hz1⟩, hzb⟩ := hz
  refine le_min ((sum_le_sum_of_subset_of_nonneg (subset_univ S) ?_).trans hzb) ?_
  · exact fun j _ _ ↦ mul_nonneg (hp j) (hz0 j)
  · exact sum_le_sum fun j _ ↦ mul_le_of_le_one_right (hp j) (hz1 j)

omit [Fintype B] in
/-- In the non-rivalrous setting, a buyer who doesn't buy some good
completely exhausts her budget. -/
public theorem spend_eq_budget_of_demand {p : G → ℝ} (hp : 0 ≤ p) {i : B} {z : G → ℝ}
    (hz : z ∈ M.demand i p) {j : G} (hj : z j < 1) :
    ∑ l, p l * z l = M.budget i := by
  -- Otherwise, buying a bit more of good `j` is affordable and strictly better.
  classical
  obtain ⟨⟨hzc, hzb⟩, hmax⟩ := hz
  have hpj : 0 ≤ p j := hp j
  by_contra hne
  have hlt : ∑ l, p l * z l < M.budget i := lt_of_le_of_ne hzb hne
  set ε := min (1 - z j) ((M.budget i - ∑ l, p l * z l) / (p j + 1)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  have hpε : p j * ε ≤ M.budget i - ∑ l, p l * z l := by
    have h1 : ε * (p j + 1) ≤ M.budget i - ∑ l, p l * z l :=
      (le_div_iff₀ (by linarith)).mp (min_le_right _ _)
    nlinarith
  have hmem : z + Pi.single j ε ∈ M.budgetSet i p := by
    refine ⟨add_single_mem_cube hzc hε0.le (min_le_left _ _), ?_⟩
    rw [sum_mul_add_single]; linarith
  have hlt' : M.util i z < M.util i (z + Pi.single j ε) :=
    M.util_strictMonoOn i hzc hmem.1 (lt_add_single z j hε0)
  have hle : M.util i (z + Pi.single j ε) ≤ M.util i z := hmax hmem
  linarith

omit [Fintype B] in
/-- In the non-rivalrous setting, each buyer spends `min(bᵢ, ∑ⱼ pⱼ)`: she either exhausts her
budget or buys every good completely. -/
public theorem spend_eq_min_of_demand {p : G → ℝ} (hp : 0 ≤ p) {i : B} {z : G → ℝ}
    (hz : z ∈ M.demand i p) : ∑ l, p l * z l = min (M.budget i) (∑ l, p l) := by
  by_cases h : ∃ j, z j < 1
  · obtain ⟨j, hj⟩ := h
    have heq := M.spend_eq_budget_of_demand hp hz hj
    have hle := M.sum_mul_le_min hp hz.1 univ
    rw [heq] at hle ⊢
    exact (min_eq_left (le_min_iff.mp hle).2).symm
  · push Not at h
    have h1 : z = 1 := funext fun j ↦ le_antisymm (hz.1.1.2 j) (h j)
    subst h1
    simpa using hz.1.2

/-- `thm:rev-vs-F` (non-rivalrous goods): `∑ⱼ R_j(p, x) = F(∑ⱼ pⱼ)`. -/
private theorem sum_revenue_of_mem_nonRivalDem {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.nonRivalDem p) : ∑ j, revenue p x j = M.F (∑ j, p j) := by
  rw [sum_revenue_eq, F]
  exact sum_congr rfl fun i _ ↦ M.spend_eq_min_of_demand hp (hx i)

/-- In the rivalrous setting, a Pareto optimal allocation can't have both a buyer with unspent
budget and a good that is not completely sold. -/
private theorem rivalDem_spent_or_sold {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.rivalDem p) :
    (∀ i, ∑ j, p j * x i j = M.budget i) ∨ (∀ j, ∑ i, x i j = 1) := by
  classical
  -- Otherwise, give buyer `i` (with unspent budget) a bit more of good `j` (which is not sold
  -- out); this Pareto dominates `x`.
  by_contra! h
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  obtain ⟨⟨hsupply, hbud⟩, hPO⟩ := hx
  have hpj : 0 ≤ p j := hp j
  have hi : ∑ l, p l * x i l < M.budget i := lt_of_le_of_ne (hbud i).2 hi
  have hj : ∑ k, x k j < 1 := lt_of_le_of_ne (hsupply j) hj
  set ε := min (1 - ∑ k, x k j) ((M.budget i - ∑ l, p l * x i l) / (p j + 1)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  have hεj : ε ≤ 1 - ∑ k, x k j := min_le_left _ _
  have hpε : p j * ε ≤ M.budget i - ∑ l, p l * x i l := by
    have h1 : ε * (p j + 1) ≤ M.budget i - ∑ l, p l * x i l :=
      (le_div_iff₀ (by linarith)).mp (min_le_right _ _)
    nlinarith
  have hxij : x i j ≤ ∑ k, x k j :=
    single_le_sum (fun k _ ↦ (hbud k).1.1 j) (mem_univ i)
  let y : B → G → ℝ := Function.update x i (x i + Pi.single j ε)
  have hyi : y i = x i + Pi.single j ε := by simp [y]
  have hyk : ∀ k, k ≠ i → y k = x k := fun k hk ↦ by simp [y, hk]
  have hmem_i : x i + Pi.single j ε ∈ M.budgetSet i p := by
    refine ⟨add_single_mem_cube (hbud i).1 hε0.le (by linarith), ?_⟩
    rw [sum_mul_add_single]; linarith [(hbud i).2]
  have hmem : y ∈ M.rivalAff p := by
    refine ⟨fun l ↦ ?_, fun k ↦ ?_⟩
    · have : ∑ k, y k l = ∑ k, x k l + (Pi.single j ε : G → ℝ) l := by
        rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ _ (mem_univ i), hyi,
          sum_congr rfl fun k hk ↦ by rw [hyk k (ne_of_mem_erase hk)]]
        simp only [Pi.add_apply]; ring
      rw [this]
      by_cases hl : l = j
      · subst hl; simp; linarith
      · simpa [hl] using hsupply l
    · by_cases hk : k = i
      · subst hk; rw [hyi]; exact hmem_i
      · rw [hyk k hk]; exact hbud k
  refine hPO y hmem ⟨fun k ↦ ?_, i, ?_⟩
  · by_cases hk : k = i
    · subst hk; rw [hyi]
      exact (M.util_strictMonoOn k (hbud k).1 hmem_i.1
        (lt_add_single _ j hε0)).le
    · rw [hyk k hk]
  · rw [hyi]
    exact M.util_strictMonoOn i (hbud i).1 hmem_i.1 (lt_add_single _ j hε0)

/-- Helper for `thm:rev-vs-F` (rivalrous goods):
`∑_{j ∈ S} R_j(p, x) ≤ min(B, ∑_{j ∈ S} pⱼ)` for every `x ∈ Aff^R(p)`. -/
private theorem sum_revenue_le_min {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.rivalAff p) (S : Finset G) :
    ∑ j ∈ S, revenue p x j ≤ min M.totalBudget (∑ j ∈ S, p j) := by
  refine le_min ?_ ?_
  · rw [sum_revenue_eq, totalBudget]
    exact sum_le_sum fun i _ ↦ (M.sum_mul_le_min hp (hx.2 i) S).trans (min_le_left _ _)
  · exact sum_le_sum fun j _ ↦ mul_le_of_le_one_right (hp j) (hx.1 j)

/-- `thm:rev-vs-F` (rivalrous goods): `∑ⱼ R_j(p, x) = min(B, ∑ⱼ pⱼ)`. -/
private theorem sum_revenue_of_mem_rivalDem {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.rivalDem p) : ∑ j, revenue p x j = min M.totalBudget (∑ j, p j) := by
  have hle := M.sum_revenue_le_min hp hx.1 univ
  rcases M.rivalDem_spent_or_sold hp hx with h | h
  · have : ∑ j, revenue p x j = M.totalBudget := by
      rw [sum_revenue_eq, totalBudget]; exact sum_congr rfl fun i _ ↦ h i
    rw [this] at hle ⊢
    exact (min_eq_left (le_min_iff.mp hle).2).symm
  · have : ∑ j, revenue p x j = ∑ j, p j :=
      sum_congr rfl fun j _ ↦ by simp [revenue, h j]
    rw [this] at hle ⊢
    exact (min_eq_right (le_min_iff.mp hle).1).symm

/-- The two definitions of the total revenue agree: for `p ≥ 0` and any `x ∈ Dem(p)`,
`∑ⱼ R_j(p, x) = R_all(p)`. In particular, `∑ⱼ R_j(p, x)` doesn't depend on `x`. -/
public theorem sum_revenue_eq_revenueAll {r : Rivalry} {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ M.dem r p) : ∑ j, revenue p x j = M.revenueAll r p := by
  cases r
  exacts [M.sum_revenue_of_mem_rivalDem hp hx, M.sum_revenue_of_mem_nonRivalDem hp hx]

/-- `R_all(p)` is non-decreasing in `∑ⱼ pⱼ`. -/
private theorem revenueAll_mono (r : Rivalry) {p q : G → ℝ} (hpq : ∑ j, p j ≤ ∑ j, q j) :
    M.revenueAll r p ≤ M.revenueAll r q := by
  cases r
  · exact min_le_min_left _ hpq
  · exact sum_le_sum fun i _ ↦ min_le_min_left _ hpq

end Market

/-- Under an allocation rule `A`, `∑ⱼ R^A_j(p) = R_all(p)` for every `p ≥ 0`. -/
public theorem Market.AllocRule.sum_revenue_eq_revenueAll {M : Market B G} {r : Rivalry}
    (A : M.AllocRule r) {p : G → ℝ} (hp : 0 ≤ p) :
    ∑ j, A.revenue p j = M.revenueAll r p :=
  M.sum_revenue_eq_revenueAll hp (A.mem_dem p hp)
