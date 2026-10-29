module

public import RareForMarkets.Defs.Misc
public import RareForMarkets.Exist.Defs
public import RareForMarkets.Exist.Accounting
public import RareForMarkets.Defs.Market
import RareForMarkets.Exist.InnerKKM
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.ProjIcc

/-!
# RARE for continuous allocation rules

`\cref{sec:exist:kkm,sec:exist:overpricing,sec:exist:continuous}`
-/

open Set Finset Filter Topology

variable {B G : Type*} [Fintype B] [Fintype G]

public theorem isClosed_scaledSimplex (β : ℝ) : IsClosed (scaledSimplex G β) := by
  have h1 : IsClosed {x : G → ℝ | 0 ≤ x} := isClosed_le continuous_const continuous_id
  have h2 : IsClosed {x : G → ℝ | ∑ j, x j = β} :=
    isClosed_eq (continuous_finsetSum _ fun j _ ↦ continuous_apply j) continuous_const
  exact h1.inter h2

public theorem le_of_mem_scaledSimplex {β : ℝ} {p : G → ℝ} (hp : p ∈ scaledSimplex G β) (j : G) :
    p j ≤ β :=
  hp.2 ▸ single_le_sum (fun k _ ↦ hp.1 k) (mem_univ j)

namespace Market.AllocRule

variable [Nonempty B] {M : Market B G} {r : Rivalry} (A : M.AllocRule r)

local notation "ν" => Market.nu (B := B) r
local notation "β" => Market.beta M r
local notation "κ" => Market.kappa M r

/-! ### Accounting for allocation rules -/

omit [Nonempty B] in
public theorem revenue_nonneg {q : G → ℝ} (hq : 0 ≤ q) (k : G) : 0 ≤ A.revenue q k :=
  M.revenue_nonneg_of_mem_dem hq (A.mem_dem q hq) k

omit [Nonempty B] in
public theorem revenue_le_nu {q : G → ℝ} (hq : 0 ≤ q) (k : G) : A.revenue q k ≤ ν * q k :=
  M.revenue_le_nu hq (A.mem_dem q hq) k

omit [Nonempty B] in
public theorem revenue_le_totalBudget {q : G → ℝ} (hq : 0 ≤ q) (k : G) :
    A.revenue q k ≤ M.totalBudget :=
  M.revenue_le_totalBudget hq (A.mem_dem q hq) k

public theorem revenue_eq_of_sum_le {q : G → ℝ} (hq : 0 ≤ q) (hs : ∑ j, q j ≤ β) (k : G) :
    A.revenue q k = ν * q k :=
  M.revenue_eq_of_sum_le hq (A.mem_dem q hq) hs k

omit [Nonempty B] in
private theorem sum_revenue_le {q : G → ℝ} (hq : 0 ≤ q) : ∑ l, A.revenue q l ≤ M.totalBudget :=
  (A.sum_revenue_eq_revenueAll hq).trans_le (M.revenueAll_le r q)

private theorem nu_mul_beta_le_sum_revenue {q : G → ℝ} (hq : 0 ≤ q) (hs : β ≤ ∑ j, q j) :
    ν * β ≤ ∑ l, A.revenue q l :=
  (A.sum_revenue_eq_revenueAll hq) ▸ M.nu_mul_beta_le_revenueAll hs

/-- Revenues are proportional to prices: `β R_k(q) = p_k R_all(q)` for every `k`. -/
private def PropRev (p q : G → ℝ) : Prop :=
  ∀ k, β * A.revenue q k = p k * ∑ l, A.revenue q l

private theorem propRev_self {p : G → ℝ} (hp : p ∈ scaledSimplex G β) : A.PropRev p p := by
  intro k
  have h := A.revenue_eq_of_sum_le hp.1 hp.2.le
  simp only [h, ← mul_sum, hp.2]
  ring

/-! ### `\cref{thm:prop-box}` -/

/-- `\label{thm:prop-box}` -/
private theorem prop_box (hA : ContinuousOn A (Ici 0)) {p : G → ℝ} (hp : p ∈ scaledSimplex G β)
    (z : G → ℝ) (hz : ∀ j, 0 < p j → p j < z j) (hz0 : ∀ j, p j = 0 → z j = 0) :
    ∃ q, p ≤ q ∧ q ≤ z ∧ (∃ i, 0 < p i ∧ q i = z i) ∧ A.PropRev p q := by
  classical
  have hp0 : ∀ j, 0 ≤ p j := hp.1
  let S := univ.filter (0 < p ·)
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : ∑ j, p j ≤ 0 := sum_nonpos fun j _ ↦ not_lt.mp (h (mem_univ j))
    linarith [hp.2, M.beta_pos r]
  let f : G → (G → ℝ) → ℝ := fun k q ↦ β * A.revenue q k - p k * ∑ l, A.revenue q l
  have hmemS : ∀ j, j ∈ S ↔ 0 < p j := fun j ↦ by simp [S]
  -- Facts about points of `U`.
  have hU : ∀ x ∈ boxTop S p z 0, p ≤ x := by
    intro x hx j
    by_cases hj : j ∈ S
    · exact (hx.1 j hj).1
    · rw [hx.2.1 j hj]
      exact le_of_not_gt fun h ↦ hj ((hmemS j).mpr h)
  have hU0 : ∀ x ∈ boxTop S p z 0, 0 ≤ x := fun x hx ↦ hp.1.trans (hU x hx)
  have hsum0 : ∀ x ∈ boxTop S p z 0, ∑ k ∈ S, f k x = 0 := by
    intro x hx
    have h1 : ∑ k ∈ S, p k = β := by
      rw [sum_filter_of_ne fun k _ hk ↦ lt_of_le_of_ne (hp0 k) (Ne.symm hk), hp.2]
    have h2 : ∑ k ∈ S, A.revenue x k = ∑ l, A.revenue x l := by
      refine sum_filter_of_ne fun k _ hk ↦ ?_
      by_contra hkS
      have : x k = 0 := hx.2.1 k ((hmemS k).not.mpr hkS)
      exact hk (by simp [AllocRule.revenue, _root_.revenue, this])
    simp only [f, sum_sub_distrib, ← mul_sum, ← sum_mul, h1, h2, sub_self]
  obtain ⟨q, hq, hfq⟩ := inner_kkm S hS p z 0 (fun j hj ↦ hz j ((hmemS j).mp hj)) f
    (fun k _ ↦ by
      have hc := fun l ↦ (A.continuousOn_revenue hA l).mono fun x hx ↦ hU0 x hx
      exact ((continuousOn_const.mul (hc k)).sub
        (continuousOn_const.mul (continuousOn_finsetSum _ fun l _ ↦ hc l))))
    (fun x hx ↦ (hsum0 x hx).ge)
    (by
      intro x hx j hj hxj
      have hx0 := hU0 x hx
      have h1 : A.revenue x j ≤ ν * p j := hxj ▸ A.revenue_le_nu hx0 j
      have h2 : ν * β ≤ ∑ l, A.revenue x l :=
        A.nu_mul_beta_le_sum_revenue hx0 (hp.2 ▸ sum_le_sum fun k _ ↦ hU x hx k)
      have hb := (M.beta_pos r).le
      simp only [f, sub_nonpos]
      calc β * A.revenue x j ≤ β * (ν * p j) := mul_le_mul_of_nonneg_left h1 hb
        _ = p j * (ν * β) := by ring
        _ ≤ p j * ∑ l, A.revenue x l := mul_le_mul_of_nonneg_left h2 (hp0 j))
  refine ⟨q, hU q hq, fun j ↦ ?_, ?_, fun k ↦ ?_⟩
  · by_cases hj : j ∈ S
    · exact (hq.1 j hj).2
    · rw [hq.2.1 j hj, hz0 j (le_antisymm (not_lt.mp ((hmemS j).not.mp hj)) (hp0 j))]
      rfl
  · obtain ⟨i, hi, hqi⟩ := hq.2.2
    exact ⟨i, (hmemS i).mp hi, hqi⟩
  · by_cases hk : k ∈ S
    · have h := (sum_eq_zero_iff_of_nonneg hfq).mp (hsum0 q hq) k hk
      simp only [f] at h
      linarith
    · have hqk : q k = 0 := hq.2.1 k hk
      have hpk : p k = 0 := le_antisymm (not_lt.mp ((hmemS k).not.mp hk)) (hp0 k)
      simp [AllocRule.revenue, _root_.revenue, hqk, hpk]

/-! ### `\cref{thm:large-dev-deter}` -/

/-- `\label{thm:large-dev-deter}`. (When `j` is the only seller, the bound on `j`'s revenue
only holds with the factor `κ`.) -/
private theorem large_dev_deter (hA : ContinuousOn A (Ici 0)) {σ ρ L : G → ℝ}
    (hover : ∀ j, M.IsOverpricing r j (σ j) (ρ j) (L j))
    {p : G → ℝ} (hp : p ∈ scaledSimplex G β) {j : G} (hρ : 0 < ρ j)
    (hpj : β * ρ j ≤ p j * M.totalBudget) {qj : ℝ} (hqj : L j < qj) :
    ∃ q : G → ℝ, q j = qj ∧ (∀ k ≠ j, q k ∈ Icc (p k) M.totalBudget) ∧
      A.revenue q j ≤ p j * κ * ν ∧ ∀ k ≠ j, ν * p k ≤ A.revenue q k := by
  classical
  have hp0 : ∀ k, 0 ≤ p k := hp.1
  have hB := M.totalBudget_pos (B := B)
  have hβ := M.beta_pos r
  have hκ := M.kappa_pos r
  have hν := Market.nu_pos (B := B) r
  have hκνβ := M.kappa_mul_nu_mul_beta r
  have hβB := M.beta_le_totalBudget r
  have hLB : ∀ k, M.totalBudget ≤ L k := fun k ↦ (le_max_left _ _).trans (hover k).max_le
  have hpj0 : 0 < p j := by
    by_contra h
    have : p j * M.totalBudget ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hB.le
    nlinarith
  -- `ρⱼ ≤ κνpⱼ`
  have hρκ : ρ j ≤ p j * κ * ν := by
    have : β * ρ j ≤ β * (p j * κ * ν) := by rw [← hκνβ] at hpj; linarith
    exact le_of_mul_le_mul_left this hβ
  let S := univ.erase j
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- `j` is the only seller.
    have hk : ∀ k, k = j := fun k ↦ by
      by_contra h
      have : k ∈ S := mem_erase.mpr ⟨h, mem_univ k⟩
      rw [hS] at this
      simp at this
    have hpjβ : p j = β := by
      rw [← hp.2, sum_eq_single j (fun k _ hkj ↦ absurd (hk k) hkj) (by simp)]
    refine ⟨Function.update p j qj, by simp, fun k hkj ↦ absurd (hk k) hkj, ?_,
      fun k hkj ↦ absurd (hk k) hkj⟩
    have hq0 : 0 ≤ Function.update p j qj := by
      intro k
      rw [hk k]
      simpa using ((hB.trans_le (hLB j)).trans hqj).le
    calc A.revenue _ j ≤ M.totalBudget := A.revenue_le_totalBudget hq0 j
      _ = p j * κ * ν := by rw [hpjβ, ← hκνβ]; ring
  have hpk : ∀ k ∈ S, p k < M.totalBudget := by
    intro k hk
    have h1 : p k + p j ≤ β := by
      rw [← hp.2, ← sum_erase_add _ _ (mem_univ j)]
      exact add_le_add_left (single_le_sum (fun l _ ↦ hp0 l) hk) _
    linarith
  let f : G → (G → ℝ) → ℝ := fun k q ↦ A.revenue q k - ν * p k
  -- Facts about points of `U`.
  have hU : ∀ x ∈ boxTop S p (fun _ ↦ M.totalBudget) (fun _ ↦ qj), p ≤ x ∧ x j = qj := by
    intro x hx
    have hxj : x j = qj := hx.2.1 j (by simp [S])
    refine ⟨fun k ↦ ?_, hxj⟩
    by_cases hk : k = j
    · subst hk
      rw [hxj]
      exact (le_of_mem_scaledSimplex hp k).trans (hβB.trans ((hLB k).trans hqj.le))
    · exact (hx.1 k (mem_erase.mpr ⟨hk, mem_univ k⟩)).1
  have hRj : ∀ x ∈ boxTop S p (fun _ ↦ M.totalBudget) (fun _ ↦ qj),
      2 * A.revenue x j ≤ ν * p j := by
    intro x hx
    have hx0 : 0 ≤ x := hp.1.trans (hU x hx).1
    have h := (hover j).revenue_le x hx0 (A x) (A.mem_dem x hx0) ((hU x hx).2 ▸ hqj)
      (fun k hk ↦ (hx.1 k (mem_erase.mpr ⟨hk, mem_univ k⟩)).2)
      (by obtain ⟨i, hi, hxi⟩ := hx.2.2; exact ⟨i, ne_of_mem_erase hi, hxi⟩)
    have : κ * (2 * A.revenue x j) ≤ κ * (ν * p j) := by
      change 2 * κ * _root_.revenue x (A x) j ≤ ρ j at h
      calc κ * (2 * A.revenue x j) = 2 * κ * _root_.revenue x (A x) j := by
            simp only [AllocRule.revenue]; ring
        _ ≤ p j * κ * ν := h.trans hρκ
        _ = κ * (ν * p j) := by ring
    exact le_of_mul_le_mul_left this hκ
  obtain ⟨q, hq, hfq⟩ := inner_kkm S hS p (fun _ ↦ M.totalBudget) (fun _ ↦ qj) hpk f
    (fun k _ ↦ ((A.continuousOn_revenue hA k).mono fun x hx ↦
      hp.1.trans (hU x hx).1).sub continuousOn_const)
    (by
      intro x hx
      have hx0 : 0 ≤ x := hp.1.trans (hU x hx).1
      have h1 := A.nu_mul_beta_le_sum_revenue hx0 (hp.2 ▸ sum_le_sum fun k _ ↦ (hU x hx).1 k)
      have h2 := hRj x hx
      have h3 : 0 ≤ A.revenue x j := A.revenue_nonneg hx0 j
      have h4 : ∑ k ∈ S, f k x = (∑ l, A.revenue x l - A.revenue x j) - ν * (β - p j) := by
        simp only [f, sum_sub_distrib, ← mul_sum, S, ← hp.2]
        rw [← sum_erase_add _ _ (mem_univ j), ← sum_erase_add univ p (mem_univ j)]
        ring
      rw [h4]
      nlinarith)
    (fun x hx k _ hxk ↦ by
      have hx0 : 0 ≤ x := hp.1.trans (hU x hx).1
      simpa [f, hxk] using A.revenue_le_nu hx0 k)
  refine ⟨q, (hU q hq).2, fun k hk ↦ hq.1 k (mem_erase.mpr ⟨hk, mem_univ k⟩), ?_,
    fun k hk ↦ by simpa [f] using hfq k (mem_erase.mpr ⟨hk, mem_univ k⟩)⟩
  have h2 := hRj q hq
  have : ν * p j ≤ p j * κ * ν := by nlinarith [M.one_le_kappa r]
  nlinarith [A.revenue_nonneg (hp.1.trans (hU q hq).1) j]

/-! ### The outer KKM sets -/

/-- The set `C_j` of prices at which every bounded deviation by seller `j` can be met with a
revenue-proportion-restoring response. -/
private def outerSet [DecidableEq G] (L : G → ℝ) (j : G) : Set (G → ℝ) :=
  {p | p ∈ scaledSimplex G β ∧ ∀ qj ∈ Icc (p j) (L j), ∃ q : G → ℝ, q j = qj ∧
    (∀ k ≠ j, q k ∈ Icc (p k) (L k)) ∧ A.PropRev p q}

omit [Nonempty B] in
private theorem isClosed_outerSet [DecidableEq G] (hA : ContinuousOn A (Ici 0)) {L : G → ℝ}
    (hL : ∀ k, β ≤ L k) (j : G) : IsClosed (A.outerSet L j) := by
  refine IsSeqClosed.isClosed fun {ps p} hps hlim ↦ ?_
  have hpS : p ∈ scaledSimplex G β :=
    (isClosed_scaledSimplex β).mem_of_tendsto hlim (Eventually.of_forall fun n ↦ (hps n).1)
  refine ⟨hpS, fun qj hqj ↦ ?_⟩
  have hLn : ∀ n, ps n j ≤ L j := fun n ↦ (le_of_mem_scaledSimplex (hps n).1 j).trans (hL j)
  have hex : ∀ n, ∃ q : G → ℝ, q j = max qj (ps n j) ∧
      (∀ k ≠ j, q k ∈ Icc (ps n k) (L k)) ∧ A.PropRev (ps n) q :=
    fun n ↦ (hps n).2 _ ⟨le_max_right _ _, max_le hqj.2 (hLn n)⟩
  choose qs hqsj hqsk hqsr using hex
  have hqj0 : 0 ≤ qj := (hpS.1 j).trans hqj.1
  have hqs_mem : ∀ n, qs n ∈ Icc (0 : G → ℝ) L := by
    intro n
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩ <;> by_cases hk : k = j
    · subst hk; rw [hqsj]; exact hqj0.trans (le_max_left _ _)
    · exact ((hps n).1.1 k).trans (hqsk n k hk).1
    · subst hk; rw [hqsj]; exact max_le hqj.2 (hLn n)
    · exact (hqsk n k hk).2
  have hqs0 : ∀ n, 0 ≤ qs n := fun n ↦ (hqs_mem n).1
  obtain ⟨q, -, φ, hφ, hq⟩ := isCompact_Icc.tendsto_subseq hqs_mem
  have hpφ : Tendsto (ps ∘ φ) atTop (𝓝 p) := hlim.comp hφ.tendsto_atTop
  have hcoord : ∀ k, Tendsto (fun n ↦ qs (φ n) k) atTop (𝓝 (q k)) :=
    fun k ↦ (continuous_apply k).continuousAt.tendsto.comp hq
  have hpcoord : ∀ k, Tendsto (fun n ↦ ps (φ n) k) atTop (𝓝 (p k)) :=
    fun k ↦ (continuous_apply k).continuousAt.tendsto.comp hpφ
  have hqj' : q j = qj := by
    have h1 : Tendsto (fun n ↦ qs (φ n) j) atTop (𝓝 (max qj (p j))) := by
      simp only [hqsj]
      exact ((continuous_const.max continuous_id).tendsto _).comp (hpcoord j)
    rw [tendsto_nhds_unique (hcoord j) h1, max_eq_left hqj.1]
  have hqk : ∀ k ≠ j, q k ∈ Icc (p k) (L k) := fun k hk ↦
    ⟨le_of_tendsto_of_tendsto' (hpcoord k) (hcoord k) fun n ↦ (hqsk (φ n) k hk).1,
      le_of_tendsto' (hcoord k) fun n ↦ (hqsk (φ n) k hk).2⟩
  have hq0 : 0 ≤ q := by
    intro k
    by_cases hk : k = j
    · rw [hk, hqj']; exact hqj0
    · exact (hpS.1 k).trans (hqk k hk).1
  -- Revenues converge.
  have hrev : ∀ k, Tendsto (fun n ↦ A.revenue (qs (φ n)) k) atTop (𝓝 (A.revenue q k)) := by
    intro k
    have hc := (A.continuousOn_revenue hA k) q hq0
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall
      fun n ↦ hqs0 (φ n)⟩)
  refine ⟨q, hqj', hqk, fun k ↦ tendsto_nhds_unique ((hrev k).const_mul _) ?_⟩
  simp only [fun n ↦ hqsr (φ n) k]
  exact (hpcoord k).mul (tendsto_finsetSum _ fun l _ ↦ hrev l)

/-! ### `\cref{thm:rare-exists-continuous-2}` -/

/-- `\label{thm:rare-exists-continuous-2}` -/
private theorem exists_mem_outerSet [DecidableEq G] [Nonempty G] (hA : ContinuousOn A (Ici 0))
    {L : G → ℝ} (hL : ∀ k, β ≤ L k) : ∃ p, ∀ j, p ∈ A.outerSet L j := by
  classical
  have hβ := M.beta_pos r
  let F : G → Set (G → ℝ) := fun i ↦ (fun θ ↦ β • θ) ⁻¹' A.outerSet L i
  have hF : ∀ i, IsClosed (F i) := fun i ↦
    (A.isClosed_outerSet hA hL i).preimage (continuous_const_smul _)
  obtain ⟨θ, -, hθ⟩ := kkm_of_support F hF (by
    intro θ hθ
    let p : G → ℝ := β • θ
    have hpS : p ∈ scaledSimplex G β :=
      ⟨fun k ↦ mul_nonneg hβ.le (hθ.1 k), by simp [p, ← mul_sum, hθ.2]⟩
    have hpos : ∀ i, 0 < θ i ↔ 0 < p i := fun i ↦ by simp [p, hβ]
    by_contra! h
    -- For each `i` in the support, a deviation `zᵢ` that can't be met.
    have hz : ∀ i, ∃ zi : ℝ, (0 < p i → zi ∈ Icc (p i) (L i) ∧ ∀ q : G → ℝ, q i = zi →
        (∀ k ≠ i, q k ∈ Icc (p k) (L k)) → ¬ A.PropRev p q) ∧ (p i = 0 → zi = 0) := by
      intro i
      by_cases hi : 0 < p i
      · have : p ∉ A.outerSet L i := h i ((hpos i).mpr hi)
        simp only [outerSet, Set.mem_setOf_eq, not_and, not_forall, not_exists] at this
        obtain ⟨zi, hzi, hzi'⟩ := this hpS
        exact ⟨zi, fun _ ↦ ⟨hzi, fun q hq hk hr ↦ hzi' q hq hk hr⟩,
          fun h0 ↦ absurd (h0 ▸ hi) (lt_irrefl 0)⟩
      · exact ⟨0, fun h' ↦ absurd h' hi, fun _ ↦ rfl⟩
    choose z hz using hz
    have hzp : ∀ i, 0 < p i → p i < z i := by
      intro i hi
      refine lt_of_le_of_ne ((hz i).1 hi).1.1 fun heq ↦ ?_
      refine ((hz i).1 hi).2 p heq (fun k _ ↦ ⟨le_rfl, ?_⟩) (A.propRev_self hpS)
      exact (le_of_mem_scaledSimplex hpS k).trans (hL k)
    obtain ⟨q, hpq, hqz, ⟨i, hi, hqi⟩, hr⟩ := A.prop_box hA hpS z hzp (fun i ↦ (hz i).2)
    refine ((hz i).1 hi).2 q hqi (fun k _ ↦ ⟨hpq k, (hqz k).trans ?_⟩) hr
    by_cases hk : 0 < p k
    · exact ((hz k).1 hk).1.2
    · rw [(hz k).2 (le_antisymm (not_lt.mp hk) (hpS.1 k))]
      exact hβ.le.trans (hL k))
  exact ⟨β • θ, hθ⟩

/-! ### `\cref{thm:rare-exists-continuous}` -/

/-- `\label{thm:rare-exists-continuous}` -/
public theorem rare_exists_continuous_aux [DecidableEq G] [Nonempty G] (hA : ContinuousOn A (Ici 0))
    (σ ρ L : G → ℝ) (hsec : ∀ j, M.IsSecurity r j (σ j) (ρ j))
    (hover : ∀ j, M.IsOverpricing r j (σ j) (ρ j) (L j)) :
    ∃ p ∈ scaledSimplex G β, ∀ j,
      (A.revenue p j = ν * p j ∧ β * ρ j ≤ p j * M.totalBudget) ∧
      ∀ qj, 0 ≤ qj → ∃ q : G → ℝ, q j = qj ∧
        (∀ k ≠ j, q k ∈ Icc (p k) (L k)) ∧
        A.revenue q j ≤ p j * κ * ν ∧
        ∀ k ≠ j, ν * p k ≤ A.revenue q k ∧ A.revenue (Function.update p j qj) k ≤ ν * p k := by
  have hβ := M.beta_pos r
  have hν := Market.nu_pos (B := B) r
  have hκ1 := M.one_le_kappa r
  have hκνβ := M.kappa_mul_nu_mul_beta r
  have hBL : ∀ k, M.totalBudget ≤ L k := fun k ↦ (le_max_left _ _).trans (hover k).max_le
  have hσL : ∀ k, σ k ≤ L k := fun k ↦ (le_max_right _ _).trans (hover k).max_le
  have hL : ∀ k, β ≤ L k := fun k ↦ (M.beta_le_totalBudget r).trans (hBL k)
  obtain ⟨p, hp⟩ := A.exists_mem_outerSet hA hL
  have hpS : p ∈ scaledSimplex G β := (hp (Classical.arbitrary G)).1
  have hp0 : 0 ≤ p := hpS.1
  have hpL : ∀ k, p k ≤ L k := fun k ↦ (le_of_mem_scaledSimplex hpS k).trans (hL k)
  have hrevp := A.revenue_eq_of_sum_le hp0 hpS.2.le
  -- Responses from the outer KKM sets.
  have hmid : ∀ j, ∀ qj ∈ Icc (p j) (L j), ∃ q : G → ℝ, q j = qj ∧
      (∀ k ≠ j, q k ∈ Icc (p k) (L k)) ∧ 0 ≤ q ∧ p ≤ q ∧
      β * A.revenue q j ≤ p j * M.totalBudget ∧ ∀ k, ν * p k ≤ A.revenue q k := by
    intro j qj hqj
    obtain ⟨q, hqj', hqk, hr⟩ := (hp j).2 qj hqj
    have hpq : p ≤ q := fun k ↦ by
      by_cases hk : k = j
      · rw [hk, hqj']; exact hqj.1
      · exact (hqk k hk).1
    have hq0 : 0 ≤ q := hp0.trans hpq
    refine ⟨q, hqj', hqk, hq0, hpq, ?_, fun k ↦ ?_⟩
    · rw [hr j]; exact mul_le_mul_of_nonneg_left (A.sum_revenue_le hq0) (hp0 j)
    · have h1 := A.nu_mul_beta_le_sum_revenue hq0 (hpS.2 ▸ sum_le_sum fun l _ ↦ hpq l)
      have : β * (ν * p k) ≤ β * A.revenue q k := by
        rw [hr k]
        calc β * (ν * p k) = p k * (ν * β) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hp0 k)
      exact le_of_mul_le_mul_left this hβ
  -- The lower bound `pⱼ ≥ βρⱼ/B`.
  have hlow : ∀ j, β * ρ j ≤ p j * M.totalBudget := by
    intro j
    by_cases hσ : p j ≤ σ j
    · obtain ⟨q, hqj, -, hq0, -, hRj, -⟩ := hmid j (σ j) ⟨hσ, hσL j⟩
      have h := (hsec j).le_revenue q hq0 (A q) (by
        rw [← hqj, Function.update_eq_self]; exact A.mem_dem q hq0)
      rw [← hqj, Function.update_eq_self] at h
      calc β * ρ j ≤ β * A.revenue q j := mul_le_mul_of_nonneg_left h hβ.le
        _ ≤ _ := hRj
    · push Not at hσ
      have hq0 : 0 ≤ Function.update p j (σ j) := by
        intro k
        by_cases hk : k = j
        · subst hk; simpa using (hsec k).σ_pos.le
        · simpa [hk] using hp0 k
      have h := (hsec j).le_revenue p hp0 _ (A.mem_dem _ hq0)
      have h' := A.revenue_le_nu hq0 j
      simp only [Function.update_self] at h'
      have hρ : ρ j ≤ ν * p j :=
        h.trans (h'.trans (mul_le_mul_of_nonneg_left hσ.le hν.le))
      calc β * ρ j ≤ β * (ν * p j) := mul_le_mul_of_nonneg_left hρ hβ.le
        _ = p j * (ν * β) := by ring
        _ ≤ p j * M.totalBudget := mul_le_mul_of_nonneg_left (M.nu_mul_beta_le r) (hp0 j)
  refine ⟨p, hpS, fun j ↦ ⟨⟨hrevp j, hlow j⟩, fun qj hqj0 ↦ ?_⟩⟩
  -- The responses.
  have hupd0 : 0 ≤ Function.update p j qj := by
    intro k
    by_cases hk : k = j
    · subst hk; simpa using hqj0
    · simpa [hk] using hp0 k
  have hupd : ∀ k ≠ j, A.revenue (Function.update p j qj) k ≤ ν * p k := fun k hk ↦ by
    simpa [hk] using A.revenue_le_nu hupd0 k
  rcases lt_or_ge qj (p j) with hlt | hge
  · -- Small deviations: keep the other prices.
    refine ⟨Function.update p j qj, by simp, fun k hk ↦ by simp [hk, hpL k], ?_,
      fun k hk ↦ ⟨?_, hupd k hk⟩⟩
    · have hs : ∑ k, Function.update p j qj k ≤ β := hpS.2 ▸ sum_le_sum fun k _ ↦ by
        by_cases hk : k = j
        · subst hk; simpa using hlt.le
        · simp [hk]
      rw [A.revenue_eq_of_sum_le hupd0 hs j]
      simp only [Function.update_self]
      calc ν * qj ≤ ν * p j := mul_le_mul_of_nonneg_left hlt.le hν.le
        _ = 1 * (p j * ν) := by ring
        _ ≤ κ * (p j * ν) := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg (hp0 j) hν.le)
        _ = p j * κ * ν := by ring
    · have hs : ∑ k, Function.update p j qj k ≤ β := hpS.2 ▸ sum_le_sum fun k _ ↦ by
        by_cases hk : k = j
        · subst hk; simpa using hlt.le
        · simp [hk]
      rw [A.revenue_eq_of_sum_le hupd0 hs k]
      simp [hk]
  rcases le_or_gt qj (L j) with hle | hgt
  · -- Medium deviations: restore revenue proportions.
    obtain ⟨q, hqj, hqk, -, -, hRj, hRk⟩ := hmid j qj ⟨hge, hle⟩
    refine ⟨q, hqj, hqk, ?_, fun k hk ↦ ⟨hRk k, hupd k hk⟩⟩
    have : β * A.revenue q j ≤ β * (p j * κ * ν) := by
      rw [← hκνβ] at hRj; linarith
    exact le_of_mul_le_mul_left this hβ
  · -- Large deviations: `\cref{thm:large-dev-deter}`.
    obtain ⟨q, hqj, hqk, hRj, hRk⟩ :=
      A.large_dev_deter hA hover hpS (hsec j).ρ_pos (hlow j) hgt
    exact ⟨q, hqj, fun k hk ↦ ⟨(hqk k hk).1, (hqk k hk).2.trans (hBL k)⟩, hRj,
      fun k hk ↦ ⟨hRk k hk, hupd k hk⟩⟩

end Market.AllocRule
