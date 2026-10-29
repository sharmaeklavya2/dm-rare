module

public import RareForMarkets.NashEq.Defs
import RareForMarkets.Prelims
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import RareForMarkets.Defs.Market
import Mathlib.Topology.Order.OrderClosed

/-! Helpers for `\cref{thm:nasheq-uncommon}`: two goods, small perturbations, and
the buyers' payments in a two-good market with unit budgets. -/

open Finset Filter Topology

variable {B : Type*} [Fintype B]

namespace TwoGoods

/-! ### Two goods -/

public theorem fin_two_cases {j k : Fin 2} (hjk : j ≠ k) : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) := by
  fin_cases j <;> fin_cases k <;> simp_all

public theorem exists_other (j : Fin 2) : ∃ k, j ≠ k := by
  fin_cases j
  exacts [⟨1, by decide⟩, ⟨0, by decide⟩]

public theorem add_eq_of_ne {j k : Fin 2} (hjk : j ≠ k) (f : Fin 2 → ℝ) :
    f j + f k = f 0 + f 1 := by
  rcases fin_two_cases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [rfl, add_comm _ _]

private theorem sum_fin_two_of_ne {j k : Fin 2} (hjk : j ≠ k) (f : Fin 2 → ℝ) :
    ∑ l, f l = f j + f k := by
  rw [Fin.sum_univ_two, add_eq_of_ne hjk]

public theorem update_nonneg {p : Fin 2 → ℝ} (hp : 0 ≤ p) (j : Fin 2) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Function.update p j s := fun l ↦ by
  by_cases hl : l = j
  · subst hl; simpa using hs
  · simpa [hl] using hp l

/-- Finitely many conditions that hold eventually near `0` hold simultaneously
at some `δ ∈ (0, a)`. (This is the paper's "choose `δ` small enough".) -/
public theorem exists_pos_forall {ι : Type*} [Finite ι] {a : ℝ} (ha : 0 < a)
    {P : ι → ℝ → Prop} (hP : ∀ i, ∀ᶠ δ in 𝓝 0, P i δ) : ∃ δ, 0 < δ ∧ δ < a ∧ ∀ i, P i δ := by
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, P i δ :=
    (eventually_all.2 hP).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδa⟩ := (h1.and (Ioo_mem_nhdsGT ha)).exists
  exact ⟨δ, hδa.1, hδa.2, hδ⟩

/-- `∑ᵢ fᵢ + δ ≤ ∑ᵢ gᵢ` if `f ≤ g` pointwise and `f i₀ + δ ≤ g i₀`. -/
public theorem sum_add_le_sum {f g : B → ℝ} (h : ∀ i, f i ≤ g i) (i₀ : B) {δ : ℝ}
    (h₀ : f i₀ + δ ≤ g i₀) : ∑ i, f i + δ ≤ ∑ i, g i := by
  have : g i₀ - f i₀ ≤ ∑ i, (g i - f i) :=
    single_le_sum (f := fun i ↦ g i - f i) (fun i _ ↦ sub_nonneg.mpr (h i)) (mem_univ i₀)
  rw [sum_sub_distrib] at this
  linarith

public theorem revenue_eq (q : Fin 2 → ℝ) (x : B → Fin 2 → ℝ) (j : Fin 2) :
    revenue q x j = ∑ i, q j * x i j :=
  mul_sum _ _ _

/-! ### Payments in a two-good market with unit budgets

Buyer `i` strictly prefers good `j` over good `k` at prices `q` if `q_j / u_{i,j} < q_k / u_{i,k}`,
written here as `q_j u_{i,k} < q_k u_{i,j}`. -/

/-- The market with unit budgets and linear utilities `w`. -/
@[expose] public abbrev unitMarket
    (w : B → Fin 2 → ℝ) (hw0 : ∀ i j, 0 < w i j) : Market B (Fin 2) :=
  Market.ofLinear (fun _ ↦ 1) w (fun _ ↦ one_pos) hw0

section Payments

omit [Fintype B]

variable {w : B → Fin 2 → ℝ} {hw0 : ∀ i j, 0 < w i j} {q z : Fin 2 → ℝ} {i : B} {j k : Fin 2}

/-- Each buyer spends `min(1, q_j + q_k)`. -/
public theorem spend_two (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q) (hjk : j ≠ k) :
    q j * z j + q k * z k = min 1 (q j + q k) := by
  have h := (unitMarket w hw0).spend_eq_min_of_demand hq hz
  rwa [sum_fin_two_of_ne hjk (fun l ↦ q l * z l), sum_fin_two_of_ne hjk q] at h

public theorem pay_le (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q) (hjk : j ≠ k) :
    q j * z j ≤ min 1 (q j) := by
  have := spend_two hq hz hjk
  have := mul_nonneg (hq k) (hz.1.1.1 k)
  exact le_min (by linarith [min_le_left (1 : ℝ) (q j + q k)])
    (mul_le_of_le_one_right (hq j) (hz.1.1.2 j))

public theorem le_pay (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q) (hjk : j ≠ k) :
    min 1 (q j + q k) - q k ≤ q j * z j := by
  have := spend_two hq hz hjk
  have := mul_le_of_le_one_right (hq k) (hz.1.1.2 k)
  linarith

/-- A buyer who strictly prefers good `j` pays `min(1, q_j)` to seller `j`. -/
public theorem pay_of_prefers (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q)
    (hjk : j ≠ k) (h : q j * w i k < q k * w i j) : q j * z j = min 1 (q j) := by
  refine le_antisymm (pay_le hq hz hjk) ?_
  have hb : q j / w i j < q k / w i k := by
    rw [div_lt_div_iff₀ (hw0 i j) (hw0 i k)]; linarith
  rcases (unitMarket w hw0).bangPerBuck rfl (hw0 i) hq hz hb with h1 | h0
  · rw [h1, mul_one]; exact min_le_right _ _
  · have := spend_two hq hz hjk
    rw [h0, mul_zero, add_zero] at this
    rw [this]
    exact min_le_min_left _ (le_add_of_nonneg_right (hq k))

/-- A buyer who strictly prefers good `k` pays `min(1, q_j + q_k) - min(1, q_k)` to seller `j`. -/
public theorem pay_of_prefers_other (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q)
    (hjk : j ≠ k) (h : q k * w i j < q j * w i k) :
    q j * z j = min 1 (q j + q k) - min 1 (q k) := by
  have := spend_two hq hz hjk
  have := pay_of_prefers hq hz hjk.symm h
  linarith

/-- If the full bundle is affordable, each buyer pays `q_j` to seller `j`. -/
public theorem pay_of_sum_le (hq : 0 ≤ q) (hz : z ∈ (unitMarket w hw0).demand i q)
    (hjk : j ≠ k) (h : q j + q k ≤ 1) : q j * z j = q j := by
  have h1 := spend_two hq hz hjk
  have h2 := (pay_le hq hz hjk).trans (min_le_right _ _)
  have h3 := (pay_le hq hz hjk.symm).trans (min_le_right _ _)
  rw [min_eq_right h] at h1
  linarith

end Payments

end TwoGoods
