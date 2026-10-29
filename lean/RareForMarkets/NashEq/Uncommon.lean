module

public import RareForMarkets.NashEq.TwoGoods
public import RareForMarkets.Defs.Market
public import RareForMarkets.NashEq.Defs

/-! Proof of `\cref{thm:nasheq-uncommon}`. -/

open Finset Filter Topology

variable {B : Type*} [Fintype B]

namespace TwoGoods

/-! ### Nash equilibria -/

section NashEq

variable {w : B → Fin 2 → ℝ} {hw0 : ∀ i j, 0 < w i j}
  {A : (unitMarket w hw0).AllocRule .nonRival} {p : Fin 2 → ℝ}

public theorem dem (A : (unitMarket w hw0).AllocRule .nonRival) {q : Fin 2 → ℝ} (hq : 0 ≤ q)
    (i : B) : A q i ∈ (unitMarket w hw0).demand i q :=
  (show A q ∈ (unitMarket w hw0).nonRivalDem q from A.mem_dem q hq) i

/-- At a Nash equilibrium, seller `j`'s revenue is positive if the other price is. -/
private theorem revenue_pos_of_isNashEq [Nonempty B] (hNE : IsNashEq A p) {j k : Fin 2}
    (hjk : j ≠ k) (hk : 0 < p k) : 0 < revenue p (A p) j := by
  obtain ⟨δ, hδ, hδ1, hδi⟩ := exists_pos_forall one_pos
    (P := fun i δ ↦ δ * w i k < p k * w i j) fun i ↦
      ContinuousAt.eventually_lt (by fun_prop) continuousAt_const
        (by simpa using mul_pos hk (hw0 i j))
  set q := Function.update p j δ
  have hq : 0 ≤ q := update_nonneg hNE.1 j hδ.le
  have hqj : q j = δ := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  have : revenue q (A q) j = ∑ _i : B, δ := by
    rw [revenue_eq]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [pay_of_prefers hq (dem A hq i) hjk (by rw [hqj, hqk]; exact hδi i), hqj,
      min_eq_right hδ1.le]
  have hpos : 0 < revenue q (A q) j := by
    rw [this]; exact sum_pos (fun _ _ ↦ hδ) univ_nonempty
  exact hpos.trans_le (hNE.2 j δ hδ.le)

/-- At a Nash equilibrium, `p₁ + p₂ ≥ 1`. -/
private theorem one_le_sum_of_isNashEq [Nonempty B] (hNE : IsNashEq A p) : 1 ≤ p 0 + p 1 := by
  by_contra! h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  set s := 1 - p 1 with hs_def
  have hs : p 0 < s := by linarith
  set q := Function.update p 0 s
  have hq : 0 ≤ q := update_nonneg hNE.1 0 ((hNE.1 0).trans hs.le)
  have hq0 : q 0 = s := by simp [q]
  have hq1 : q 1 = p 1 := by simp [q]
  have hRq : revenue q (A q) 0 = ∑ _i : B, s := by
    rw [revenue_eq]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [pay_of_sum_le hq (dem A hq i) h01 (by rw [hq0, hq1]; linarith), hq0]
  have hRp : revenue p (A p) 0 = ∑ _i : B, p 0 := by
    rw [revenue_eq]
    exact sum_congr rfl fun i _ ↦ pay_of_sum_le hNE.1 (dem A hNE.1 i) h01 h.le
  have := hNE.2 0 s ((hNE.1 0).trans hs.le)
  rw [hRq, hRp] at this
  exact this.not_gt (sum_lt_sum_of_nonempty univ_nonempty fun _ _ ↦ hs)

/-- At a Nash equilibrium, both prices are positive. -/
private theorem pos_of_isNashEq [Nonempty B] (hNE : IsNashEq A p) (j : Fin 2) : 0 < p j := by
  obtain ⟨k, hjk⟩ := exists_other j
  by_contra! hj
  have hj0 : p j = 0 := le_antisymm hj (hNE.1 j)
  have hk : 0 < p k := by linarith [one_le_sum_of_isNashEq hNE, add_eq_of_ne hjk p]
  have := revenue_pos_of_isNashEq hNE hjk hk
  simp [revenue, hj0] at this

/-- If `p₁ + p₂ = 1`, no buyer strictly prefers either good. -/
private theorem not_prefers_of_sum_eq_one [Nonempty B] (hNE : IsNashEq A p) {j k : Fin 2}
    (hjk : j ≠ k) (hsum : p j + p k = 1) {c : B} (hc : p j * w c k < p k * w c j) : False := by
  have hpk := pos_of_isNashEq hNE k
  have hpj1 : p j < 1 := by linarith
  obtain ⟨δ, hδ, hδa, hδc⟩ := exists_pos_forall (ι := Unit) (sub_pos.mpr hpj1)
    (P := fun _ δ ↦ (p j + δ) * w c k < p k * w c j) fun _ ↦
      ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simpa using hc)
  set q := Function.update p j (p j + δ)
  have hs : 0 ≤ p j + δ := by linarith [show 0 ≤ p j from hNE.1 j]
  have hq : 0 ≤ q := update_nonneg hNE.1 j hs
  have hqj : q j = p j + δ := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  have hR : (∑ _i : B, p j) + δ ≤ revenue q (A q) j := by
    rw [revenue_eq]
    refine sum_add_le_sum (fun i ↦ ?_) c ?_
    · -- Every buyer still pays at least `1 - p_k = p_j`.
      have := le_pay hq (dem A hq i) hjk
      rw [hqk, min_eq_left (by rw [hqj]; linarith)] at this
      linarith
    · rw [pay_of_prefers hq (dem A hq c) hjk (by rw [hqj, hqk]; exact hδc ()), hqj,
        min_eq_right (by linarith)]
  have hRp : revenue p (A p) j = ∑ _i : B, p j := by
    rw [revenue_eq]
    exact sum_congr rfl fun i _ ↦ pay_of_sum_le hNE.1 (dem A hNE.1 i) hjk hsum.le
  linarith [hNE.2 j (p j + δ) hs]

/-- `min(1, s) - δ ≤ min(1, s - δ)` for `δ ≥ 0`. -/
private theorem min_one_sub_le (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : min 1 s - δ ≤ min 1 (s - δ) := by
  rcases le_total 1 (s - δ) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : (1 : ℝ) ≤ s)]
    linarith
  · rw [min_eq_right h]; linarith [min_le_right 1 s]

/-- If `p_j + p_k > 1` and buyer `c` is indifferent and pays seller `j` less than `min(1, p_j)`,
then seller `j` can profitably lower her price. -/
private theorem tie_aux [Nonempty B] (hNE : IsNashEq A p) {j k : Fin 2} (hjk : j ≠ k)
    (hsum : 1 < p j + p k) {c : B} (hc : p j * w c k = p k * w c j)
    (hg : p j * A p c j < min 1 (p j)) : False := by
  set g := min 1 (p j) - p j * A p c j
  have hg' : 0 < g := sub_pos.mpr hg
  have hpj := pos_of_isNashEq hNE j
  have hn : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 < min (p j) (min (p j + p k - 1) (g / Fintype.card B)) :=
    lt_min hpj (lt_min (by linarith) (div_pos hg' hn))
  -- Buyers who strictly prefer good `k` keep doing so.
  obtain ⟨δ, hδ, hδa, hδi⟩ := exists_pos_forall ha
    (P := fun i δ ↦ p k * w i j < p j * w i k → p k * w i j < (p j - δ) * w i k) fun i ↦ by
      by_cases hi : p k * w i j < p j * w i k
      · filter_upwards [ContinuousAt.eventually_lt (f := fun _ ↦ p k * w i j)
          (g := fun δ ↦ (p j - δ) * w i k) continuousAt_const (by fun_prop) (by simpa using hi)]
          with δ hδ using fun _ ↦ hδ
      · exact Eventually.of_forall fun _ h ↦ absurd h hi
  have hδpj : δ < p j := hδa.trans_le (min_le_left _ _)
  have hδs : δ < p j + p k - 1 := hδa.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδg : δ * Fintype.card B < g :=
    (lt_div_iff₀ hn).mp (hδa.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  set q := Function.update p j (p j - δ)
  have hs : 0 ≤ p j - δ := by linarith
  have hq : 0 ≤ q := update_nonneg hNE.1 j hs
  have hqj : q j = p j - δ := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  have hlt : ∀ i, (p j - δ) * w i k < p j * w i k := fun i ↦
    mul_lt_mul_of_pos_right (by linarith) (hw0 i k)
  -- Buyers who strictly prefer good `j` at `q` pay at least `min(1, p_j) - δ`.
  have hpref : ∀ i, (p j - δ) * w i k < p k * w i j → min 1 (p j) - δ ≤ q j * A q i j :=
    fun i hi ↦ by
      rw [pay_of_prefers hq (dem A hq i) hjk (by rw [hqj, hqk]; exact hi), hqj]
      exact min_one_sub_le _ hδ.le
  have hle : ∀ i, p j * A p i j - δ ≤ q j * A q i j := fun i ↦ by
    by_cases hi : p k * w i j < (p j - δ) * w i k
    · -- Buyer `i` strictly prefers good `k` at `q`, hence also at `p`: her payment is unchanged.
      have hip : p k * w i j < p j * w i k := hi.trans (hlt i)
      rw [pay_of_prefers_other hq (dem A hq i) hjk (by rw [hqj, hqk]; exact hi),
        pay_of_prefers_other hNE.1 (dem A hNE.1 i) hjk hip, hqj, hqk,
        min_eq_left (by linarith : (1 : ℝ) ≤ p j - δ + p k), min_eq_left hsum.le]
      linarith
    · -- Otherwise she strictly prefers good `j` at `q` (ties at `q` are ruled out by `hδi`).
      push Not at hi
      have hstrict : (p j - δ) * w i k < p k * w i j := by
        rcases hi.lt_or_eq with h | h
        · exact h
        · exfalso
          have hip : p k * w i j < p j * w i k := by rw [← h]; exact hlt i
          linarith [hδi i hip]
      linarith [hpref i hstrict, pay_le hNE.1 (dem A hNE.1 i) hjk]
  have hc' : p j * A p c j - δ + g ≤ q j * A q c j := by
    have := hpref c (by rw [← hc]; exact hlt c)
    simp only [g]
    linarith
  have hR := sum_add_le_sum hle c hc'
  rw [← revenue_eq, sum_sub_distrib, ← revenue_eq, sum_const, card_univ, nsmul_eq_mul] at hR
  linarith [hNE.2 j (p j - δ) hs]

/-- `min(1, a) + min(1, b) > 1` if `a, b > 0` and `a + b > 1`. -/
private theorem one_lt_min_add_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) :
    1 < min 1 a + min 1 b := by
  rcases le_total 1 a with h1 | h1 <;> rcases le_total 1 b with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]; norm_num
  · rw [min_eq_left h1, min_eq_right h2]; linarith
  · rw [min_eq_right h1, min_eq_left h2]; linarith
  · rw [min_eq_right h1, min_eq_right h2]; exact hab

/-- If `p₁ + p₂ > 1`, no buyer has equal bang per buck for the two goods. -/
private theorem no_tie [Nonempty B] (hNE : IsNashEq A p) {j k : Fin 2} (hjk : j ≠ k)
    (hsum : 1 < p j + p k) {c : B} (hc : p j * w c k = p k * w c j) : False := by
  have hspend := spend_two hNE.1 (dem A hNE.1 c) hjk
  rw [min_eq_left hsum.le] at hspend
  by_cases hj : p j * A p c j < min 1 (p j)
  · exact tie_aux hNE hjk hsum hc hj
  by_cases hk : p k * A p c k < min 1 (p k)
  · exact tie_aux hNE hjk.symm (by linarith) hc.symm hk
  push Not at hj hk
  linarith [one_lt_min_add_min (pos_of_isNashEq hNE j) (pos_of_isNashEq hNE k) hsum]

/-- If `p₁ + p₂ > 1` and `p_j < 1`, no buyer strictly prefers good `j`:
otherwise seller `j` can profitably raise her price. -/
private theorem not_prefers_of_lt_one [Nonempty B] (hNE : IsNashEq A p) {j k : Fin 2}
    (hjk : j ≠ k) (hsum : 1 < p j + p k) (hpj1 : p j < 1) {c : B}
    (hc : p j * w c k < p k * w c j) : False := by
  -- Buyers who strictly prefer good `j` keep doing so.
  obtain ⟨δ, hδ, hδa, hδi⟩ := exists_pos_forall (sub_pos.mpr hpj1)
    (P := fun i δ ↦ p j * w i k < p k * w i j → (p j + δ) * w i k < p k * w i j) fun i ↦ by
      by_cases hi : p j * w i k < p k * w i j
      · filter_upwards [ContinuousAt.eventually_lt (f := fun δ ↦ (p j + δ) * w i k)
          (g := fun _ ↦ p k * w i j) (by fun_prop) continuousAt_const (by simpa using hi)]
          with δ hδ using fun _ ↦ hδ
      · exact Eventually.of_forall fun _ h ↦ absurd h hi
  set q := Function.update p j (p j + δ)
  have hs : 0 ≤ p j + δ := by linarith [show 0 ≤ p j from hNE.1 j]
  have hq : 0 ≤ q := update_nonneg hNE.1 j hs
  have hqj : q j = p j + δ := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  have hpref : ∀ i, p j * w i k < p k * w i j → p j * A p i j + δ = q j * A q i j :=
    fun i hi ↦ by
      rw [pay_of_prefers hq (dem A hq i) hjk (by rw [hqj, hqk]; exact hδi i hi),
        pay_of_prefers hNE.1 (dem A hNE.1 i) hjk hi, hqj, min_eq_right hpj1.le,
        min_eq_right (by linarith)]
  have hle : ∀ i, p j * A p i j ≤ q j * A q i j := fun i ↦ by
    rcases lt_or_gt_of_ne (fun h ↦ no_tie hNE hjk hsum h : p j * w i k ≠ p k * w i j) with
      hi | hi
    · linarith [hpref i hi]
    · -- Buyer `i` strictly prefers good `k` at `p`, hence also at `q`: her payment is unchanged.
      have hiq : p k * w i j < (p j + δ) * w i k :=
        hi.trans (mul_lt_mul_of_pos_right (by linarith) (hw0 i k))
      rw [pay_of_prefers_other hq (dem A hq i) hjk (by rw [hqj, hqk]; exact hiq),
        pay_of_prefers_other hNE.1 (dem A hNE.1 i) hjk hi, hqj, hqk,
        min_eq_left (by linarith : (1 : ℝ) ≤ p j + δ + p k), min_eq_left hsum.le]
  have hR := sum_add_le_sum hle c (hpref c hc).le
  rw [← revenue_eq, ← revenue_eq] at hR
  linarith [hNE.2 j (p j + δ) hs]

/-- If `p₁ + p₂ > 1`, both prices are at least `1`. -/
private theorem one_le_of_isNashEq [Nonempty B] (hNE : IsNashEq A p) (hsum : 1 < p 0 + p 1)
    (j : Fin 2) : 1 ≤ p j := by
  obtain ⟨k, hjk⟩ := exists_other j
  have hsum' : 1 < p j + p k := by rwa [add_eq_of_ne hjk]
  by_contra! hpj1
  -- Every buyer strictly prefers good `k`.
  have hk : ∀ i, p k * w i j < p j * w i k := fun i ↦ by
    rcases lt_trichotomy (p j * w i k) (p k * w i j) with h | h | h
    · exact (not_prefers_of_lt_one hNE hjk hsum' hpj1 h).elim
    · exact (no_tie hNE hjk hsum' h).elim
    · exact h
  obtain ⟨i₀⟩ := ‹Nonempty B›
  rcases lt_or_ge (p k) 1 with hpk1 | hpk1
  · exact not_prefers_of_lt_one hNE hjk.symm (by linarith) hpk1 (hk i₀)
  · -- Seller `j` gets nothing, contradicting `revenue_pos_of_isNashEq`.
    have : revenue p (A p) j = 0 := by
      rw [revenue_eq]
      refine sum_eq_zero fun i _ ↦ ?_
      rw [pay_of_prefers_other hNE.1 (dem A hNE.1 i) hjk (hk i), min_eq_left hsum'.le,
        min_eq_left hpk1, sub_self]
    linarith [revenue_pos_of_isNashEq hNE hjk (pos_of_isNashEq hNE k)]

/-- If both prices are at least `1`, a seller with revenue at most `n/2` can attract every buyer
with a price slightly above `1/2`. -/
private theorem final_aux [Nonempty B] (hw : ∀ i j, w i j ∈ Set.Ico 1 2) (hNE : IsNashEq A p)
    {j k : Fin 2} (hjk : j ≠ k) (hk1 : 1 ≤ p k)
    (hR : revenue p (A p) j ≤ Fintype.card B / 2) : False := by
  obtain ⟨δ, hδ, hδa, hδi⟩ := exists_pos_forall (by norm_num : (0 : ℝ) < 1 / 2)
    (P := fun i δ ↦ (1 / 2 + δ) * w i k < w i j) fun i ↦
      ContinuousAt.eventually_lt (by fun_prop) continuousAt_const
        (by simp; linarith [(hw i k).2, (hw i j).1])
  set q := Function.update p j (1 / 2 + δ)
  have hs : (0 : ℝ) ≤ 1 / 2 + δ := by linarith
  have hq : 0 ≤ q := update_nonneg hNE.1 j hs
  have hqj : q j = 1 / 2 + δ := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  have hRq : revenue q (A q) j = ∑ _i : B, (1 / 2 + δ) := by
    rw [revenue_eq]
    refine sum_congr rfl fun i _ ↦ ?_
    have hi : q j * w i k < q k * w i j := by
      rw [hqj, hqk]
      exact (hδi i).trans_le (le_mul_of_one_le_left (hw0 i j).le hk1)
    rw [pay_of_prefers hq (dem A hq i) hjk hi, hqj, min_eq_right (by linarith)]
  have := hNE.2 j (1 / 2 + δ) hs
  rw [hRq, sum_const, card_univ, nsmul_eq_mul] at this
  have hn : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

/-- `\label{thm:nasheq-uncommon}`, the "only if" direction:
if two buyers have different utility ratios, there is no Nash equilibrium. -/
private theorem not_isNashEq [Nonempty B] (hw : ∀ i j, w i j ∈ Set.Ico 1 2) {a c : B}
    (hac : w a 0 * w c 1 < w c 0 * w a 1) (hNE : IsNashEq A p) : False := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rcases (one_le_sum_of_isNashEq hNE).lt_or_eq with hsum | hsum
  · -- `p₁ + p₂ > 1`: both prices are at least `1`, and the total revenue is `n`.
    have h1 := one_le_of_isNashEq hNE hsum
    have htot : revenue p (A p) 0 + revenue p (A p) 1 = Fintype.card B := by
      rw [revenue_eq, revenue_eq, ← sum_add_distrib]
      simp_rw [spend_two hNE.1 (dem A hNE.1 _) h01, min_eq_left hsum.le]
      simp
    rcases le_total (revenue p (A p) 0) (Fintype.card B / 2) with h | h
    · exact final_aux hw hNE h01 (h1 1) h
    · exact final_aux hw hNE h01.symm (h1 0) (by linarith)
  · -- `p₁ + p₂ = 1`: buyer `c` strictly prefers good 1, or buyer `a` strictly prefers good 2.
    by_cases hc : p 0 * w c 1 < p 1 * w c 0
    · exact not_prefers_of_sum_eq_one hNE h01 hsum.symm hc
    · push Not at hc
      have ha : p 1 * w a 0 < p 0 * w a 1 := by
        by_contra! h
        nlinarith [mul_le_mul_of_nonneg_right hc (hw0 a 1).le,
          mul_le_mul_of_nonneg_right h (hw0 c 1).le,
          mul_lt_mul_of_pos_left hac (pos_of_isNashEq hNE 1)]
      exact not_prefers_of_sum_eq_one hNE h01.symm (by linarith) ha

/-- `\label{thm:nasheq-uncommon}`, the "if" direction: if all buyers have the same utility ratio
`α`, then `p = (α / (1 + α), 1 / (1 + α))` is a Nash equilibrium. -/
private theorem isNashEq_of_ratio_eq [Nonempty B] (i₀ : B)
    (h : ∀ i k, w i 0 / w i 1 = w k 0 / w k 1) :
    IsNashEq A ![w i₀ 0 / w i₀ 1 / (1 + w i₀ 0 / w i₀ 1), 1 / (1 + w i₀ 0 / w i₀ 1)] := by
  set α := w i₀ 0 / w i₀ 1 with hα_def
  have hα : 0 < α := div_pos (hw0 i₀ 0) (hw0 i₀ 1)
  set p : Fin 2 → ℝ := ![α / (1 + α), 1 / (1 + α)]
  have hp0 : p 0 = α / (1 + α) := rfl
  have hp1 : p 1 = 1 / (1 + α) := rfl
  have hp : 0 ≤ p := fun l ↦ by
    fin_cases l
    exacts [div_nonneg hα.le (by linarith), div_nonneg zero_le_one (by linarith)]
  have h1α : 1 + α ≠ 0 := (by linarith : (0 : ℝ) < 1 + α).ne'
  have hsum : p 0 + p 1 = 1 := by
    rw [hp0, hp1, ← add_div, add_comm, div_self h1α]
  -- Every buyer is indifferent between the two goods.
  have htie : ∀ i, p 0 * w i 1 = p 1 * w i 0 := fun i ↦ by
    have := h i i₀
    rw [div_eq_iff (hw0 i 1).ne'] at this
    rw [hp0, hp1, this, ← hα_def]
    field_simp
  refine ⟨hp, fun j s hs ↦ ?_⟩
  obtain ⟨k, hjk⟩ := exists_other j
  have hsum' : p j + p k = 1 := by rw [add_eq_of_ne hjk]; exact hsum
  have htie' : ∀ i, p j * w i k = p k * w i j := fun i ↦ by
    rcases fin_two_cases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [htie i, (htie i).symm]
  set q := Function.update p j s
  have hq : 0 ≤ q := update_nonneg hp j hs
  have hqj : q j = s := by simp [q]
  have hqk : q k = p k := by simp [q, hjk.symm]
  rw [revenue_eq, revenue_eq]
  refine sum_le_sum fun i _ ↦ ?_
  rw [pay_of_sum_le hp (dem A hp i) hjk hsum'.le]
  rcases le_or_gt s (p j) with hsj | hsj
  · -- Seller `j` gets at most `s ≤ p_j` from each buyer.
    exact (pay_le hq (dem A hq i) hjk).trans ((min_le_right _ _).trans (by rw [hqj]; exact hsj))
  · -- Every buyer strictly prefers good `k` and pays `1 - p_k = p_j` to seller `j`.
    have hi : q k * w i j < q j * w i k := by
      rw [hqj, hqk, ← htie' i]
      exact mul_lt_mul_of_pos_right hsj (hw0 i k)
    have hpk1 : p k ≤ 1 := by linarith [show 0 ≤ p j from hp j]
    rw [pay_of_prefers_other hq (dem A hq i) hjk hi, hqj, hqk, min_eq_left (by linarith),
      min_eq_right hpk1]
    linarith

end NashEq

/-- `\cref{thm:nasheq-uncommon}`. -/
public theorem nasheq_uncommon_aux [Nonempty B] (w : B → Fin 2 → ℝ)
    (hw : ∀ i j, w i j ∈ Set.Ico 1 2)
    (A : (Market.ofLinear (fun _ ↦ 1) w (fun _ ↦ one_pos)
      (fun i j ↦ one_pos.trans_le (hw i j).1)).AllocRule .nonRival) :
    (∃ p, IsNashEq A p) ↔ ∀ i k, w i 0 / w i 1 = w k 0 / w k 1 := by
  have hw0 : ∀ i j, 0 < w i j := fun i j ↦ one_pos.trans_le (hw i j).1
  obtain ⟨i₀⟩ := ‹Nonempty B›
  refine ⟨fun ⟨p, hNE⟩ ↦ ?_, fun h ↦ ⟨_, isNashEq_of_ratio_eq (A := A) i₀ h⟩⟩
  by_contra! hne
  obtain ⟨a, c, hac⟩ := hne
  rw [ne_eq, div_eq_div_iff (hw0 a 1).ne' (hw0 c 1).ne'] at hac
  rcases lt_or_gt_of_ne hac with h | h
  · exact not_isNashEq (A := A) hw h hNE
  · exact not_isNashEq (A := A) hw h hNE

end TwoGoods
