module

public import RareForMarkets.NashEq.Defs
public import RareForMarkets.Prelims
public import RareForMarkets.Defs.Market

/-! Facts used in the proof of `\cref{thm:rivalize-1}`: bounds on `u_min` and `u_max`,
demand facts in a general market, and the bang-per-buck cutoffs `τ(v)`. -/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Rivalize

/-! ### Facts about `u_min` and `u_max` -/

section Weights

omit [Fintype B] [Fintype G]

variable [Finite B] [Finite G]

public theorem minWeight_le (w : B → G → ℝ) (i : B) (j : G) : minWeight w ≤ w i j :=
  (ciInf_le (Set.finite_range _).bddBelow i).trans (ciInf_le (Set.finite_range _).bddBelow j)

public theorem le_maxWeight (w : B → G → ℝ) (i : B) (j : G) : w i j ≤ maxWeight w :=
  (le_ciSup (Set.finite_range _).bddAbove j).trans
    (le_ciSup (Set.finite_range (fun i ↦ ⨆ j, w i j)).bddAbove i)

omit [Finite B] [Finite G] in
/-- The hypothesis `0 < ε < u_min² / u_max` forces at least one buyer and one good
(otherwise `u_min = 0`). -/
public theorem nonempty_of_lt_minWeight {w : B → G → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hεw : ε < minWeight w ^ 2 / maxWeight w) : Nonempty B ∧ Nonempty G := by
  by_contra h
  have : minWeight w = 0 := by
    rcases not_and_or.mp h with hB | hG
    · rw [not_nonempty_iff] at hB; exact Real.iInf_of_isEmpty _
    · rw [not_nonempty_iff] at hG; simp [minWeight]
  rw [this] at hεw
  simp at hεw
  linarith

public theorem minWeight_pos [Nonempty B] [Nonempty G] {w : B → G → ℝ} (hw : ∀ i j, 0 < w i j) :
    0 < minWeight w := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i ↦ ⨅ j, w i j)
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := w i)
  rw [minWeight, ← hi, ← hj]
  exact hw i j

end Weights

/-! ### Demand facts in a general market -/

section Demand

omit [Fintype B]

/-- A demanded bundle contains all of every zero-price good. -/
public theorem demand_apply_eq_one_of_price_zero (M : Market B G) {i : B}
    {p z : G → ℝ} (hz : z ∈ M.demand i p) {j : G} (hpj : p j = 0) : z j = 1 := by
  classical
  by_contra h
  have hlt : z j < 1 := lt_of_le_of_ne (hz.1.1.2 j) h
  set z' := Function.update z j 1
  have hz' : z' ∈ M.budgetSet i p := by
    refine ⟨⟨fun k ↦ ?_, fun k ↦ ?_⟩, ?_⟩
    · by_cases hk : k = j
      · simp [z', hk]
      · simpa [z', hk] using hz.1.1.1 k
    · by_cases hk : k = j
      · simp [z', hk]
      · simpa [z', hk] using hz.1.1.2 k
    · refine le_of_eq_of_le (sum_congr rfl fun k _ ↦ ?_) hz.1.2
      by_cases hk : k = j
      · simp [z', hk, hpj]
      · simp [z', hk]
  have hzz' : z < z' := Pi.lt_def.mpr ⟨fun k ↦ by
    by_cases hk : k = j
    · subst hk; simpa [z'] using hz.1.1.2 k
    · simp [z', hk], j, by simpa [z'] using hlt⟩
  exact (M.util_strictMonoOn i hz.1.1 hz'.1 hzz').not_ge ((isMaxOn_iff.mp hz.2) z' hz')

/-- If the full bundle is affordable, it is the only demanded bundle. -/
public theorem demand_eq_one (M : Market B G) {i : B} {p z : G → ℝ} (hz : z ∈ M.demand i p)
    (hp : ∑ j, p j ≤ M.budget i) : z = 1 := by
  by_contra h
  have h1 : (1 : G → ℝ) ∈ M.budgetSet i p :=
    ⟨Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩, by simpa using hp⟩
  exact (M.util_strictMonoOn i hz.1.1 h1.1 (lt_of_le_of_ne hz.1.1.2 h)).not_ge
    ((isMaxOn_iff.mp hz.2) 1 h1)

end Demand

/-! ### Bang-per-buck cutoffs

For prices `p`, budget `b`, and utility coefficients `v`, the cutoff `τ(v)` is the supremum of
the thresholds `t` such that the positively-priced goods with bang-per-buck `vⱼ / pⱼ ≥ t` cost
at least `b`. This is the paper's `τ(v)`, written as a supremum over all `t`
(rather than a maximum over the bang-per-bucks). -/

section Cutoff

omit [Fintype B]

variable {p : G → ℝ} {b : ℝ}

variable (p) in
/-- The total price of the positively-priced goods `j` with `t pⱼ ≤ vⱼ`. -/
@[expose] public noncomputable def spendAbove (v : G → ℝ) (t : ℝ) : ℝ :=
  ∑ j, if 0 < p j ∧ t * p j ≤ v j then p j else 0

variable (p b) in
/-- The thresholds `t` whose goods `{j : 0 < pⱼ, t pⱼ ≤ vⱼ}` cost at least `b`. -/
@[expose] public def cutoffSet (v : G → ℝ) : Set ℝ := {t | b ≤ spendAbove p v t}

variable (p b) in
/-- The cutoff `τ(v)`. -/
@[expose] public noncomputable def cutoff (v : G → ℝ) : ℝ := sSup (cutoffSet p b v)

public theorem cutoffSet_bddAbove (hp : 0 ≤ p) (hb : 0 < b) {v : G → ℝ} (hv : 0 ≤ v) :
    BddAbove (cutoffSet p b v) := by
  refine ⟨∑ j, v j / p j, fun t (ht : b ≤ spendAbove p v t) ↦ ?_⟩
  by_contra! h
  have : spendAbove p v t = 0 := by
    refine sum_eq_zero fun j _ ↦ if_neg fun ⟨hpj, hj⟩ ↦ ?_
    have h1 : v j / p j ≤ ∑ k, v k / p k :=
      single_le_sum (f := fun k ↦ v k / p k) (fun k _ ↦ div_nonneg (hv k) (hp k)) (mem_univ j)
    have h2 : t ≤ v j / p j := (le_div_iff₀ hpj).mpr hj
    linarith
  linarith

/-- If `c v ≤ v'` coordinatewise, then `t ∈ cutoffSet v` implies `c t ∈ cutoffSet v'`. -/
public theorem mul_mem_cutoffSet {v v' : G → ℝ} {c t : ℝ} (hc : 0 < c)
    (hvv' : ∀ j, c * v j ≤ v' j) (ht : t ∈ cutoffSet p b v) : c * t ∈ cutoffSet p b v' := by
  refine (show b ≤ spendAbove p v t from ht).trans (sum_le_sum fun j _ ↦ ?_)
  by_cases h1 : 0 < p j ∧ t * p j ≤ v j
  · have h : c * t * p j ≤ v' j :=
      calc c * t * p j = c * (t * p j) := by ring
        _ ≤ c * v j := mul_le_mul_of_nonneg_left h1.2 hc.le
        _ ≤ v' j := hvv' j
    rw [if_pos h1, if_pos ⟨h1.1, h⟩]
  · rw [if_neg h1]
    split_ifs with h2
    exacts [h2.1.le, le_rfl]

/-- If `c v ≤ v'` coordinatewise, then `c τ(v) ≤ τ(v')`. -/
public theorem mul_cutoff_le (hp : 0 ≤ p) (hb : 0 < b) {v v' : G → ℝ} (hv' : 0 ≤ v')
    {c : ℝ} (hc : 0 < c) (hvv' : ∀ j, c * v j ≤ v' j) (hne : (cutoffSet p b v).Nonempty) :
    c * cutoff p b v ≤ cutoff p b v' := by
  rw [← le_div_iff₀' hc]
  refine csSup_le hne fun t ht ↦ ?_
  rw [le_div_iff₀' hc]
  exact le_csSup (cutoffSet_bddAbove hp hb hv') (mul_mem_cutoffSet hc hvv' ht)

/-- When the full bundle is unaffordable, `1 / ∑ⱼ pⱼ` is an admissible threshold for `v = 1`. -/
public theorem inv_sum_mem_cutoffSet (hp : 0 ≤ p) (hb : 0 < b) (hpb : b < ∑ j, p j) :
    (∑ j, p j)⁻¹ ∈ cutoffSet p b 1 := by
  have hP : 0 < ∑ j, p j := hb.trans hpb
  refine hpb.le.trans (le_of_eq (sum_congr rfl fun j _ ↦ ?_).symm)
  by_cases hpj : 0 < p j
  · have h : (∑ j, p j)⁻¹ * p j ≤ (1 : G → ℝ) j := by
      rw [Pi.one_apply, inv_mul_le_iff₀ hP, mul_one]
      exact single_le_sum (fun k _ ↦ hp k) (mem_univ j)
    rw [if_pos ⟨hpj, h⟩]
  · rw [if_neg (fun h ↦ hpj h.1)]
    linarith [show 0 ≤ p j from hp j, not_lt.mp hpj]

/-- `eq:rivalize-cutoff`, first part: goods above the cutoff are bought completely. -/
public theorem demand_eq_one_of_cutoff_lt (M : Market B G) {i : B} {v : G → ℝ}
    (hu : M.util i = linearUtil v) (hv : ∀ j, 0 < v j) (hp : 0 ≤ p) {z : G → ℝ}
    (hz : z ∈ M.demand i p) {j : G} (hpj : 0 < p j)
    (hj : cutoff p (M.budget i) v * p j < v j) : z j = 1 := by
  by_contra hzj
  have hspend := M.spend_eq_budget_of_demand hp hz (lt_of_le_of_ne (hz.1.1.2 j) hzj)
  have hr : cutoff p (M.budget i) v < v j / p j := (lt_div_iff₀ hpj).mpr hj
  refine hr.not_ge (le_csSup (cutoffSet_bddAbove hp (M.budget_pos i) fun k ↦ (hv k).le) ?_)
  change M.budget i ≤ spendAbove p v (v j / p j)
  rw [← hspend]
  refine sum_le_sum fun k _ ↦ ?_
  split_ifs with hk
  · exact mul_le_of_le_one_right (hp k) (hz.1.1.2 k)
  · rcases (hp k).lt_or_eq with hpk | hpk
    · have hvk : v k < v j / p j * p k := lt_of_not_ge fun h ↦ hk ⟨hpk, h⟩
      have : p j / v j < p k / v k := by
        rw [div_lt_div_iff₀ (hv j) (hv k)]
        rw [div_mul_eq_mul_div, lt_div_iff₀ hpj] at hvk
        linarith
      rcases M.bangPerBuck hu hv hp hz this with h | h
      · exact absurd h hzj
      · simp [h]
    · simp [← hpk]

/-- `eq:rivalize-cutoff`, second part: goods below the cutoff are not bought at all. -/
public theorem demand_eq_zero_of_lt_cutoff (M : Market B G) {i : B} {v : G → ℝ}
    (hu : M.util i = linearUtil v) (hv : ∀ j, 0 < v j) (hp : 0 ≤ p) {z : G → ℝ}
    (hz : z ∈ M.demand i p) (hne : (cutoffSet p (M.budget i) v).Nonempty) {j : G}
    (hpj : 0 < p j) (hj : v j < cutoff p (M.budget i) v * p j) : z j = 0 := by
  classical
  by_contra hzj
  have hzj' : 0 < z j := lt_of_le_of_ne (hz.1.1.1 j) (Ne.symm hzj)
  have hr : v j / p j < cutoff p (M.budget i) v := (div_lt_iff₀ hpj).mpr hj
  obtain ⟨t, ht, hrt⟩ := exists_lt_of_lt_csSup hne hr
  have ht' : M.budget i ≤ spendAbove p v t := ht
  have hjt : v j < t * p j := (div_lt_iff₀ hpj).mp hrt
  have hjnot : ¬ (0 < p j ∧ t * p j ≤ v j) := fun h ↦ by linarith [h.2]
  have hle : spendAbove p v t + p j * z j ≤ ∑ k, p k * z k := by
    rw [spendAbove, ← add_sum_erase _ _ (mem_univ j), ← add_sum_erase _ _ (mem_univ j),
      if_neg hjnot, zero_add]
    have : ∑ k ∈ univ.erase j, (if 0 < p k ∧ t * p k ≤ v k then p k else 0) ≤
        ∑ k ∈ univ.erase j, p k * z k := by
      refine sum_le_sum fun k _ ↦ ?_
      split_ifs with hk
      · have : p k / v k < p j / v j := by
          rw [div_lt_div_iff₀ (hv k) (hv j)]
          nlinarith [mul_lt_mul_of_pos_left hjt hk.1, mul_le_mul_of_nonneg_left hk.2 hpj.le]
        rcases M.bangPerBuck hu hv hp hz this with h | h
        · rw [h, mul_one]
        · exact absurd h hzj
      · exact mul_nonneg (hp k) (hz.1.1.1 k)
    linarith
  linarith [hz.1.2, mul_pos hpj hzj']

end Cutoff

end Rivalize
