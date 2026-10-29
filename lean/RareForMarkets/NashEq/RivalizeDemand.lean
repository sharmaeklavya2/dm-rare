module

public import RareForMarkets.NashEq.Cutoff
public import RareForMarkets.Defs.Market
public import RareForMarkets.NashEq.Defs
import Mathlib.Algebra.BigOperators.Field

/-! Proofs of `\cref{thm:rivalize-1}`, item 2, and `\cref{thm:rivalize-2}`.

The lemmas are stated for any market `Mh` whose buyers have budget `b` and utilities
`ûᵢ = rivalizeUtil n ε (u_{i,·})`, i.e., for `Market.rivalize`, which is defined
in `ReductionToRival.lean`. -/

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

namespace Rivalize

/-! ### Welfare certificates -/

omit [Fintype G] in
/-- If `∑ᵢ (uᵢ(yᵢ) - uᵢ(xᵢ)) / cᵢ ≤ 0` for all `y ∈ S`, with positive weights `cᵢ`,
then no `y ∈ S` Pareto dominates `x`. -/
private theorem not_paretoDominates_of_weighted {M : Market B G} {x : B → G → ℝ}
    {S : Set (B → G → ℝ)} (c : B → ℝ) (hc : ∀ i, 0 < c i)
    (hcert : ∀ y ∈ S, ∑ i, (M.util i (y i) - M.util i (x i)) / c i ≤ 0) :
    ∀ y ∈ S, ¬ M.ParetoDominates y x := by
  rintro y hy ⟨hle, i, hlt⟩
  have : 0 < ∑ i, (M.util i (y i) - M.util i (x i)) / c i :=
    sum_pos' (fun k _ ↦ div_nonneg (sub_nonneg.mpr (hle k)) (hc k).le)
      ⟨i, mem_univ i, div_pos (sub_pos.mpr hlt) (hc i)⟩
  linarith [hcert y hy]

/-- `eq:rivalize-support`: the line of slope `Q` through `(x, f(x))` lies above the graph of
`f(t) = a min(t, 1) + e max(t - 1, 0)` on `t ≥ 0`, if `Q` lies between the slopes of `f`
on both sides of `x`. -/
private theorem rivalize_support {a e Q x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t)
    (haQ : x < 1 → a ≤ Q) (hQa : 0 < x → Q ≤ a) (heQ : e ≤ Q) :
    a * min t 1 + e * max (t - 1) 0 - (a * min x 1 + e * max (x - 1) 0) ≤ Q * (t - x) := by
  rw [min_eq_left hx1, max_eq_right (show x - 1 ≤ 0 by linarith)]
  rcases le_or_gt t 1 with h | h
  · rw [min_eq_left h, max_eq_right (show t - 1 ≤ 0 by linarith)]
    rcases le_or_gt x t with hxt | hxt
    · rcases hx1.lt_or_eq with hx | hx
      · nlinarith [mul_nonneg (sub_nonneg.mpr (haQ hx)) (sub_nonneg.mpr hxt)]
      · have : t = x := by linarith
        simp [this]
    · nlinarith [mul_nonneg (sub_nonneg.mpr (hQa (by linarith))) (sub_nonneg.mpr hxt.le)]
  · rw [min_eq_right h.le, max_eq_left (show 0 ≤ t - 1 by linarith)]
    rcases hx1.lt_or_eq with hx | hx
    · nlinarith [mul_nonneg (sub_nonneg.mpr (haQ hx)) (sub_nonneg.mpr hx.le),
        mul_nonneg (sub_nonneg.mpr heQ) (sub_nonneg.mpr h.le)]
    · subst hx
      nlinarith [mul_nonneg (sub_nonneg.mpr heQ) (sub_nonneg.mpr h.le)]

/-! ### Demand sets -/

/-- `ûᵢ(z / n) = uᵢ(z)` for every bundle `z ∈ [0, 1]^m`. -/
private theorem rivalizeUtil_div {n ε : ℝ} (hn : 0 < n) (v z : G → ℝ) (hz : z ∈ cube G) :
    rivalizeUtil n ε v (fun j ↦ z j / n) = linearUtil v z := by
  refine sum_congr rfl fun j _ ↦ ?_
  have : n * (z j / n) = z j := by field_simp
  have hz1 : z j ≤ 1 := hz.2 j
  rw [this, min_eq_left hz1, max_eq_right (show z j - 1 ≤ 0 by linarith)]
  ring

/-- If every `yᵢ ∈ [0, 1]^m` is affordable at `p`, then `y / n ∈ Aff^R(n p; Î)`. -/
private theorem div_mem_rivalAff {b : ℝ} {Mh : Market B G} (hMb : ∀ i, Mh.budget i = b) [Nonempty B]
    {p : G → ℝ} {y : B → G → ℝ} (hy : ∀ i, y i ∈ cube G) (hyb : ∀ i, ∑ j, p j * y i j ≤ b) :
    (fun i j ↦ y i j / Fintype.card B) ∈ Mh.rivalAff (fun j ↦ Fintype.card B * p j) := by
  have hn : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos
  refine ⟨fun j ↦ ?_, fun i ↦ ⟨⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩⟩
  · calc ∑ i, y i j / Fintype.card B ≤ ∑ _i : B, 1 / (Fintype.card B : ℝ) :=
          sum_le_sum fun i _ ↦ div_le_div_of_nonneg_right ((hy i).2 j) hn.le
      _ = 1 := by simp [sum_const, card_univ]
  · exact div_nonneg ((hy i).1 j) hn.le
  · exact (div_le_one hn).mpr (((hy i).2 j).trans hn1)
  · rw [hMb]
    refine le_of_eq_of_le (sum_congr rfl fun j _ ↦ ?_) (hyb i)
    field_simp

/-- The reverse implication of `\cref{thm:rivalize-1}`, item 2. -/
private theorem mem_nonRivalDem_of_rivalize {b ε : ℝ} {w : B → G → ℝ} (hb : 0 < b)
    (hw : ∀ i j, 0 < w i j) {Mh : Market B G} (hMb : ∀ i, Mh.budget i = b)
    (hMu : ∀ i, Mh.util i = rivalizeUtil (Fintype.card B) ε (w i)) [Nonempty B]
    {p : G → ℝ} {x : B → G → ℝ} (hx : ∀ i, x i ∈ cube G)
    (hxh : (fun i j ↦ x i j / Fintype.card B) ∈ Mh.rivalDem (fun j ↦ Fintype.card B * p j)) :
    x ∈ (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).nonRivalDem p := by
  classical
  have hn : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hxb : ∀ i, ∑ j, p j * x i j ≤ b := fun i ↦ by
    have := (hxh.1.2 i).2
    rw [hMb] at this
    refine le_of_eq_of_le (sum_congr rfl fun j _ ↦ ?_) this
    simp only
    field_simp
  refine fun i ↦ ⟨⟨hx i, hxb i⟩, isMaxOn_iff.mpr fun z hz ↦ ?_⟩
  by_contra! hlt
  set y := Function.update x i z
  have hy : ∀ k, y k ∈ cube G := fun k ↦ by
    by_cases hk : k = i
    · subst hk; simpa [y] using hz.1
    · simpa [y, hk] using hx k
  have hyb : ∀ k, ∑ j, p j * y k j ≤ b := fun k ↦ by
    by_cases hk : k = i
    · subst hk; simpa [y] using hz.2
    · simpa [y, hk] using hxb k
  refine hxh.2 _ (div_mem_rivalAff hMb hy hyb) ⟨fun k ↦ ?_, i, ?_⟩
  · by_cases hk : k = i
    · subst hk
      rw [hMu, rivalizeUtil_div hn _ _ (hx k), rivalizeUtil_div hn _ _ (hy k)]
      simpa [y] using hlt.le
    · simp [y, hk]
  · rw [hMu, rivalizeUtil_div hn _ _ (hx i), rivalizeUtil_div hn _ _ (hy i)]
    simpa [y] using hlt

/-- The forward implication of `\cref{thm:rivalize-1}`, item 2. -/
private theorem rivalize_mem_rivalDem {b ε : ℝ} {w : B → G → ℝ} (hb : 0 < b)
    (hw : ∀ i j, 0 < w i j) {Mh : Market B G} (hMb : ∀ i, Mh.budget i = b)
    (hMu : ∀ i, Mh.util i = rivalizeUtil (Fintype.card B) ε (w i))
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w) [Nonempty B] [Nonempty G]
    {p : G → ℝ} (hp : 0 ≤ p) {x : B → G → ℝ}
    (hx : x ∈ (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).nonRivalDem p) :
    (fun i j ↦ x i j / Fintype.card B) ∈ Mh.rivalDem (fun j ↦ Fintype.card B * p j) := by
  set M := Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw
  set n : ℝ := (Fintype.card B : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  set umin := minWeight w
  set umax := maxWeight w
  have humin : 0 < umin := minWeight_pos hw
  have humin_le : ∀ i j, umin ≤ w i j := minWeight_le w
  have hle_umax : ∀ i j, w i j ≤ umax := le_maxWeight w
  obtain ⟨i₀⟩ := ‹Nonempty B›
  obtain ⟨j₀⟩ := ‹Nonempty G›
  have humax : 0 < umax := humin.trans_le ((humin_le i₀ j₀).trans (hle_umax i₀ j₀))
  have hεumax : ε * umax < umin ^ 2 := (lt_div_iff₀ humax).mp hεw
  have hεumin : ε ≤ umin := by
    have : umin ≤ umax := (humin_le i₀ j₀).trans (hle_umax i₀ j₀)
    nlinarith
  have hxc : ∀ i, x i ∈ cube G := fun i ↦ (hx i).1.1
  -- The utility `ûᵢ(yᵢ) = ∑ⱼ f_{i,j}(n y_{i,j})`, and `ûᵢ(xᵢ / n) = ∑ⱼ f_{i,j}(x_{i,j})`.
  set f : B → G → ℝ → ℝ := fun i j t ↦ w i j * min t 1 + ε * max (t - 1) 0
  have hfx : ∀ i, Mh.util i (fun j ↦ x i j / n) = ∑ j, f i j (x i j) := fun i ↦ by
    rw [hMu]
    refine sum_congr rfl fun j _ ↦ ?_
    have : n * (x i j / n) = x i j := by field_simp
    simp only [f, this]
  -- A weighted welfare certificate: weights `cᵢ` and slopes `q_j` satisfying the support
  -- inequality and `∑_{i,j} q_j (n y_{i,j} - x_{i,j}) ≤ 0` show Pareto optimality.
  have key : ∀ (c : B → ℝ) (q : G → ℝ), (∀ i, 0 < c i) →
      (∀ i j t, 0 ≤ t → (f i j t - f i j (x i j)) / c i ≤ q j * (t - x i j)) →
      (∀ y ∈ Mh.rivalAff (fun j ↦ n * p j), ∑ i, ∑ j, q j * (n * y i j - x i j) ≤ 0) →
      (fun i j ↦ x i j / n) ∈ Mh.rivalDem (fun j ↦ n * p j) := by
    intro c q hc hsupp hsum
    refine ⟨div_mem_rivalAff hMb hxc fun i ↦ (hx i).1.2,
      not_paretoDominates_of_weighted c hc fun y hy ↦ ?_⟩
    refine le_trans (sum_le_sum fun i _ ↦ ?_) (hsum y hy)
    have hfy : Mh.util i (y i) = ∑ j, f i j (n * y i j) := by rw [hMu]; rfl
    rw [hfy, hfx, ← sum_sub_distrib, sum_div]
    exact sum_le_sum fun j _ ↦ hsupp i j _ (mul_nonneg hn.le ((hy.2 i).1.1 j))
  rcases le_or_gt (∑ j, p j) b with hpb | hpb
  · -- Case 1: the full bundle is affordable, so `x = 1`; use weights `1` and slopes `u_min`.
    have hx1 : ∀ i j, x i j = 1 := fun i j ↦ congrFun (demand_eq_one M (hx i) hpb) j
    refine key (fun _ ↦ 1) (fun _ ↦ umin) (fun _ ↦ one_pos) (fun i j t ht ↦ ?_) fun y hy ↦ ?_
    · rw [div_one]
      exact rivalize_support ((hxc i).1 j) ((hxc i).2 j) ht (by simp [hx1]) (fun _ ↦ humin_le i j)
        hεumin
    · rw [sum_comm]
      refine sum_nonpos fun j _ ↦ ?_
      simp only [hx1, mul_sub, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul,
        mul_one]
      nlinarith [hy.1 j, mul_pos humin hn]
  · -- Case 2: the full bundle is unaffordable; use the cutoffs `λᵢ` as weights.
    have hspend : ∀ i, ∑ j, p j * x i j = b := fun i ↦ by
      rw [M.spend_eq_min_of_demand hp (hx i)]
      exact min_eq_left hpb.le
    set lam : B → ℝ := fun i ↦ cutoff p b (w i)
    set lam0 := cutoff p b 1
    have hne1 := inv_sum_mem_cutoffSet hp hb hpb
    have hlam0 : 0 < lam0 :=
      (inv_pos.mpr (hb.trans hpb)).trans_le (le_csSup (cutoffSet_bddAbove hp hb zero_le_one) hne1)
    have hne : ∀ i, (cutoffSet p b (w i)).Nonempty := fun i ↦
      ⟨_, mul_mem_cutoffSet humin (fun j ↦ by simpa using humin_le i j) hne1⟩
    have hlow : ∀ k, umin * lam0 ≤ lam k := fun k ↦
      mul_cutoff_le hp hb (fun j ↦ (hw k j).le) humin (fun j ↦ by simpa using humin_le k j)
        ⟨_, hne1⟩
    have hup : ∀ i, lam i ≤ umax * lam0 := fun i ↦ by
      have := mul_cutoff_le hp hb zero_le_one (inv_pos.mpr humax)
        (fun j ↦ by rw [Pi.one_apply, inv_mul_le_iff₀ humax, mul_one]; exact hle_umax i j) (hne i)
      exact (inv_mul_le_iff₀ humax).mp this
    have hlam : ∀ i, 0 < lam i := fun i ↦ (mul_pos humin hlam0).trans_le (hlow i)
    -- `ε λᵢ ≤ u_{i,j} λ_k` for all `i, j, k` (`eq:rivalize-tail-bound`).
    have hcross : ∀ i j k, ε / lam k ≤ w i j / lam i := fun i j k ↦ by
      rw [div_le_div_iff₀ (hlam k) (hlam i)]
      calc ε * lam i ≤ ε * (umax * lam0) := by gcongr; exact hup i
        _ = (ε * umax) * lam0 := by ring
        _ ≤ umin ^ 2 * lam0 := by gcongr
        _ = umin * (umin * lam0) := by ring
        _ ≤ umin * lam k := by gcongr; exact hlow k
        _ ≤ w i j * lam k := by gcongr; exacts [(hlam k).le, humin_le i j]
    set θ := ⨆ k, ε / lam k
    have hθ_ge : ∀ k, ε / lam k ≤ θ := fun k ↦
      le_ciSup (f := fun k ↦ ε / lam k) (Set.finite_range _).bddAbove k
    have hθ_le : ∀ i j, θ ≤ w i j / lam i := fun i j ↦ ciSup_le fun k ↦ hcross i j k
    -- `eq:rivalize-cutoff`, phrased with `w / λ` against the prices.
    have hcut1 : ∀ i j, x i j < 1 → w i j / lam i ≤ p j := fun i j hxij ↦ by
      rcases (hp j).lt_or_eq with hpj | hpj
      · rw [div_le_iff₀ (hlam i), mul_comm]
        exact le_of_not_gt fun h ↦ hxij.ne (demand_eq_one_of_cutoff_lt M rfl (hw i) hp (hx i) hpj h)
      · exact absurd (demand_apply_eq_one_of_price_zero M (hx i) hpj.symm) hxij.ne
    have hcut0 : ∀ i j, 0 < x i j → p j ≤ w i j / lam i := fun i j hxij ↦ by
      rcases (hp j).lt_or_eq with hpj | hpj
      · rw [le_div_iff₀ (hlam i), mul_comm]
        exact le_of_not_gt fun h ↦ hxij.ne'
          (demand_eq_zero_of_lt_cutoff M rfl (hw i) hp (hx i) (hne i) hpj h)
      · rw [← hpj]; exact (div_pos (hw i j) (hlam i)).le
    set q : G → ℝ := fun j ↦ max (p j) θ
    refine key lam q hlam (fun i j t ht ↦ ?_) fun y hy ↦ ?_
    · have : (f i j t - f i j (x i j)) / lam i =
          w i j / lam i * min t 1 + ε / lam i * max (t - 1) 0 -
            (w i j / lam i * min (x i j) 1 + ε / lam i * max (x i j - 1) 0) := by
        simp only [f]; ring
      rw [this]
      exact rivalize_support ((hxc i).1 j) ((hxc i).2 j) ht
        (fun h ↦ (hcut1 i j h).trans (le_max_left _ _))
        (fun h ↦ max_le (hcut0 i j h) (hθ_le i j)) ((hθ_ge i).trans (le_max_right _ _))
    · -- Split `q = p + (q - p)`: the budgets control `p`, the supplies control `q - p`.
      have hsplit : ∀ i j, q j * (n * y i j - x i j) =
          (n * p j * y i j - p j * x i j) + (q j - p j) * (n * y i j - x i j) := fun _ _ ↦ by ring
      simp_rw [hsplit, sum_add_distrib]
      have h1 : ∑ i, ∑ j, (n * p j * y i j - p j * x i j) ≤ 0 := sum_nonpos fun i _ ↦ by
        have : ∑ j, n * p j * y i j ≤ b := hMb i ▸ (hy.2 i).2
        rw [sum_sub_distrib, hspend i]
        linarith
      have h2 : ∑ i, ∑ j, (q j - p j) * (n * y i j - x i j) ≤ 0 := by
        rw [sum_comm]
        refine sum_nonpos fun j _ ↦ ?_
        rcases (le_max_left (p j) θ).eq_or_lt with h | h
        · simp [q, ← h]
        · -- `q_j > p_j` only for goods that every buyer buys completely.
          have hall : ∀ i, x i j = 1 := fun i ↦ by
            by_contra hne1
            have := hcut1 i j (lt_of_le_of_ne ((hxc i).2 j) hne1)
            have := hθ_le i j
            have : p j < θ := by simpa [q] using h
            linarith
          simp only [hall, ← mul_sum, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
            mul_one]
          rw [← hn_def]
          nlinarith [mul_nonneg (sub_pos.mpr h).le (mul_nonneg hn.le (sub_nonneg.mpr (hy.1 j)))]
      linarith

/-- `\cref{thm:rivalize-1}`, item 2. -/
public theorem rivalize_dem_iff_aux {b ε : ℝ} {w : B → G → ℝ} (hb : 0 < b)
    (hw : ∀ i j, 0 < w i j) {Mh : Market B G} (hMb : ∀ i, Mh.budget i = b)
    (hMu : ∀ i, Mh.util i = rivalizeUtil (Fintype.card B) ε (w i))
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    {p : G → ℝ} (hp : 0 ≤ p) (x : B → G → ℝ) :
    x ∈ (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).nonRivalDem p ↔
      (∀ i, x i ∈ cube G) ∧
      (fun i j ↦ x i j / Fintype.card B) ∈ Mh.rivalDem (fun j ↦ Fintype.card B * p j) := by
  obtain ⟨_, _⟩ := nonempty_of_lt_minWeight hε hεw
  exact ⟨fun hx ↦ ⟨fun i ↦ (hx i).1.1, rivalize_mem_rivalDem hb hw hMb hMu hε hεw hp hx⟩,
    fun ⟨hx, hxh⟩ ↦ mem_nonRivalDem_of_rivalize hb hw hMb hMu hx hxh⟩

/-- `\cref{thm:rivalize-2}`, item 1. -/
public theorem rivalize_allocRule_mem_aux {b ε : ℝ} {w : B → G → ℝ} (hb : 0 < b)
    (hw : ∀ i j, 0 < w i j) {Mh : Market B G} (hMb : ∀ i, Mh.budget i = b)
    (hMu : ∀ i, Mh.util i = rivalizeUtil (Fintype.card B) ε (w i))
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    (A : (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).AllocRule .nonRival)
    (p : G → ℝ) (hp : 0 ≤ p) :
    (fun i j ↦ A (fun j ↦ p j / Fintype.card B) i j / Fintype.card B) ∈ Mh.rivalDem p := by
  obtain ⟨_, _⟩ := nonempty_of_lt_minWeight hε hεw
  have hn : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hp' : 0 ≤ fun j ↦ p j / Fintype.card B := fun j ↦ div_nonneg (hp j) hn.le
  have := ((rivalize_dem_iff_aux hb hw hMb hMu hε hεw hp' _).mp (A.mem_dem _ hp')).2
  convert this using 2
  funext j
  field_simp

omit [Fintype G] in
/-- `\cref{thm:rivalize-2}`, item 2, for the function `Â(p) = A(p / n) / n`. -/
public theorem rivalize_isNashEq_iff_aux [DecidableEq G] [Nonempty B]
    (A : (G → ℝ) → (B → G → ℝ)) (p : G → ℝ) :
    IsNashEq (fun p i j ↦ A (fun j ↦ p j / Fintype.card B) i j / Fintype.card B) p ↔
      IsNashEq A (fun j ↦ p j / Fintype.card B) := by
  have hn : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  -- `R^Â_j(q) = R^A_j(q / n)`.
  have hrev : ∀ q j,
      revenue q ((fun p i j ↦ A (fun j ↦ p j / Fintype.card B) i j / Fintype.card B) q) j =
        revenue (fun j ↦ q j / Fintype.card B) (A fun j ↦ q j / Fintype.card B) j := fun q j ↦ by
    simp only [revenue]
    rw [← sum_div]
    field_simp
  have hupd : ∀ (q : G → ℝ) j s, (fun k ↦ Function.update q j s k / Fintype.card B) =
      Function.update (fun k ↦ q k / Fintype.card B) j (s / Fintype.card B) := fun q j s ↦ by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have hnn : 0 ≤ p ↔ 0 ≤ fun j ↦ p j / Fintype.card B :=
    ⟨fun h j ↦ div_nonneg (h j) hn.le, fun h j ↦ by
      have := mul_nonneg (h j) hn.le
      rwa [div_mul_cancel₀ _ hn.ne'] at this⟩
  unfold IsNashEq
  rw [← hnn]
  refine and_congr_right fun _ ↦ forall_congr' fun j ↦ ⟨fun h s hs ↦ ?_, fun h s hs ↦ ?_⟩
  · have := h (s * Fintype.card B) (mul_nonneg hs hn.le)
    rwa [hrev, hrev, hupd, mul_div_cancel_right₀ _ hn.ne'] at this
  · rw [hrev, hrev, hupd]
    exact h _ (div_nonneg hs hn.le)

end Rivalize
