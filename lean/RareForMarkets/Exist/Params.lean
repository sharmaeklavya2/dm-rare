module

public import RareForMarkets.Exist.Defs
public import RareForMarkets.Defs.Market
import RareForMarkets.Exist.Accounting
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field

/-!
# Security and overpricing parameters (`\cref{sec:exist-extra:market-params}`)

We prove `\cref{thm:security,thm:overpricing}` uniformly over a family of markets `M ε`,
`ε ∈ [0, 1]`, with the same budgets and jointly continuous utilities.
This gives `\cref{thm:robust-params}`, and the constant family gives the plain versions.
-/

open Set

variable {B G : Type*} [Fintype B] [Fintype G]

omit [Fintype G] in
private theorem add_single_mem_cube' [DecidableEq G] {z : G → ℝ} (hz : z ∈ cube G) {k : G}
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : z k ≤ 1 - η) : z + Pi.single k η ∈ cube G := by
  have h0 : ∀ l, 0 ≤ z l := hz.1
  have h1 : ∀ l, z l ≤ 1 := hz.2
  refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩ <;> by_cases hl : l = k
  · subst hl; simp; linarith [h0 l]
  · simpa [hl] using h0 l
  · subst hl; simp; linarith
  · simpa [hl] using h1 l

omit [Fintype G] in
/-- `\label{thm:uniform-utility-improvement}` -/
private theorem uniform_utility_improvement [Finite G] [DecidableEq G] {v : ℝ × (G → ℝ) → ℝ}
    (hv : ContinuousOn v (Icc 0 1 ×ˢ cube G))
    (hmono : ∀ ε, StrictMonoOn (fun z ↦ v (ε, z)) (cube G))
    (k : G) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ δ > 0, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ cube G, ∀ y ∈ cube G, z k ≤ 1 - η →
      (∀ l, |y l - (z + Pi.single k η : G → ℝ) l| < δ) → v (ε, z) < v (ε, y) := by
  have := Fintype.ofFinite G
  let K := Icc (0 : ℝ) 1 ×ˢ cube G
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let K' := Icc (0 : ℝ) 1 ×ˢ (cube G ∩ {z | z k ≤ 1 - η})
  have hK' : IsCompact K' := isCompact_Icc.prod
    (isCompact_Icc.inter_right (isClosed_le (continuous_apply k) continuous_const))
  let w : ℝ × (G → ℝ) → ℝ × (G → ℝ) := fun x ↦ (x.1, x.2 + Pi.single k η)
  have hw : MapsTo w K' K := fun x hx ↦
    ⟨hx.1, add_single_mem_cube' hx.2.1 hη.le hx.2.2⟩
  have hK'K : K' ⊆ K := fun x hx ↦ ⟨hx.1, hx.2.1⟩
  let g : ℝ × (G → ℝ) → ℝ := fun x ↦ v (w x) - v x
  have hg : ContinuousOn g K' :=
    (hv.comp (by fun_prop) hw).sub (hv.mono hK'K)
  have hne : K'.Nonempty := ⟨(0, 0), ⟨by simp, ⟨le_rfl, fun _ ↦ zero_le_one⟩, by
    simp only [mem_setOf_eq, Pi.zero_apply]; linarith⟩⟩
  -- The minimum improvement `γ > 0`.
  obtain ⟨x0, hx0, hmin⟩ := hK'.exists_isMinOn hne hg
  have hγ : 0 < g x0 := by
    have := hmono x0.1 hx0.2.1 (hw hx0).2 (by
      refine Pi.lt_def.mpr ⟨fun l ↦ ?_, k, by simp [w, hη]⟩
      by_cases hl : l = k
      · subst hl; simp [w, hη.le]
      · simp [w, hl])
    simp only [g, w]
    linarith
  obtain ⟨δ, hδ, hδv⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hv) (g x0) hγ
  refine ⟨δ, hδ, fun ε hε z hz y hy hzk hyz ↦ ?_⟩
  have hzK' : (ε, z) ∈ K' := ⟨hε, hz, hzk⟩
  have hdist : dist (ε, y) (w (ε, z)) < δ := by
    rw [Prod.dist_eq, dist_self, max_lt_iff]
    refine ⟨hδ, (dist_pi_lt_iff hδ).mpr fun l ↦ ?_⟩
    rw [Real.dist_eq]
    exact hyz l
  have h1 := hδv (ε, y) ⟨hε, hy⟩ (w (ε, z)) (hw hzK') hdist
  rw [Real.dist_eq, abs_lt] at h1
  have h2 : g x0 ≤ g (ε, z) := hmin hzK'
  simp only [g] at h2
  linarith [h1.1]

omit [Fintype G] in
private theorem sum_update_apply [DecidableEq B] (x : B → G → ℝ) (i : B) (y : G → ℝ) (l : G) :
    ∑ k, Function.update x i y k l = ∑ k, x k l - x i l + y l := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ (fun k ↦ x k l) (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl fun k hk ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]]
  ring

namespace Market

variable (M : Market B G)

/-- A strictly better affordable bundle for a single buyer contradicts demand. (In the
rivalrous setting, the modified allocation must also respect the stock constraints.) -/
private theorem not_improve {r : Rivalry} {p : G → ℝ} {x : B → G → ℝ}
    (hx : x ∈ M.dem r p) {i : B} {y : G → ℝ} (hy : y ∈ M.budgetSet i p)
    (hu : M.util i (x i) < M.util i y)
    (hstock : r = .rival → ∀ l, ∑ k, x k l - x i l + y l ≤ 1) : False := by
  classical
  cases r
  · obtain ⟨⟨_, hbud⟩, hPO⟩ := hx
    refine hPO (Function.update x i y) ⟨fun l ↦ ?_, fun k ↦ ?_⟩
      ⟨fun k ↦ ?_, i, by simpa using hu⟩
    · rw [sum_update_apply]; exact hstock rfl l
    · by_cases hk : k = i
      · subst hk; simpa using hy
      · simpa [hk] using hbud k
    · by_cases hk : k = i
      · subst hk; simpa using hu.le
      · simp [hk]
  · exact (hu.trans_le ((hx i).2 hy)).false

end Market

/-! ### Families of markets -/

variable [DecidableEq G]

/-- `\label{thm:security}`, uniformly over a family of markets. -/
private theorem exists_security_family [Nonempty B] (Mf : ℝ → Market B G)
    (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget)
    (hcont : ∀ i, ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (Mf x.1).util i x.2)
      (Icc 0 1 ×ˢ cube G))
    (r : Rivalry) :
    ∃ σ ρ : G → ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j, (Mf ε).IsSecurity r j (σ j) (ρ j) := by
  classical
  let i0 := Classical.arbitrary B
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : G → ℝ, (∀ j, 0 < δ j) ∧ ∀ j, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ z ∈ cube G, ∀ y ∈ cube G, z j ≤ 1 - 1 / 4 →
      (∀ l, |y l - (z + Pi.single j (1 / 4) : G → ℝ) l| < δ j) →
        (Mf ε).util i0 z < (Mf ε).util i0 y := by
    choose δ hδpos hδ using fun j ↦ uniform_utility_improvement (hcont i0)
      (fun ε ↦ (Mf ε).util_strictMonoOn i0) j (η := 1 / 4) (by norm_num) (by norm_num)
    exact ⟨δ, hδpos, hδ⟩
  set b1 := (Mf 0).budget i0
  have hb1 : 0 < b1 := (Mf 0).budget_pos i0
  set μ : G → ℝ := fun j ↦ min 1 (δ j)
  have hμ : ∀ j, 0 < μ j := fun j ↦ lt_min one_pos (hδpos j)
  have hμ1 : ∀ j, μ j ≤ 1 := fun j ↦ min_le_left _ _
  have hμδ : ∀ j, μ j ≤ δ j := fun j ↦ min_le_right _ _
  refine ⟨fun j ↦ b1 * μ j, fun j ↦ b1 * μ j / 4, fun ε hε j ↦
    ⟨mul_pos hb1 (hμ j), by have := mul_pos hb1 (hμ j); positivity, ?_⟩⟩
  intro q hq x hx
  set P := Function.update q j (b1 * μ j)
  have hPj : P j = b1 * μ j := by simp [P]
  by_contra hlt
  push Not at hlt
  have hσ := mul_pos hb1 (hμ j)
  have hsum : ∑ i, x i j < 1 / 4 := by
    have : P j * ∑ i, x i j < P j * (1 / 4) := by
      change revenue P x j < _ at hlt
      simp only [revenue] at hlt
      rw [hPj] at hlt ⊢
      linarith
    exact lt_of_mul_lt_mul_left this (hPj ▸ hσ.le)
  have hxa := (Mf ε).dem_subset_nonRivalAff r P hx
  obtain ⟨⟨hx0, hx1⟩, hcost⟩ := hxa i0
  have hx0 : ∀ l, 0 ≤ x i0 l := hx0
  have hx1 : ∀ l, x i0 l ≤ 1 := hx1
  have hxj : x i0 j ≤ ∑ i, x i j :=
    Finset.single_le_sum (fun i _ ↦ ((hxa i).1.1 j)) (Finset.mem_univ i0)
  set lam := μ j / 4
  have hlam0 : 0 < lam := div_pos (hμ j) (by norm_num)
  have hlam1 : lam ≤ 1 / 4 := by simp only [lam]; linarith [hμ1 j]
  set y : G → ℝ := (1 - lam) • x i0 + Pi.single j (1 / 4)
  have hy : ∀ l, y l = (1 - lam) * x i0 l + if l = j then 1 / 4 else 0 := fun l ↦ by
    by_cases hl : l = j
    · subst hl; simp [y]
    · simp [y, hl]
  have hycube : y ∈ cube G := by
    refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩ <;> simp only [Pi.zero_apply, Pi.one_apply, hy] <;>
      split_ifs with hl <;> (try subst hl) <;> nlinarith [hx0 l, hx1 l, hxj, hsum]
  have hycost : ∑ l, P l * y l = (1 - lam) * ∑ l, P l * x i0 l + P j * (1 / 4) := by
    simp only [hy, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun l _ ↦ by ring
    · simp
  have hbud : (Mf ε).budget i0 = b1 := by rw [hb ε]
  rw [hbud] at hcost
  refine (Mf ε).not_improve hx (i := i0) (y := y) ⟨hycube, ?_⟩ ?_ ?_
  · rw [hycost, hbud, hPj]
    have : (1 - lam) * ∑ l, P l * x i0 l ≤ (1 - lam) * b1 :=
      mul_le_mul_of_nonneg_left hcost (by linarith)
    simp only [lam] at this ⊢
    linarith
  · refine hδ j ε hε (x i0) ⟨hx0, hx1⟩ y hycube (by linarith) fun l ↦ ?_
    have : y l - (x i0 + Pi.single j (1 / 4) : G → ℝ) l = -(lam * x i0 l) := by
      rw [hy]; by_cases hl : l = j
      · subst hl; simp; ring
      · simp [hl]; ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg hlam0.le (hx0 l))]
    calc lam * x i0 l ≤ lam * 1 := mul_le_mul_of_nonneg_left (hx1 l) hlam0.le
      _ < δ j := by simp only [lam]; linarith [hμδ j, hδpos j]
  · intro hr l
    subst hr
    have hstock : ∑ i, x i l ≤ 1 := hx.1.1 l
    rw [hy]
    by_cases hl : l = j
    · subst hl; simp only [if_true]; nlinarith [hx0 l]
    · simp only [hl, if_false]; nlinarith [hx0 l]

omit [DecidableEq G] in
/-- `\label{thm:overpricing}`, uniformly over a family of markets. -/
private theorem exists_overpricing_family [Nonempty B] (Mf : ℝ → Market B G)
    (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget)
    (hcont : ∀ i, ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (Mf x.1).util i x.2)
      (Icc 0 1 ×ˢ cube G))
    (r : Rivalry) (σ ρ : G → ℝ) (hρ : ∀ j, 0 < ρ j) :
    ∃ L : G → ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j, (Mf ε).IsOverpricing r j (σ j) (ρ j) (L j) := by
  classical
  let i0 := Classical.arbitrary B
  set M0 := Mf 0
  set Bt := M0.totalBudget
  set κ := M0.kappa r
  set n : ℝ := (Fintype.card B : ℝ)
  have hBt : 0 < Bt := M0.totalBudget_pos
  have hκ : 0 < κ := M0.kappa_pos r
  have hn1 : 1 ≤ n := by simpa [n] using Fintype.card_pos (α := B)
  have hn : 0 < n := by linarith
  set a : G → ℝ := fun j ↦ ρ j / (2 * κ)
  have ha : ∀ j, 0 < a j := fun j ↦ div_pos (hρ j) (by positivity)
  set η : G → ℝ := fun j ↦ min (1 / 2) (a j / (2 * n * Bt))
  have hη : ∀ j, 0 < η j := fun j ↦ lt_min (by norm_num) (by have := ha j; positivity)
  have hη1 : ∀ j, η j ≤ 1 := fun j ↦ (min_le_left _ _).trans (by norm_num)
  have hηa : ∀ j, Bt * (2 * η j) ≤ a j / n := by
    intro j
    have h : η j * (2 * n * Bt) ≤ a j :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    rw [le_div_iff₀ hn]
    linarith
  choose d hdpos hd using fun (i : B) (k : G) (j : G) ↦ uniform_utility_improvement (hcont i)
    (fun ε ↦ (Mf ε).util_strictMonoOn i) k (hη j) (hη1 j)
  have hne : ∀ j, (Finset.univ ×ˢ Finset.univ : Finset (B × G)).Nonempty :=
    fun j ↦ ⟨(i0, j), by simp⟩
  set δ : G → ℝ := fun j ↦ (Finset.univ ×ˢ Finset.univ).inf' (hne j) (fun ik ↦ d ik.1 ik.2 j)
  have hδ : ∀ j, 0 < δ j := fun j ↦ (Finset.lt_inf'_iff _).mpr fun ik _ ↦ hdpos _ _ _
  have hδd : ∀ i k j, δ j ≤ d i k j := fun i k j ↦
    Finset.inf'_le (fun ik : B × G ↦ d ik.1 ik.2 j) (by simp : (i, k) ∈ Finset.univ ×ˢ Finset.univ)
  refine ⟨fun j ↦ max (max Bt (σ j)) (Bt / δ j), fun ε hε j ↦ ?_⟩
  have hBε : (Mf ε).totalBudget = Bt := (Mf ε).totalBudget_congr (hb ε)
  have hκε : (Mf ε).kappa r = κ := (Mf ε).kappa_congr (hb ε) r
  refine ⟨by rw [hBε]; exact le_max_left _ _, ?_⟩
  intro q hq x hx hqj hqk ⟨k, hkj, hqkB⟩
  rw [hκε]
  rw [hBε] at hqk hqkB
  have hbud : ∀ i, (Mf ε).budget i = M0.budget i := fun i ↦ by rw [hb ε]
  have hbB : ∀ i, M0.budget i ≤ Bt := fun i ↦
    Finset.single_le_sum (fun i _ ↦ (M0.budget_pos i).le) (Finset.mem_univ i)
  have hq0 : ∀ l, 0 ≤ q l := hq
  have hqjL : Bt / δ j < q j := (le_max_right _ _).trans_lt hqj
  have hqjB : Bt < q j := (le_max_left _ _ |>.trans (le_max_left _ _)).trans_lt hqj
  have hqj0 : 0 < q j := hBt.trans hqjB
  by_contra hlt
  push Not at hlt
  -- `R_j(q, x) > a_j`
  have hR : a j < ∑ i, q j * x i j := by
    rw [← Finset.mul_sum]
    change ρ j < 2 * κ * (q j * ∑ i, x i j) at hlt
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hxa := (Mf ε).dem_subset_nonRivalAff r q hx
  have hx0 : ∀ i l, 0 ≤ x i l := fun i l ↦ (hxa i).1.1 l
  have hx1 : ∀ i l, x i l ≤ 1 := fun i l ↦ (hxa i).1.2 l
  have hcost : ∀ i, ∑ l, q l * x i l ≤ M0.budget i := fun i ↦ hbud i ▸ (hxa i).2
  -- A buyer who spends a lot on good `j`
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, a j / n < q j * x i j := by
    refine Finset.exists_lt_of_sum_lt ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hn.ne']
    exact hR
  have hpair : ∀ i', q k * x i' k + q j * x i' j ≤ ∑ l, q l * x i' l := fun i' ↦ by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l ↦ q l * x i' l)
      (Finset.subset_univ {k, j}) fun l _ _ ↦ mul_nonneg (hq0 l) (hx0 i' l)
    rwa [Finset.sum_pair hkj] at h
  have hxij : x i j < δ j := by
    have h1 : q j * x i j ≤ Bt := by
      linarith [hpair i, hcost i, hbB i, mul_nonneg (hq0 k) (hx0 i k)]
    have h2 : Bt < q j * δ j := (div_lt_iff₀ (hδ j)).mp hqjL
    nlinarith
  -- There is room for `η` more of good `k`.
  have hroom : r = .rival → ∑ i', x i' k + 2 * η j ≤ 1 := by
    intro hr
    have h1 : Bt * ∑ i', x i' k ≤ Bt - ∑ i', q j * x i' j := by
      have hsumB : ∑ i', M0.budget i' = Bt := rfl
      have := Finset.sum_le_sum fun i' (_ : i' ∈ Finset.univ) ↦ (hpair i').trans (hcost i')
      rw [Finset.sum_add_distrib, hsumB] at this
      simp only [hqkB] at this
      rw [Finset.mul_sum]
      linarith
    have h2 : a j / n ≤ a j := div_le_self (ha j).le hn1
    have : Bt * (∑ i', x i' k + 2 * η j) < Bt * 1 := by nlinarith [hηa j]
    exact (lt_of_mul_lt_mul_left this hBt.le).le
  have hroom' : x i k + 2 * η j ≤ 1 := by
    cases r
    · have := Finset.single_le_sum (fun i' _ ↦ hx0 i' k) (Finset.mem_univ i)
      linarith [hroom rfl]
    · have h1 : Bt * x i k ≤ M0.budget i - q j * x i j := by
        rw [← hqkB]; linarith [hpair i, hcost i]
      have : Bt * (x i k + 2 * η j) < Bt * 1 := by nlinarith [hηa j, hbB i]
      exact (lt_of_mul_lt_mul_left this hBt.le).le
  -- Replace buyer `i`'s purchase of good `j` by `η` units of good `k`.
  set y : G → ℝ := x i - Pi.single j (x i j) + Pi.single k (η j)
  have hy : ∀ l, y l = x i l - (if l = j then x i j else 0) + if l = k then η j else 0 :=
    fun l ↦ by simp [y, Pi.single_apply]
  have hyj : y j = 0 := by rw [hy]; simp [hkj.symm]
  have hyk : y k = x i k + η j := by rw [hy]; simp [hkj]
  have hyl : ∀ l, l ≠ j → l ≠ k → y l = x i l := fun l hlj hlk ↦ by rw [hy]; simp [hlj, hlk]
  have hycube : y ∈ cube G := by
    refine ⟨fun l ↦ ?_, fun l ↦ ?_⟩ <;> simp only [Pi.zero_apply, Pi.one_apply]
    · by_cases hlj : l = j
      · rw [hlj, hyj]
      by_cases hlk : l = k
      · rw [hlk, hyk]; linarith [hx0 i k, hη j]
      · rw [hyl l hlj hlk]; exact hx0 i l
    · by_cases hlj : l = j
      · rw [hlj, hyj]; norm_num
      by_cases hlk : l = k
      · rw [hlk, hyk]; linarith [hη j]
      · rw [hyl l hlj hlk]; exact hx1 i l
  have hycost : ∑ l, q l * y l = ∑ l, q l * x i l - q j * x i j + q k * η j := by
    simp only [hy, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Mf ε).not_improve hx (i := i) (y := y) ⟨hycube, ?_⟩ ?_ ?_
  · rw [hycost, hbud, hqkB]
    have := hηa j
    have : Bt * η j ≤ a j / n := by nlinarith [hBt, hη j]
    linarith [hcost i]
  · refine hd i k j ε hε (x i) ⟨fun l ↦ hx0 i l, fun l ↦ hx1 i l⟩ y hycube
      (by linarith [hη j]) fun l ↦ ?_
    have : y l - (x i + Pi.single k (η j) : G → ℝ) l = -(if l = j then x i j else 0) := by
      rw [hy]; by_cases hlk : l = k <;> simp [hlk]
    rw [this, abs_neg]
    split_ifs
    · rw [abs_of_nonneg (hx0 i j)]; exact hxij.trans_le (hδd i k j)
    · simpa using hdpos i k j
  · intro hr l
    have hroom := hroom hr
    subst hr
    have hstock : ∑ i', x i' l ≤ 1 := hx.1.1 l
    by_cases hlj : l = j
    · rw [hlj, hyj]; rw [hlj] at hstock; linarith [hx0 i j]
    by_cases hlk : l = k
    · rw [hlk, hyk]; linarith [hη j]
    · rw [hyl l hlj hlk]; linarith

/-- `\label{thm:robust-params}`: security and overpricing parameters for a family of markets
with the same budgets and jointly continuous utilities. -/
public theorem exists_params_family [Nonempty B] (Mf : ℝ → Market B G)
    (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget)
    (hcont : ∀ i, ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (Mf x.1).util i x.2)
      (Icc 0 1 ×ˢ cube G))
    (r : Rivalry) :
    ∃ σ ρ L : G → ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      (∀ j, (Mf ε).IsSecurity r j (σ j) (ρ j)) ∧
        ∀ j, (Mf ε).IsOverpricing r j (σ j) (ρ j) (L j) := by
  obtain ⟨σ, ρ, hsec⟩ := exists_security_family Mf hb hcont r
  obtain ⟨L, hover⟩ := exists_overpricing_family Mf hb hcont r σ ρ
    fun j ↦ (hsec 0 ⟨le_rfl, zero_le_one⟩ j).ρ_pos
  exact ⟨σ, ρ, L, fun ε hε ↦ ⟨hsec ε hε, hover ε hε⟩⟩

/-- `\label{thm:security}` and `\label{thm:overpricing}`. -/
public theorem Market.exists_params [Nonempty B] (M : Market B G) (r : Rivalry) :
    ∃ σ ρ L : G → ℝ, (∀ j, M.IsSecurity r j (σ j) (ρ j)) ∧
      ∀ j, M.IsOverpricing r j (σ j) (ρ j) (L j) := by
  obtain ⟨σ, ρ, L, h⟩ := exists_params_family (fun _ ↦ M) (fun _ ↦ rfl)
    (fun i ↦ (M.util_continuousOn i).comp continuousOn_snd fun x hx ↦ hx.2) r
  exact ⟨σ, ρ, L, h 0 ⟨le_rfl, zero_le_one⟩⟩

