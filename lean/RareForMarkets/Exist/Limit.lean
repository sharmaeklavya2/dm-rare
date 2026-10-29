module

public import RareForMarkets.Exist.Continuous
public import RareForMarkets.Defs.Market
public import RareForMarkets.Defs.Misc
public import RareForMarkets.Exist.Defs
import RareForMarkets.Exist.Demand
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Taking limits of RAREs of perturbed markets

The common part of the proofs of `\cref{thm:nonrival-rare-exists,thm:rival-rare-exists}`:
apply `\cref{thm:rare-exists-continuous}` to markets `M εₜ` with `εₜ = 1/(t+1)` and continuous
allocation rules `Aₜ`, and pass to convergent subsequences. The demand sets of all the markets
are encoded in a closed set `Γ` of triples `(ε, p, x)`.
-/

open Set Filter Topology

variable {B G : Type*} [Fintype B] [Fintype G]

public theorem limit_rare [DecidableEq G] [Nonempty B] [Nonempty G] (Mf : ℝ → Market B G)
    (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget) (r : Rivalry) (σ ρ L : G → ℝ)
    (hsec : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j, (Mf ε).IsSecurity r j (σ j) (ρ j))
    (hover : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ j, (Mf ε).IsOverpricing r j (σ j) (ρ j) (L j))
    (Γ : Set (ℝ × (G → ℝ) × (B → G → ℝ))) (hΓ : IsClosed Γ)
    (A : ∀ t : ℕ, (Mf (1 / ((t : ℝ) + 1))).AllocRule r)
    (hA : ∀ t, ContinuousOn (A t) (Ici 0))
    (hAΓ : ∀ (t : ℕ) p, 0 ≤ p → (1 / ((t : ℝ) + 1), p, A t p) ∈ Γ) :
    ∃ p ∈ scaledSimplex G ((Mf 0).beta r), ∃ x, (0, p, x) ∈ Γ ∧
      (∀ j, revenue p x j = Market.nu (B := B) r * p j ∧
        (Mf 0).beta r * ρ j ≤ p j * (Mf 0).totalBudget) ∧
      ∀ j qj, 0 ≤ qj → ∃ q : G → ℝ, 0 ≤ q ∧ q j = qj ∧ ∃ z, (0, q, z) ∈ Γ ∧
        revenue q z j ≤ p j * (Mf 0).kappa r * Market.nu (B := B) r ∧
        ∀ k ≠ j, Market.nu (B := B) r * p k ≤ revenue q z k := by
  set ε : ℕ → ℝ := fun t ↦ 1 / ((t : ℝ) + 1)
  have hε : ∀ t, ε t ∈ Icc (0 : ℝ) 1 := fun t ↦
    ⟨by positivity, (div_le_one (by positivity)).mpr (by simp)⟩
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set β := (Mf 0).beta r
  set κ := (Mf 0).kappa r
  set ν := Market.nu (B := B) r
  have hβ : ∀ t : ℕ, (Mf (1 / ((t : ℝ) + 1))).beta r = β :=
    fun t ↦ (Mf _).beta_congr (hb _) r
  have hκ : ∀ t : ℕ, (Mf (1 / ((t : ℝ) + 1))).kappa r = κ :=
    fun t ↦ (Mf _).kappa_congr (hb _) r
  have hB : ∀ t : ℕ, (Mf (1 / ((t : ℝ) + 1))).totalBudget = (Mf 0).totalBudget :=
    fun t ↦ (Mf _).totalBudget_congr (hb _)
  -- RAREs of the perturbed markets.
  have H := fun t ↦ (A t).rare_exists_continuous_aux (hA t) σ ρ L
    (hsec _ (hε t)) (hover _ (hε t))
  choose ps hpsS hps using H
  simp only [hβ, hκ, hB] at hpsS hps
  have hps0 : ∀ t, 0 ≤ ps t := fun t ↦ (hpsS t).1
  -- Allocations lie in the unit cube.
  have hcube : ∀ t q, 0 ≤ q → A t q ∈ Icc (0 : B → G → ℝ) 1 := fun t q hq ↦
    mem_Icc_iff_cube.mpr fun i ↦
      ((Mf (ε t)).dem_subset_nonRivalAff r q ((A t).mem_dem q hq) i).1
  -- Pass to a subsequence along which `(pₜ, Aₜ(pₜ))` converges.
  obtain ⟨⟨p, x⟩, -, φ, hφ, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq (x := fun t ↦ (ps t, A t (ps t)))
      (s := Icc (0 : G → ℝ) (fun _ ↦ β) ×ˢ Icc (0 : B → G → ℝ) 1)
      fun t ↦ ⟨⟨hps0 t, le_of_mem_scaledSimplex (hpsS t)⟩, hcube t _ (hps0 t)⟩
  have hplim : Tendsto (fun n ↦ ps (φ n)) atTop (𝓝 p) := (continuous_fst.tendsto _).comp hlim
  have hxlim : Tendsto (fun n ↦ A (φ n) (ps (φ n))) atTop (𝓝 x) :=
    (continuous_snd.tendsto _).comp hlim
  have hεφ : Tendsto (fun n ↦ ε (φ n)) atTop (𝓝 0) := hεlim.comp hφ.tendsto_atTop
  have hpcoord : ∀ k, Tendsto (fun n ↦ ps (φ n) k) atTop (𝓝 (p k)) :=
    fun k ↦ ((continuous_apply k).tendsto _).comp hplim
  refine ⟨p, (isClosed_scaledSimplex β).mem_of_tendsto hplim
    (Eventually.of_forall fun n ↦ hpsS (φ n)), x,
    hΓ.mem_of_tendsto (hεφ.prodMk_nhds (hplim.prodMk_nhds hxlim))
      (Eventually.of_forall fun n ↦ hAΓ _ _ (hps0 _)), fun j ↦ ⟨?_, ?_⟩, fun j qj hqj ↦ ?_⟩
  · -- `R_j(p, x) = ν pⱼ`
    have h1 : Tendsto (fun n ↦ revenue (ps (φ n)) (A (φ n) (ps (φ n))) j) atTop
        (𝓝 (revenue p x j)) :=
      ((continuous_revenue j).tendsto _).comp (hplim.prodMk_nhds hxlim)
    have h2 : Tendsto (fun n ↦ revenue (ps (φ n)) (A (φ n) (ps (φ n))) j) atTop
        (𝓝 (ν * p j)) := by
      simp only [fun n ↦ show revenue (ps (φ n)) (A (φ n) (ps (φ n))) j = _ from
        (hps (φ n) j).1.1]
      exact (hpcoord j).const_mul ν
    exact tendsto_nhds_unique h1 h2
  · -- the lower bound
    exact ge_of_tendsto ((hpcoord j).mul_const _)
      (Eventually.of_forall fun n ↦ (hps (φ n) j).1.2)
  -- The responses to the deviation `qj`.
  choose qs hqsj hqsk hRj hRk using fun n ↦ (hps (φ n) j).2 qj hqj
  have hqs0 : ∀ n, 0 ≤ qs n := fun n k ↦ by
    by_cases hk : k = j
    · rw [hk, hqsj]; exact hqj
    · exact (hps0 _ k).trans (hqsk n k hk).1
  set Lq : G → ℝ := fun k ↦ max (L k) qj
  have hqsL : ∀ n, qs n ∈ Icc (0 : G → ℝ) Lq := fun n ↦ ⟨hqs0 n, fun k ↦ by
    by_cases hk : k = j
    · rw [hk, hqsj]; exact le_max_right _ _
    · exact (hqsk n k hk).2.trans (le_max_left _ _)⟩
  obtain ⟨⟨q, z⟩, -, ψ, hψ, hlim'⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
      (x := fun n ↦ (qs n, A (φ n) (qs n)))
      (s := Icc (0 : G → ℝ) Lq ×ˢ Icc (0 : B → G → ℝ) 1)
      fun n ↦ ⟨hqsL n, hcube _ _ (hqs0 n)⟩
  have hqlim : Tendsto (fun n ↦ qs (ψ n)) atTop (𝓝 q) := (continuous_fst.tendsto _).comp hlim'
  have hzlim : Tendsto (fun n ↦ A (φ (ψ n)) (qs (ψ n))) atTop (𝓝 z) :=
    (continuous_snd.tendsto _).comp hlim'
  have hpcoord' : ∀ k, Tendsto (fun n ↦ ps (φ (ψ n)) k) atTop (𝓝 (p k)) :=
    fun k ↦ (hpcoord k).comp hψ.tendsto_atTop
  have hrev : ∀ k, Tendsto (fun n ↦ revenue (qs (ψ n)) (A (φ (ψ n)) (qs (ψ n))) k) atTop
      (𝓝 (revenue q z k)) := fun k ↦
    ((continuous_revenue k).tendsto _).comp (hqlim.prodMk_nhds hzlim)
  refine ⟨q, ?_, ?_, z, ?_, ?_, fun k hk ↦ ?_⟩
  · exact isClosed_Ici.mem_of_tendsto hqlim (Eventually.of_forall fun n ↦ hqs0 (ψ n))
  · have := ((continuous_apply j).tendsto _).comp hqlim
    simp only [Function.comp_def, hqsj] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  · exact hΓ.mem_of_tendsto ((hεφ.comp hψ.tendsto_atTop).prodMk_nhds
      (hqlim.prodMk_nhds hzlim)) (Eventually.of_forall fun n ↦ hAΓ _ _ (hqs0 _))
  · exact le_of_tendsto_of_tendsto' (hrev j) (((hpcoord' j).mul_const _).mul_const _)
      fun n ↦ hRj (ψ n)
  · exact le_of_tendsto_of_tendsto' ((hpcoord' k).const_mul _) (hrev k)
      fun n ↦ (hRk (ψ n) k hk).1
