module

public import RareForMarkets.Defs.Market
public import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Limits of affordable allocations and maximizers (`\cref{sec:exist-extra:limits}`)

We work with a family of objectives `V(ε, ·)`, `ε ∈ [0, 1]`, maximized over the feasible sets
`F(p) = {x ∈ Y : pᵀxᵢ ≤ bᵢ ∀ i}`, where `Y ⊆ [0, 1]^{n × m}` is closed under shrinking
individual bundles. (`Y = [0, 1]^{n × m}` gives `Aff^NR`, and adding the stock constraints
gives `Aff^R`.) The main results are:

* `isClosed_argmaxGraph`: the graph `{(ε, p, x) : x ∈ argmax_{F(p)} V(ε, ·)}` is closed.
  This is `\cref{thm:affordable-limits,thm:maximizer-limits}` in one statement.
* `exists_continuous_argmax`: if `V(ε, ·)` is strictly concave, the maximizer is unique
  and depends continuously on `p`.
-/

open Set Filter Topology

variable {B G : Type*} [Fintype G]

/-- The feasible allocations `F(p) = {x ∈ Y : pᵀxᵢ ≤ bᵢ ∀ i}`. -/
@[expose] public def feasible (Y : Set (B → G → ℝ)) (b : B → ℝ) (p : G → ℝ) : Set (B → G → ℝ) :=
  {x | x ∈ Y ∧ ∀ i, ∑ j, p j * x i j ≤ b i}

/-- Scale each buyer's bundle down (by `bᵢ / max(bᵢ, pᵀyᵢ)`) to make it affordable. -/
private noncomputable def shrink (b : B → ℝ) (p : G → ℝ) (y : B → G → ℝ) : B → G → ℝ :=
  fun i ↦ (b i / max (b i) (∑ j, p j * y i j)) • y i

/-- `Y` is closed under scaling individual bundles by factors in `[0, 1]`. -/
@[expose] public def ShrinkClosed (Y : Set (B → G → ℝ)) : Prop :=
  ∀ x ∈ Y, ∀ c : B → ℝ, (∀ i, c i ∈ Icc (0 : ℝ) 1) → (fun i ↦ c i • x i) ∈ Y

/-- The graph of the argmax correspondence. -/
@[expose] public def argmaxGraph (Y : Set (B → G → ℝ)) (b : B → ℝ) (V : ℝ × (B → G → ℝ) → ℝ) :
    Set (ℝ × (G → ℝ) × (B → G → ℝ)) :=
  {e | e.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ e.2.1 ∧ e.2.2 ∈ feasible Y b e.2.1 ∧
    ∀ y ∈ feasible Y b e.2.1, V (e.1, y) ≤ V (e.1, e.2.2)}

variable {Y : Set (B → G → ℝ)} {b : B → ℝ}

private theorem shrink_mem (hY : ShrinkClosed Y) (hb : ∀ i, 0 < b i) (p : G → ℝ) {y : B → G → ℝ}
    (hy : y ∈ Y) : shrink b p y ∈ feasible Y b p := by
  have hmax : ∀ i, 0 < max (b i) (∑ j, p j * y i j) := fun i ↦ lt_max_of_lt_left (hb i)
  refine ⟨hY y hy _ fun i ↦ ⟨div_nonneg (hb i).le (hmax i).le,
    (div_le_one (hmax i)).mpr (le_max_left _ _)⟩, fun i ↦ ?_⟩
  simp only [shrink, Pi.smul_apply, smul_eq_mul, mul_left_comm (p _), ← Finset.mul_sum]
  rcases le_total (∑ j, p j * y i j) (b i) with h | h
  · rw [max_eq_left h, div_self (hb i).ne', one_mul]; exact h
  · rw [max_eq_right h, div_mul_cancel₀ _ (by linarith [hb i])]

private theorem shrink_eq (hb : ∀ i, 0 < b i) {p : G → ℝ} {y : B → G → ℝ}
    (hy : y ∈ feasible Y b p) : shrink b p y = y := by
  funext i
  simp [shrink, max_eq_left (hy.2 i), div_self (hb i).ne']

private theorem continuous_shrink (hb : ∀ i, 0 < b i) (y : B → G → ℝ) :
    Continuous fun p ↦ shrink b p y := by
  refine continuous_pi fun i ↦ Continuous.smul ?_ continuous_const
  exact continuous_const.div (continuous_const.max (by fun_prop))
    fun p ↦ (lt_max_of_lt_left (hb i)).ne'

private theorem isClosed_feasibleGraph (hYc : IsClosed Y) :
    IsClosed {e : ℝ × (G → ℝ) × (B → G → ℝ) |
      e.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ e.2.1 ∧ e.2.2 ∈ feasible Y b e.2.1} := by
  have h1 : IsClosed {e : ℝ × (G → ℝ) × (B → G → ℝ) | e.1 ∈ Icc (0 : ℝ) 1} :=
    isClosed_Icc.preimage continuous_fst
  have h2 : IsClosed {e : ℝ × (G → ℝ) × (B → G → ℝ) | 0 ≤ e.2.1} :=
    isClosed_le continuous_const (continuous_fst.comp continuous_snd)
  have h3 : IsClosed {e : ℝ × (G → ℝ) × (B → G → ℝ) | e.2.2 ∈ Y} :=
    hYc.preimage (continuous_snd.comp continuous_snd)
  have h4 : IsClosed
      {e : ℝ × (G → ℝ) × (B → G → ℝ) | ∀ i, ∑ j, e.2.1 j * e.2.2 i j ≤ b i} := by
    rw [setOf_forall]
    exact isClosed_iInter fun i ↦ isClosed_le (continuous_finsetSum _ fun j _ ↦
      ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
        (by fun_prop : Continuous fun e : ℝ × (G → ℝ) × (B → G → ℝ) ↦ e.2.2 i j))
      continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- `\label{thm:affordable-limits}` and `\label{thm:maximizer-limits}`:
the graph of the argmax correspondence is closed. -/
public theorem isClosed_argmaxGraph (hYc : IsClosed Y) (hY : ShrinkClosed Y) (hb : ∀ i, 0 < b i)
    {V : ℝ × (B → G → ℝ) → ℝ} (hV : ContinuousOn V (Icc 0 1 ×ˢ Y)) :
    IsClosed (argmaxGraph Y b V) := by
  set D := {e : ℝ × (G → ℝ) × (B → G → ℝ) |
      e.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ e.2.1 ∧ e.2.2 ∈ feasible Y b e.2.1}
  have hD : IsClosed D := isClosed_feasibleGraph hYc
  have hsub : argmaxGraph Y b V ⊆ D := fun e he ↦ ⟨he.1, he.2.1, he.2.2.1⟩
  refine isClosed_of_closure_subset fun e he ↦ ?_
  have heD : e ∈ D := hD.closure_subset_iff.mpr hsub he
  refine ⟨heD.1, heD.2.1, heD.2.2, fun y hy ↦ ?_⟩
  -- Compare against the shrunk version of `y`, which is feasible everywhere.
  have hC : IsClosed {e ∈ D | V (e.1, shrink b e.2.1 y) ≤ V (e.1, e.2.2)} := by
    have hc1 : ContinuousOn
        (fun e : ℝ × (G → ℝ) × (B → G → ℝ) ↦ (e.1, shrink b e.2.1 y)) D :=
      (continuous_fst.prodMk ((continuous_shrink hb y).comp
        (continuous_fst.comp continuous_snd))).continuousOn
    have hc2 : ContinuousOn (fun e : ℝ × (G → ℝ) × (B → G → ℝ) ↦ (e.1, e.2.2)) D :=
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
    exact hD.isClosed_le (hV.comp hc1 fun e he ↦ ⟨he.1, (shrink_mem hY hb e.2.1 hy.1).1⟩)
      (hV.comp hc2 fun e he ↦ ⟨he.1, he.2.2.1⟩)
  have hsubC : argmaxGraph Y b V ⊆ {e ∈ D | V (e.1, shrink b e.2.1 y) ≤ V (e.1, e.2.2)} :=
    fun e' he' ↦ ⟨hsub he', he'.2.2.2 _ (shrink_mem hY hb e'.2.1 hy.1)⟩
  have := (hC.closure_subset_iff.mpr hsubC he).2
  rwa [shrink_eq hb hy] at this

/-- Strictly concave functions have at most one maximizer on a convex set. -/
private theorem eq_of_isMaxOn_of_strictConcaveOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : StrictConcaveOn ℝ S f) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hmx : IsMaxOn f S x) (hmy : IsMaxOn f S y) : x = y := by
  by_contra hne
  have h1 : f y ≤ f x := hmx hy
  have h2 : f x ≤ f y := hmy hx
  have h := hf.2 hx hy hne (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (by norm_num)
  have h3 : f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤ f x :=
    hmx (hf.1 hx hy (by norm_num) (by norm_num) (by norm_num))
  simp only [smul_eq_mul] at h
  linarith

private theorem convex_feasible (hYcvx : Convex ℝ Y) (p : G → ℝ) : Convex ℝ (feasible Y b p) := by
  have : feasible Y b p = Y ∩ ⋂ i, {x : B → G → ℝ | ∑ j, p j * x i j ≤ b i} := by
    ext x; simp [feasible]
  rw [this]
  refine hYcvx.inter (convex_iInter fun i ↦ convex_halfSpace_le ?_ _)
  constructor
  · intro x y; simp [mul_add, Finset.sum_add_distrib]
  · intro c x; simp [Finset.mul_sum, mul_left_comm]

/-- If `V(ε₀, ·)` is continuous and strictly concave, then for every `p ≥ 0` there is a unique
maximizer `f(p)` over `F(p)`, and `f` is continuous (`\cref{thm:unique-nr-demand}` and
`\cref{thm:unique-rival-demand}`). -/
public theorem exists_continuous_argmax (hYc : IsClosed Y) (hY : ShrinkClosed Y) (hb : ∀ i, 0 < b i)
    (hYcube : Y ⊆ Icc 0 1) (hY0 : (0 : B → G → ℝ) ∈ Y) (hYcvx : Convex ℝ Y)
    {V : ℝ × (B → G → ℝ) → ℝ} (hV : ContinuousOn V (Icc 0 1 ×ˢ Y))
    {ε₀ : ℝ} (hε₀ : ε₀ ∈ Icc (0 : ℝ) 1) (hconc : StrictConcaveOn ℝ Y fun x ↦ V (ε₀, x)) :
    (∀ p : G → ℝ, 0 ≤ p → ∃! x, (ε₀, p, x) ∈ argmaxGraph Y b V) ∧
      ∃ f : (G → ℝ) → (B → G → ℝ), (∀ p, 0 ≤ p → (ε₀, p, f p) ∈ argmaxGraph Y b V) ∧
        ContinuousOn f (Ici 0) := by
  have hYk : IsCompact Y := isCompact_Icc.of_isClosed_subset hYc hYcube
  have hF : ∀ p, IsCompact (feasible Y b p) := fun p ↦ by
    refine hYk.of_isClosed_subset ?_ fun x hx ↦ hx.1
    have : feasible Y b p = Y ∩ ⋂ i, {x : B → G → ℝ | ∑ j, p j * x i j ≤ b i} := by
      ext x; simp [feasible]
    rw [this]
    exact hYc.inter (isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const)
  have hVε : ContinuousOn (fun x ↦ V (ε₀, x)) Y :=
    hV.comp (by fun_prop) fun x hx ↦ ⟨hε₀, hx⟩
  have huniq : ∀ p : G → ℝ, 0 ≤ p → ∃! x, (ε₀, p, x) ∈ argmaxGraph Y b V := by
    intro p hp
    obtain ⟨x, hx, hmax⟩ := (hF p).exists_isMaxOn ⟨0, hY0, fun i ↦ by simp [(hb i).le]⟩
      (hVε.mono fun x hx ↦ hx.1)
    refine ⟨x, ⟨hε₀, hp, hx, fun y hy ↦ hmax hy⟩, fun y hy ↦ ?_⟩
    exact eq_of_isMaxOn_of_strictConcaveOn
      (hconc.subset (fun x hx ↦ hx.1) (convex_feasible hYcvx p)) hy.2.2.1 hx
      (fun z hz ↦ hy.2.2.2 z hz) hmax
  refine ⟨huniq, ?_⟩
  classical
  let f : (G → ℝ) → (B → G → ℝ) := fun p ↦
    if hp : 0 ≤ p then (huniq p hp).exists.choose else 0
  have hf : ∀ p, 0 ≤ p → (ε₀, p, f p) ∈ argmaxGraph Y b V := fun p hp ↦ by
    simp only [f, hp, dif_pos]; exact (huniq p hp).exists.choose_spec
  refine ⟨f, hf, fun p hp ↦ ?_⟩
  have hp : 0 ≤ p := hp
  -- `f` takes values in the compact set `Y`, and its only cluster point at `p` is `f p`.
  refine hYk.tendsto_nhds_of_unique_mapClusterPt
    (eventually_nhdsWithin_of_forall fun p' hp' ↦ (hf p' hp').2.2.1.1) fun x hxY hx ↦ ?_
  have hmem : (ε₀, p, x) ∈ argmaxGraph Y b V := by
    refine (isClosed_argmaxGraph hYc hY hb hV).closure_subset
      (mem_closure_iff_nhds.mpr fun t ht ↦ ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp ht
    obtain ⟨v1, hv1, w, hw, hvw⟩ := mem_nhds_prod_iff.mp hv
    have hev1 : ∀ᶠ p' in 𝓝[Ici 0] p, p' ∈ v1 := nhdsWithin_le_nhds hv1
    have hev2 : ∀ᶠ p' in 𝓝[Ici 0] p, p' ∈ Ici (0 : G → ℝ) := self_mem_nhdsWithin
    have hev := hev1.and hev2
    obtain ⟨p', hp'w, hp'v, hp'0⟩ :=
      ((mapClusterPt_iff_frequently.mp hx w hw).and_eventually hev).exists
    exact ⟨(ε₀, p', f p'), huv ⟨mem_of_mem_nhds hu, hvw ⟨hp'v, hp'w⟩⟩, hf p' hp'0⟩
  exact ((huniq p hp).unique hmem (hf p hp))
