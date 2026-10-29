module

public import RareForMarkets.Exist.Argmax
public import RareForMarkets.Exist.Defs
public import RareForMarkets.Defs.Market
import RareForMarkets.Prelims
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Module.Defs

/-!
# Demand sets as argmax correspondences

Non-rivalrous demand and `W`-rivalrous demand, for a family of markets `M ε` with common
budgets, are argmax correspondences in the sense of `RareForMarkets.Exist.Argmax`.
-/

open Set
open Finset (sum_le_sum sum_lt_sum sum_add_distrib mul_sum sum_erase_add
  ne_of_mem_erase sum_congr)

variable {B G : Type*} [Fintype B] [Fintype G]

/-! ### The feasible sets -/

/-- The allocations `[0, 1]^{n × m}`; the feasible set is then `Aff^NR`. -/
@[expose] public abbrev nonRivalY (B G : Type*) : Set (B → G → ℝ) := Icc 0 1

/-- The allocations in `[0, 1]^{n × m}` respecting the stock constraints;
the feasible set is then `Aff^R`. -/
@[expose] public def rivalY (B G : Type*) [Fintype B] : Set (B → G → ℝ) :=
  Icc 0 1 ∩ {x | ∀ j, ∑ i, x i j ≤ 1}

omit [Fintype B] [Fintype G] in
public theorem mem_Icc_iff_cube {x : B → G → ℝ} : x ∈ Icc (0 : B → G → ℝ) 1 ↔ ∀ i, x i ∈ cube G :=
  ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

omit [Fintype B] [Fintype G] in
public theorem shrinkClosed_nonRivalY : ShrinkClosed (nonRivalY B G) := by
  intro x hx c hc
  refine mem_Icc_iff_cube.mpr fun i ↦ ⟨fun j ↦ ?_, fun j ↦ ?_⟩
  · exact mul_nonneg (hc i).1 (hx.1 i j)
  · exact mul_le_one₀ (hc i).2 (hx.1 i j) (hx.2 i j)

omit [Fintype G] in
public theorem shrinkClosed_rivalY : ShrinkClosed (rivalY B G) := by
  intro x hx c hc
  refine ⟨shrinkClosed_nonRivalY x hx.1 c hc, fun j ↦ (sum_le_sum fun i _ ↦ ?_).trans (hx.2 j)⟩
  exact mul_le_of_le_one_left (hx.1.1 i j) (hc i).2

omit [Fintype G] in
public theorem isClosed_rivalY : IsClosed (rivalY B G) := by
  refine isClosed_Icc.inter ?_
  rw [setOf_forall]
  exact isClosed_iInter fun j ↦ isClosed_le (by fun_prop) continuous_const

omit [Fintype G] in
public theorem convex_rivalY : Convex ℝ (rivalY B G) := by
  refine (convex_Icc 0 1).inter ?_
  rw [setOf_forall]
  refine convex_iInter fun j ↦ convex_halfSpace_le ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩ 1
  · simp [sum_add_distrib]
  · simp [mul_sum]

omit [Fintype B] [Fintype G] in
public theorem convex_nonRivalY : Convex ℝ (nonRivalY B G) := convex_Icc 0 1

omit [Fintype G] in
public theorem zero_mem_rivalY : (0 : B → G → ℝ) ∈ rivalY B G :=
  ⟨⟨le_rfl, zero_le_one⟩, fun j ↦ by simp⟩

namespace Market

variable (M : Market B G)

omit [Fintype B] in
private theorem feasible_nonRivalY (p : G → ℝ)
    : feasible (nonRivalY B G) M.budget p = M.nonRivalAff p := by
  ext x
  simp only [feasible, nonRivalAff, mem_setOf_eq, mem_Icc_iff_cube]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

private theorem feasible_rivalY (p : G → ℝ) : feasible (rivalY B G) M.budget p = M.rivalAff p := by
  ext x
  constructor
  · rintro ⟨⟨hI, hs⟩, hc⟩
    exact ⟨hs, fun i ↦ ⟨⟨hI.1 i, hI.2 i⟩, hc i⟩⟩
  · rintro ⟨hs, hb⟩
    exact ⟨⟨⟨fun i ↦ (hb i).1.1, fun i ↦ (hb i).1.2⟩, hs⟩, fun i ↦ (hb i).2⟩

end Market

/-! ### Welfare functions -/

/-- The utilitarian welfare `∑ᵢ vᵢ`. -/
@[expose] public def sumWelfare (B : Type*) [Fintype B] : (B → ℝ) → ℝ := fun v ↦ ∑ i, v i

public theorem isNiceWelfare_sum : IsNiceWelfare (sumWelfare B) := by
  refine ⟨(continuous_finsetSum _ fun i _ ↦ continuous_apply i).continuousOn, ?_, ?_⟩
  · intro v _ w _ hvw
    obtain ⟨hle, i, hlt⟩ := Pi.lt_def.mp hvw
    exact sum_lt_sum (fun k _ ↦ hle k) ⟨i, Finset.mem_univ i, hlt⟩
  · refine ⟨convex_Ici 0, fun x _ y _ a b _ _ _ ↦ le_of_eq ?_⟩
    simp [sumWelfare, sum_add_distrib, mul_sum]

/-- The objective `V(ε, x) = W(u₁^ε(x₁), …, uₙ^ε(xₙ))` for a family of markets. -/
@[expose] public def welfareObj (Mf : ℝ → Market B G) (W : (B → ℝ) → ℝ) : ℝ × (B → G → ℝ) → ℝ :=
  fun e ↦ W fun i ↦ (Mf e.1).util i (e.2 i)

omit [Fintype B] [Fintype G] in
public theorem continuousOn_welfareObj {Mf : ℝ → Market B G}
    (hcont : ∀ i, ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (Mf x.1).util i x.2)
      (Icc 0 1 ×ˢ cube G))
    {W : (B → ℝ) → ℝ} (hW : ContinuousOn W (Ici 0)) {Y : Set (B → G → ℝ)}
    (hY : Y ⊆ Icc 0 1) : ContinuousOn (welfareObj Mf W) (Icc 0 1 ×ˢ Y) := by
  have hu : ContinuousOn (fun e : ℝ × (B → G → ℝ) ↦ fun i ↦ (Mf e.1).util i (e.2 i))
      (Icc 0 1 ×ˢ Y) :=
    continuousOn_pi.mpr fun i ↦ (hcont i).comp
      (f := fun e : ℝ × (B → G → ℝ) ↦ (e.1, e.2 i))
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)).continuousOn
      fun e (he : e ∈ Icc (0 : ℝ) 1 ×ˢ Y) ↦ ⟨he.1, mem_Icc_iff_cube.mp (hY he.2) i⟩
  exact hW.comp hu fun e (he : e ∈ Icc (0 : ℝ) 1 ×ˢ Y) i ↦
    (Mf e.1).util_nonneg i (mem_Icc_iff_cube.mp (hY he.2) i)

omit [Fintype B] [Fintype G] in
/-- `V(x) = W(u₁(x₁), …, uₙ(xₙ))` is strictly concave
(proof of `\cref{thm:unique-rival-demand}`). -/
public theorem Market.strictConcaveOn_welfare (M : Market B G)
    (hu : ∀ i, StrictConcaveOn ℝ (cube G) (M.util i)) {W : (B → ℝ) → ℝ}
    (hW : IsNiceWelfare W) {S : Set (B → G → ℝ)} (hS : Convex ℝ S) (hSY : S ⊆ Icc 0 1) :
    StrictConcaveOn ℝ S fun x ↦ W fun i ↦ M.util i (x i) := by
  refine ⟨hS, fun x hx y hy hne a b ha hb hab ↦ ?_⟩
  have hxc := mem_Icc_iff_cube.mp (hSY hx)
  have hyc := mem_Icc_iff_cube.mp (hSY hy)
  have hzc := mem_Icc_iff_cube.mp (hSY (hS hx hy ha.le hb.le hab))
  set U : (B → G → ℝ) → B → ℝ := fun z i ↦ M.util i (z i)
  have hU : ∀ z, (∀ i, z i ∈ cube G) → U z ∈ Ici 0 := fun z hz i ↦ M.util_nonneg i (hz i)
  have hlt : a • U x + b • U y < U (a • x + b • y) := by
    refine Pi.lt_def.mpr ⟨fun i ↦ ?_, ?_⟩
    · simpa [U] using (hu i).concaveOn.2 (hxc i) (hyc i) ha.le hb.le hab
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra! h; exact hne (funext h)
      exact ⟨i, by simpa [U] using (hu i).2 (hxc i) (hyc i) hi ha hb hab⟩
  have h1 := hW.strictMonoOn
    (by
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (mul_nonneg ha.le (hU x hxc i)) (mul_nonneg hb.le (hU y hyc i)))
    (hU _ hzc) hlt
  have h2 := hW.concaveOn.2 (hU x hxc) (hU y hyc) ha.le hb.le hab
  exact h2.trans_lt h1

/-! ### Demand as an argmax -/

omit [Fintype G] in
private theorem sum_update_eq [DecidableEq B] {f : B → (G → ℝ) → ℝ}
    (x : B → G → ℝ) (i : B) (z : G → ℝ) :
    ∑ k, f k (Function.update x i z k) = ∑ k, f k (x k) - f i (x i) + f i z := by
  rw [← sum_erase_add _ _ (Finset.mem_univ i),
    ← sum_erase_add Finset.univ (fun k ↦ f k (x k)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
  ring

namespace Market

variable (Mf : ℝ → Market B G) (hb : ∀ ε, (Mf ε).budget = (Mf 0).budget)
include hb

/-- Non-rivalrous demand is the argmax of `∑ᵢ uᵢ(xᵢ)` over `Aff^NR`. -/
public theorem mem_nonRivalDem_iff {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) {p : G → ℝ} (hp : 0 ≤ p)
    {x : B → G → ℝ} :
    x ∈ (Mf ε).nonRivalDem p ↔
      (ε, p, x) ∈ argmaxGraph (nonRivalY B G) (Mf 0).budget (welfareObj Mf (sumWelfare B)) := by
  classical
  have hF : feasible (nonRivalY B G) (Mf 0).budget p = (Mf ε).nonRivalAff p := by
    rw [← hb ε, feasible_nonRivalY]
  constructor
  · intro hx
    refine ⟨hε, hp, hF ▸ (Mf ε).nonRivalDem_subset_nonRivalAff p hx, fun y hy ↦ ?_⟩
    rw [hF] at hy
    exact sum_le_sum fun i _ ↦ (hx i).2 (hy i)
  · rintro ⟨-, -, hx, hmax⟩
    rw [hF] at hx hmax
    intro i
    refine ⟨hx i, fun z hz ↦ ?_⟩
    have hy : Function.update x i z ∈ (Mf ε).nonRivalAff p := fun k ↦ by
      by_cases hk : k = i
      · subst hk; simpa using hz
      · simpa [hk] using hx k
    have := hmax _ hy
    simp only [welfareObj, sumWelfare] at this
    rw [sum_update_eq (f := fun k ↦ (Mf ε).util k)] at this
    change (Mf ε).util i z ≤ (Mf ε).util i (x i)
    linarith

/-- `W`-rivalrous demand is the argmax of `W(u₁(x₁), …, uₙ(xₙ))` over `Aff^R`. -/
public theorem mem_welfareDem_iff (W : (B → ℝ) → ℝ) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) {p : G → ℝ}
    (hp : 0 ≤ p) {x : B → G → ℝ} :
    x ∈ (Mf ε).welfareDem W p ↔
      (ε, p, x) ∈ argmaxGraph (rivalY B G) (Mf 0).budget (welfareObj Mf W) := by
  have hF : feasible (rivalY B G) (Mf 0).budget p = (Mf ε).rivalAff p := by
    rw [← hb ε, feasible_rivalY]
  rw [argmaxGraph, mem_setOf_eq, hF]
  exact ⟨fun hx ↦ ⟨hε, hp, hx.1, fun y hy ↦ hx.2 hy⟩, fun hx ↦ ⟨hx.2.2.1, fun y hy ↦ hx.2.2.2 y hy⟩⟩

end Market

/-- For a strictly monotone welfare function, `Dem^W(p) ⊆ Dem^R(p)`. -/
public theorem Market.welfareDem_subset_rivalDem (M : Market B G) {W : (B → ℝ) → ℝ}
    (hW : StrictMonoOn W (Ici 0)) (p : G → ℝ) : M.welfareDem W p ⊆ M.rivalDem p := by
  intro x hx
  refine ⟨hx.1, fun y hy ⟨hle, i, hlt⟩ ↦ ?_⟩
  have hU : ∀ z ∈ M.rivalAff p, (fun i ↦ M.util i (z i)) ∈ Ici 0 :=
    fun z hz i ↦ M.util_nonneg i (hz.2 i).1
  have := hW (hU x hx.1) (hU y hy) (Pi.lt_def.mpr ⟨hle, i, hlt⟩)
  exact (this.trans_le (hx.2 hy)).false
