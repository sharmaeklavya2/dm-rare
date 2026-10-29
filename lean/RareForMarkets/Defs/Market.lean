module

public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Markets, demand, and allocation rules

Conventions:

* Buyers are indexed by a finite type `B` (the paper's `[n]`)
  and goods (equivalently sellers) by a finite type `G` (the paper's `[m]`).
* Bundles and prices are functions `G → ℝ`, and allocations are functions `B → G → ℝ`
  (`x i j` is the fraction of good `j` that buyer `i` gets).
* The paper's `x_{-j} ∈ ℝ^{[m] ∖ {j}}` is not a separate type: we keep a full vector `x`
  and ignore its `j`-th coordinate. The paper's `(s, x_{-j})` is `Function.update x j s`.
* Non-negativity of prices (`p ∈ ℝ_{≥0}^m`) is an explicit hypothesis `0 ≤ p`.
-/

@[expose] public section

open Finset

variable {B G : Type*} [Fintype B] [Fintype G]

/-- The set `[0, 1]^G` of bundles: `z j` is the fraction of good `j` in the bundle. -/
abbrev cube (G : Type*) : Set (G → ℝ) := Set.Icc 0 1

/-- A *market instance* `([n], [m], (uᵢ), (bᵢ))` with buyers `B` and goods `G`.
Each buyer `i` has a budget `bᵢ > 0` and a utility function `uᵢ`, which only matters on `cube G`.
(`uᵢ` is non-negative; this follows from `util_zero` and `util_strictMonoOn`;
proved in `Market.util_nonneg` in `../Prelims.lean`.) -/
structure Market (B G : Type*) where
  /-- The budget `bᵢ` of buyer `i`. -/
  budget : B → ℝ
  /-- The utility function `uᵢ` of buyer `i`. -/
  util : B → (G → ℝ) → ℝ
  budget_pos : ∀ i, 0 < budget i
  util_zero : ∀ i, util i 0 = 0
  util_continuousOn : ∀ i, ContinuousOn (util i) (cube G)
  /-- Strict monotonicity of `uᵢ`; see `strictMonoOn_cube_iff` in `../Prelims.lean`
  for an elementary restatement matching the paper. -/
  util_strictMonoOn : ∀ i, StrictMonoOn (util i) (cube G)

namespace Market

variable (M : Market B G)

/-! ### Budgets -/

/-- The total budget `B = ∑ᵢ bᵢ`. -/
def totalBudget : ℝ := ∑ i, M.budget i

/-- The average budget `b_avg = B / n`. -/
noncomputable def avgBudget : ℝ := M.totalBudget / Fintype.card B

/-- The minimum budget `b_min = minᵢ bᵢ`. (It is `0` if there are no buyers.) -/
noncomputable def minBudget : ℝ := ⨅ i, M.budget i

/-! ### Demand for non-rivalrous goods -/

/-- The bundles buyer `i` can afford at prices `p`: `{z ∈ [0, 1]^m : pᵀz ≤ bᵢ}`. -/
abbrev budgetSet (i : B) (p : G → ℝ) : Set (G → ℝ) :=
  {z ∈ cube G | ∑ j, p j * z j ≤ (M.budget i)}

/-- Buyer `i`'s demand set `Dem_i(p)`: the utility-maximizing affordable bundles. -/
def demand (i : B) (p : G → ℝ) : Set (G → ℝ) :=
  {z ∈ M.budgetSet i p | IsMaxOn (M.util i) (M.budgetSet i p) z}

/-- The combined non-rivalrous demand set `Dem^NR(p) = ∏ᵢ Dem_i(p)`. -/
def nonRivalDem (p : G → ℝ) : Set (B → G → ℝ) :=
  {x | ∀ i, x i ∈ M.demand i p}

/-! ### Demand for rivalrous goods -/

/-- `x` Pareto dominates `y` (`x ≻ y`): every buyer weakly prefers `x`,
and some buyer strictly prefers `x`. -/
def ParetoDominates (x y : B → G → ℝ) : Prop :=
  (∀ i, M.util i (y i) ≤ M.util i (x i)) ∧ ∃ i, M.util i (y i) < M.util i (x i)

/-- The Pareto optimal subset `PO(S)`: allocations in `S` not Pareto dominated
by any allocation in `S`. -/
def paretoOpt (S : Set (B → G → ℝ)) : Set (B → G → ℝ) :=
  {x ∈ S | ∀ y ∈ S, ¬ M.ParetoDominates y x}

/-- The affordable rivalrous allocations `Aff^R(p)`: allocations in `[0, 1]^{n × m}` where
each good is allocated at most once and each buyer can afford her bundle. -/
def rivalAff (p : G → ℝ) : Set (B → G → ℝ) :=
  {x | (∀ j, ∑ i, x i j ≤ 1) ∧ (∀ i, x i ∈ M.budgetSet i p)}

/-- The combined rivalrous demand set `Dem^R(p) = PO(Aff^R(p))`. -/
def rivalDem (p : G → ℝ) : Set (B → G → ℝ) :=
  M.paretoOpt (M.rivalAff p)

/-- The affordable non-rivalrous allocations `Aff^NR(p) = ∏ᵢ {z ∈ [0, 1]^m : pᵀz ≤ bᵢ}`. -/
def nonRivalAff (p : G → ℝ) : Set (B → G → ℝ) :=
  {x | ∀ i, x i ∈ M.budgetSet i p}

end Market

/-! ### Linear utilities -/

/-- The linear utility `z ↦ ∑ⱼ wⱼ zⱼ`. -/
def linearUtil (w : G → ℝ) (z : G → ℝ) : ℝ :=
  ∑ j, w j * z j

/-- Needed for `Market.ofLinear` -/
theorem linearUtil_strictMono {w : G → ℝ} (hw : ∀ j, 0 < w j) : StrictMono (linearUtil w) := by
  intro x y hxy
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.mp hxy
  exact sum_lt_sum (fun k _ ↦ by gcongr; exacts [(hw k).le, hle k])
    ⟨j, mem_univ j, by gcongr; exact hw j⟩

/-- The market where buyer `i` has linear utility `uᵢ(z) = ∑ⱼ u_{i,j} z_j` with `u_{i,j} > 0`. -/
def Market.ofLinear (budget : B → ℝ) (w : B → G → ℝ)
    (budget_pos : ∀ i, 0 < budget i) (w_pos : ∀ i j, 0 < w i j) : Market B G where
  budget := budget
  util i := linearUtil (w i)
  budget_pos := budget_pos
  util_zero i := by simp [linearUtil]
  util_continuousOn i := by unfold linearUtil; fun_prop
  util_strictMonoOn i := (linearUtil_strictMono (w_pos i)).strictMonoOn _

/-! ### Sellers' revenues -/

/-- Seller `j`'s revenue `R_j(p, x) = pⱼ ∑ᵢ x_{i,j}`. -/
def revenue (p : G → ℝ) (x : B → G → ℝ) (j : G) : ℝ :=
  p j * ∑ i, x i j

namespace Market

variable (M : Market B G)

/-- The function `F(y) = ∑ᵢ min(bᵢ, y)`. -/
noncomputable def F (y : ℝ) : ℝ := ∑ i, min (M.budget i) y

end Market

/-! ### Unifying rivalrous and non-rivalrous goods

Everything below is parametrized by whether the goods are rivalrous or not. -/

/-- Whether the goods are rivalrous or non-rivalrous. -/
inductive Rivalry
  | rival
  | nonRival
  deriving DecidableEq

namespace Market

variable (M : Market B G)

/-- The demand set `Dem(p)`: `Dem^R(p)` for rivalrous goods and
`Dem^NR(p)` for non-rivalrous goods. -/
def dem : Rivalry → (G → ℝ) → Set (B → G → ℝ)
  | .rival => M.rivalDem
  | .nonRival => M.nonRivalDem

/-- The sellers' total revenue `R_all(p)`: `min(B, ∑ⱼ pⱼ)` for rivalrous goods and
`F(∑ⱼ pⱼ)` for non-rivalrous goods.
This equals `∑ⱼ R_j(p, x)` for every `x ∈ Dem(p)` when `p ≥ 0`;
see `Market.sum_revenue_eq_revenueAll` in `../Prelims.lean`. -/
noncomputable def revenueAll : Rivalry → (G → ℝ) → ℝ
  | .rival, p => min M.totalBudget (∑ j, p j)
  | .nonRival, p => M.F (∑ j, p j)

/-! ### Market parameters -/

/-- The parameter `ν`: `1` for rivalrous goods and `n` for non-rivalrous goods. -/
noncomputable def nu : Rivalry → ℝ
  | .rival => 1
  | .nonRival => Fintype.card B

/-- The parameter `β`: `B` for rivalrous goods and `b_min` for non-rivalrous goods. -/
noncomputable def beta : Rivalry → ℝ
  | .rival => M.totalBudget
  | .nonRival => M.minBudget

/-- The parameter `κ`: `1` for rivalrous goods and `b_avg / b_min` for non-rivalrous goods.
This equals `B / (νβ)` when there is at least one buyer;
see `Market.kappa_eq` in `../Prelims.lean`. -/
noncomputable def kappa : Rivalry → ℝ
  | .rival => 1
  | .nonRival => M.avgBudget / M.minBudget

/-! ### Allocation rules -/

/-- An allocation rule `A : ℝ_{≥0}^m → [0, 1]^{n × m}` maps every non-negative price vector `p`
to an allocation in the demand set `Dem(p)` (`Dem^R(p)` or `Dem^NR(p)`, depending on `r`).
Its values at other price vectors are irrelevant. -/
structure AllocRule (r : Rivalry) where
  /-- The allocation `A(p)` at prices `p`. -/
  toFun : (G → ℝ) → (B → G → ℝ)
  mem_dem : ∀ p, 0 ≤ p → toFun p ∈ M.dem r p

end Market

namespace Market.AllocRule

variable {M : Market B G} {r : Rivalry}

instance : CoeFun (M.AllocRule r) (fun _ ↦ (G → ℝ) → (B → G → ℝ)) := ⟨toFun⟩

/-- Seller `j`'s revenue `R^A_j(p) = R_j(p, A(p))` under the allocation rule `A`. -/
def revenue (A : M.AllocRule r) (p : G → ℝ) (j : G) : ℝ := _root_.revenue p (A p) j

end Market.AllocRule

end
