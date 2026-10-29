module

public import RareForMarkets.Defs.Market
public import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Pi

/-!
# Perturbed markets

The market `Ical^{(ε)}` with utilities `uᵢ(z) + ε ∑ₖ zₖ(2 − zₖ)`.
(For `ε < 0` we use `max ε 0` instead of `ε`, so that `M.perturb ε` is a market for every `ε`.)
-/

open Set Finset

variable {B G : Type*} [Fintype G]

/-- The perturbation term `∑ₖ zₖ(2 − zₖ)`. -/
@[expose] public def perturbTerm (z : G → ℝ) : ℝ := ∑ k, z k * (2 - z k)

public theorem continuous_perturbTerm : Continuous (perturbTerm (G := G)) := by
  unfold perturbTerm; fun_prop

private theorem perturbTerm_mono {x y : G → ℝ} (hx : x ∈ cube G) (hy : y ∈ cube G) (hxy : x ≤ y) :
    perturbTerm x ≤ perturbTerm y := by
  refine sum_le_sum fun k _ ↦ ?_
  have h1 : x k ≤ 1 := hx.2 k
  have h2 : y k ≤ 1 := hy.2 k
  nlinarith [mul_nonneg (sub_nonneg.mpr (hxy k)) (show 0 ≤ 2 - x k - y k by linarith)]

/-- The perturbation term is strictly concave on the cube. -/
private theorem perturbTerm_strict {x y : G → ℝ} (hne : x ≠ y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : a * perturbTerm x + b * perturbTerm y < perturbTerm (a • x + b • y) := by
  have hterm : ∀ k, (a * x k + b * y k) * (2 - (a * x k + b * y k)) -
      (a * (x k * (2 - x k)) + b * (y k * (2 - y k))) = a * b * (x k - y k) ^ 2 := by
    intro k
    obtain rfl : b = 1 - a := by linarith
    ring
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
    by_contra! h; exact hne (funext h)
  have : ∑ l, (a * (x l * (2 - x l)) + b * (y l * (2 - y l))) <
      ∑ l, (a * x l + b * y l) * (2 - (a * x l + b * y l)) := by
    refine sum_lt_sum (fun l _ ↦ ?_) ⟨k, mem_univ k, ?_⟩
    · have := hterm l; nlinarith [sq_nonneg (x l - y l), mul_pos ha hb]
    · have := hterm k
      have : 0 < (x k - y k) ^ 2 := by positivity
      nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) this]
  simpa [perturbTerm, mul_sum, sum_add_distrib] using this

namespace Market

variable (M : Market B G)

/-- The perturbed market `Ical^{(ε)}`. -/
@[expose] public noncomputable def perturb (ε : ℝ) : Market B G where
  budget := M.budget
  util i z := M.util i z + max ε 0 * perturbTerm z
  budget_pos := M.budget_pos
  util_zero i := by simp [M.util_zero, perturbTerm]
  util_continuousOn i :=
    (M.util_continuousOn i).add (continuousOn_const.mul continuous_perturbTerm.continuousOn)
  util_strictMonoOn i := by
    intro x hx y hy hxy
    have h1 := M.util_strictMonoOn i hx hy hxy
    have h2 := mul_le_mul_of_nonneg_left (perturbTerm_mono hx hy hxy.le) (le_max_right ε 0)
    simp only
    linarith

@[simp] private theorem perturb_budget (ε : ℝ) : (M.perturb ε).budget = M.budget := rfl

public theorem perturb_zero : M.perturb 0 = M := by
  cases M
  simp [perturb]

public theorem continuousOn_perturb (i : B) :
    ContinuousOn (fun x : ℝ × (G → ℝ) ↦ (M.perturb x.1).util i x.2)
      (Set.Icc 0 1 ×ˢ cube G) :=
  ((M.util_continuousOn i).comp continuousOn_snd fun _ hx ↦ hx.2).add
    ((continuous_fst.max continuous_const).mul
      (continuous_perturbTerm.comp continuous_snd)).continuousOn

/-- For `ε > 0`, perturbing concave utilities makes them strictly concave. -/
public theorem strictConcaveOn_perturb {i : B} (hu : ConcaveOn ℝ (cube G) (M.util i)) {ε : ℝ}
    (hε : 0 < ε) : StrictConcaveOn ℝ (cube G) ((M.perturb ε).util i) := by
  refine ⟨hu.1, fun x hx y hy hne a b ha hb hab ↦ ?_⟩
  have h1 := hu.2 hx hy ha.le hb.le hab
  have h2 := mul_lt_mul_of_pos_left (perturbTerm_strict hne ha hb hab) hε
  simp only [perturb, max_eq_left hε.le, smul_eq_mul] at h1 ⊢
  nlinarith

end Market
