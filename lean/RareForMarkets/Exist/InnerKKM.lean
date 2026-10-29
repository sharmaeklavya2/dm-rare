module

public import Mathlib.Analysis.Convex.StdSimplex
import FixedPoint.KKM
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Order.Field

/-!
# The KKM lemma, and `\cref{thm:general-inner-kkm}`
-/

open Set Finset

/-- The KKM lemma over any nonempty finite index type, with the covering condition stated
pointwise: every point of the simplex lies in some `F i` with `0 < x i`. -/
public theorem kkm_of_support {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ι → Set (ι → ℝ)) (hclosed : ∀ i, IsClosed (F i))
    (hcover : ∀ x ∈ stdSimplex ℝ ι, ∃ i, 0 < x i ∧ x ∈ F i) :
    ∃ x ∈ stdSimplex ℝ ι, ∀ i, x ∈ F i := by
  -- Relabel the coordinates along `e : ι ≃ Fin n` and apply `kkm_closed_cover`.
  let e := Fintype.equivFin ι
  let φ : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) := fun y i ↦ y (e i)
  have hφ : Continuous φ := continuous_pi fun i ↦ continuous_apply (e i)
  have hφ_mem : ∀ y ∈ stdSimplex ℝ (Fin (Fintype.card ι)), φ y ∈ stdSimplex ℝ ι :=
    fun y hy ↦ ⟨fun i ↦ hy.1 (e i), (e.sum_comp y).trans hy.2⟩
  obtain ⟨y, hy, hyF⟩ := kkm_closed_cover Fintype.card_pos (fun k ↦ φ ⁻¹' F (e.symm k))
    (fun k ↦ (hclosed _).preimage hφ) (by
      intro σ y ⟨hy, hyσ⟩
      obtain ⟨i, hi, hiF⟩ := hcover (φ y) (hφ_mem y hy)
      have hmem : e i ∈ σ := by
        by_contra h
        exact hi.ne' (hyσ (e i) h)
      exact mem_iUnion₂.mpr ⟨e i, hmem, by simpa using hiF⟩)
  exact ⟨φ y, hφ_mem y hy, fun i ↦ by simpa using hyF (e i)⟩

variable {G : Type*}

/-- The part `U` of the boundary of the box `∏_{j ∈ S} [aⱼ, bⱼ]` where some coordinate
`i ∈ S` is at its upper bound `bᵢ`. Coordinates outside `S` are fixed to `c`. -/
@[expose] public def boxTop (S : Finset G) (a b c : G → ℝ) : Set (G → ℝ) :=
  {x | (∀ j ∈ S, x j ∈ Icc (a j) (b j)) ∧ (∀ j ∉ S, x j = c j) ∧ ∃ i ∈ S, x i = b i}

/-- `\label{thm:general-inner-kkm}` (with the coordinates outside `J = S` fixed to `c`). -/
public theorem inner_kkm (S : Finset G) (hS : S.Nonempty) (a b c : G → ℝ)
    (hab : ∀ j ∈ S, a j < b j) (f : G → (G → ℝ) → ℝ)
    (hf : ∀ j ∈ S, ContinuousOn (f j) (boxTop S a b c))
    (hsum : ∀ x ∈ boxTop S a b c, 0 ≤ ∑ j ∈ S, f j x)
    (hlow : ∀ x ∈ boxTop S a b c, ∀ j ∈ S, x j = a j → f j x ≤ 0) :
    ∃ x ∈ boxTop S a b c, ∀ j ∈ S, 0 ≤ f j x := by
  classical
  haveI : Nonempty S := hS.coe_sort
  -- Shoot a ray from `a` in direction `θ` and let `y θ` be where it hits `U`.
  let w : S → (S → ℝ) → ℝ := fun k θ ↦ θ k / (b k - a k)
  let m : (S → ℝ) → ℝ := fun θ ↦ univ.sup' univ_nonempty (w · θ)
  let y : (S → ℝ) → G → ℝ := fun θ j ↦ if h : j ∈ S then a j + θ ⟨j, h⟩ / m θ else c j
  have hba : ∀ k : S, 0 < b k - a k := fun k ↦ sub_pos.mpr (hab k k.2)
  have hm_pos : ∀ θ ∈ stdSimplex ℝ S, 0 < m θ := by
    intro θ hθ
    obtain ⟨k, hk⟩ : ∃ k, 0 < θ k := by
      by_contra! h
      have : ∑ k, θ k ≤ 0 := sum_nonpos fun k _ ↦ h k
      linarith [hθ.2]
    exact (div_pos hk (hba k)).trans_le (le_sup' (w · θ) (mem_univ k))
  have hy_mem : ∀ θ ∈ stdSimplex ℝ S, y θ ∈ boxTop S a b c := by
    intro θ hθ
    have hm := hm_pos θ hθ
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ by simp [y, hj], ?_⟩
    · have hle : w ⟨j, hj⟩ θ ≤ m θ := le_sup' (w · θ) (mem_univ _)
      have h0 := hθ.1 ⟨j, hj⟩
      have hb := hba ⟨j, hj⟩
      simp only [w] at hle hb
      simp only [y, hj, dite_true, Set.mem_Icc]
      refine ⟨by have := div_nonneg h0 hm.le; linarith, ?_⟩
      rw [div_le_iff₀ hb] at hle
      have : θ ⟨j, hj⟩ / m θ ≤ b j - a j := by
        rw [div_le_iff₀ hm]; linarith
      linarith
    · obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' univ_nonempty (w · θ)
      refine ⟨i, i.2, ?_⟩
      have hi' : m θ = θ i / (b i - a i) := hi
      have hθi : 0 < θ i := by
        have := hba i
        rw [hi'] at hm
        exact (div_pos_iff_of_pos_right this).mp hm
      simp only [y, i.2, dite_true, Subtype.coe_eta, hi']
      field_simp [(hba i).ne', hθi.ne']
      ring
  have hy_cont : ContinuousOn y (stdSimplex ℝ S) := by
    refine continuousOn_pi.mpr fun j ↦ ?_
    by_cases hj : j ∈ S
    · simp only [y, hj, dite_true]
      refine continuousOn_const.add ((continuous_apply _).continuousOn.div ?_ ?_)
      · exact (Continuous.finset_sup'_apply _ fun k _ ↦
          (continuous_apply k).div_const _).continuousOn
      · exact fun θ hθ ↦ (hm_pos θ hθ).ne'
    · simp only [y, hj, dite_false]
      exact continuousOn_const
  -- The KKM sets.
  let C : S → Set (S → ℝ) := fun k ↦ stdSimplex ℝ S ∩ (fun θ ↦ f k (y θ)) ⁻¹' Ici 0
  have hC : ∀ k, IsClosed (C k) := fun k ↦
    ((hf k k.2).comp hy_cont hy_mem).preimage_isClosed_of_isClosed
      (isCompact_stdSimplex ℝ S).isClosed isClosed_Ici
  obtain ⟨θ, hθ, hθC⟩ := kkm_of_support C hC (by
    intro θ hθ
    by_contra! h
    have hneg : ∑ k : S, f k (y θ) < ∑ _k : S, (0 : ℝ) := by
      obtain ⟨k, hk⟩ : ∃ k, 0 < θ k := by
        by_contra! h'
        have : ∑ k, θ k ≤ 0 := sum_nonpos fun k _ ↦ h' k
        linarith [hθ.2]
      refine sum_lt_sum (fun k _ ↦ ?_) ⟨k, mem_univ _, ?_⟩
      · rcases (hθ.1 k).lt_or_eq with hk | hk
        · exact (not_le.mp fun h' ↦ h k hk ⟨hθ, h'⟩).le
        · refine hlow _ (hy_mem θ hθ) k k.2 ?_
          simp [y, ← hk]
      · exact not_le.mp fun h' ↦ h k hk ⟨hθ, h'⟩
    rw [sum_coe_sort S (fun k ↦ f k (y θ))] at hneg
    simp only [sum_const_zero] at hneg
    exact (hsum _ (hy_mem θ hθ)).not_gt hneg)
  exact ⟨y θ, hy_mem θ hθ, fun j hj ↦ (hθC ⟨j, hj⟩).2⟩
