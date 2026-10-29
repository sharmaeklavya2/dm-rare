module

public import RareForMarkets.NashEq.Defs
public import RareForMarkets.Defs.Market

/-! Properties of the rivalized utility `rivalizeUtil` (`\cref{thm:rivalize-1}`, item 1). -/

open Finset

variable {G : Type*} [Fintype G]

/-- Each summand `t ↦ a min(n t, 1) + ε max(n t - 1, 0)` of `rivalizeUtil`
is strictly increasing. -/
private theorem rivalizeUtil_summand_strictMono {n ε a : ℝ} (hn : 0 < n) (hε : 0 < ε)
    (ha : 0 < a) : StrictMono fun t : ℝ ↦ a * min (n * t) 1 + ε * max (n * t - 1) 0 := by
  intro t s hts
  have hnts : n * t < n * s := by gcongr
  have h1 : min (n * t) 1 ≤ min (n * s) 1 := min_le_min_right _ hnts.le
  have h2 : max (n * t - 1) 0 ≤ max (n * s - 1) 0 := max_le_max_right _ (by linarith)
  rcases lt_or_ge (n * t) 1 with h | h
  · have : min (n * t) 1 < min (n * s) 1 := by
      rw [min_eq_left h.le]; exact lt_min hnts h
    exact add_lt_add_of_lt_of_le (by gcongr) (by gcongr)
  · have : max (n * t - 1) 0 < max (n * s - 1) 0 := by
      rw [max_eq_left (by linarith)]; exact lt_max_of_lt_left (by linarith)
    exact add_lt_add_of_le_of_lt (by gcongr) (by gcongr)

/-- Part of `\cref{thm:rivalize-1}`, item 1: `ûᵢ` is strictly increasing. -/
public theorem rivalizeUtil_strictMonoOn_aux {n ε : ℝ} {w : G → ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hw : ∀ j, 0 < w j) :
    StrictMonoOn (rivalizeUtil n ε w) (cube G) := by
  refine StrictMono.strictMonoOn (fun x y hxy ↦ ?_) _
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.mp hxy
  exact sum_lt_sum (fun k _ ↦ (rivalizeUtil_summand_strictMono hn hε (hw k)).monotone (hle k))
    ⟨j, mem_univ j, rivalizeUtil_summand_strictMono hn hε (hw j) hlt⟩

/-- Part of `\cref{thm:rivalize-1}`, item 1: `ûᵢ` is SPLC.
(The paper gets `ε ≤ u_{i,j}` from `ε < u_min² / u_max ≤ u_min`.) -/
public theorem rivalizeUtil_isSPLC_aux {n ε : ℝ} {w : G → ℝ} (hεw : ∀ j, ε ≤ w j) :
    IsSPLC (rivalizeUtil n ε w) := by
  refine ⟨1, fun j ↦ ![w j * n, ε * n], fun j ↦ ![0, w j - ε], fun z _ ↦ sum_congr rfl
    fun j _ ↦ ?_⟩
  set f : Fin 2 → ℝ := fun l ↦ ![w j * n, ε * n] l * z j + ![0, w j - ε] l
  have hbdd : BddBelow (Set.range f) := (Set.finite_range _).bddBelow
  have hinf : ⨅ l, f l = min (f 0) (f 1) :=
    le_antisymm (le_min (ciInf_le hbdd 0) (ciInf_le hbdd 1))
      (le_ciInf (Fin.forall_fin_two.mpr ⟨min_le_left _ _, min_le_right _ _⟩))
  rw [hinf]
  simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
  have hwε := hεw j
  rcases le_total (n * z j) 1 with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), min_eq_left (by nlinarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith), min_eq_right (by nlinarith)]
    ring
