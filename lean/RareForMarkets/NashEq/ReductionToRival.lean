module

public import RareForMarkets.NashEq.Defs
public import RareForMarkets.Defs.Market
import RareForMarkets.NashEq.RivalizeUtil
import RareForMarkets.NashEq.RivalizeDemand

/-! Main results from `\cref{sec:lin-nonrival-to-splc-rival}` in the paper:
reducing non-rivalrous markets with linear utilities and equal budgets
to rivalrous markets with SPLC utilities. -/

variable {B G : Type*} [Fintype B] [Fintype G]

/-! ### The rivalized market -/

/-- Part of `\cref{thm:rivalize-1}`, item 1: `ûᵢ` is strictly increasing. -/
public theorem rivalizeUtil_strictMonoOn {n ε : ℝ} {w : G → ℝ}
    (hn : 0 < n) (hε : 0 < ε) (hw : ∀ j, 0 < w j) :
    StrictMonoOn (rivalizeUtil n ε w) (cube G) :=
  rivalizeUtil_strictMonoOn_aux hn hε hw

/-- Part of `\cref{thm:rivalize-1}`, item 1: `ûᵢ` is SPLC.
(The paper gets `ε ≤ u_{i,j}` from `ε < u_min² / u_max ≤ u_min`.) -/
private theorem rivalizeUtil_isSPLC {n ε : ℝ} {w : G → ℝ} (hεw : ∀ j, ε ≤ w j) :
    IsSPLC (rivalizeUtil n ε w) :=
  rivalizeUtil_isSPLC_aux hεw

/-- The market `Î = ([n], [m], (ûᵢ), (b))` from `\cref{thm:rivalize-1}`,
where `ûᵢ = rivalizeUtil n ε (u_{i,·})`. -/
@[expose] public noncomputable def Market.rivalize (b : ℝ) (w : B → G → ℝ) (ε : ℝ)
    (hb : 0 < b) (hw : ∀ i j, 0 < w i j) (hε : 0 < ε) : Market B G where
  budget _ := b
  util i := rivalizeUtil (Fintype.card B) ε (w i)
  budget_pos _ := hb
  util_zero i := by simp [rivalizeUtil]
  util_continuousOn i := by unfold rivalizeUtil; fun_prop
  util_strictMonoOn i :=
    rivalizeUtil_strictMonoOn (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩) hε (hw i)

/-! ### Demand sets -/

/-- `\label{thm:rivalize-1}`, item 2: for a non-rivalrous market `I` with common budget `b`
and linear utilities, and `0 < ε < u_min² / u_max`,
`x ∈ Dem^NR(p; I) ↔ (x ∈ [0, 1]^{n × m} and x / n ∈ Dem^R(n p; Î))`. -/
private theorem rivalize_dem_iff {b : ℝ} {w : B → G → ℝ} {ε : ℝ}
    (hb : 0 < b) (hw : ∀ i j, 0 < w i j)
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    {p : G → ℝ} (hp : 0 ≤ p) (x : B → G → ℝ) :
    x ∈ (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).nonRivalDem p ↔
      (∀ i, x i ∈ cube G) ∧
      (fun i j ↦ x i j / Fintype.card B) ∈
        (Market.rivalize b w ε hb hw hε).rivalDem (fun j ↦ Fintype.card B * p j) :=
  Rivalize.rivalize_dem_iff_aux hb hw (fun _ ↦ rfl) (fun _ ↦ rfl) hε hεw hp x

/-! ### Allocation rules and Nash equilibria -/

/-- `\label{thm:rivalize-2}`, item 1: for a non-rivalrous allocation rule `A` for `I`,
`Â(p) = A(p / n) / n` lies in `Dem^R(p; Î)` for all `p ≥ 0`. -/
public theorem rivalize_allocRule_mem {b : ℝ} {w : B → G → ℝ} {ε : ℝ}
    (hb : 0 < b) (hw : ∀ i j, 0 < w i j)
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    (A : (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).AllocRule .nonRival)
    (p : G → ℝ) (hp : 0 ≤ p) :
    (fun i j ↦ A (fun j ↦ p j / Fintype.card B) i j / Fintype.card B) ∈
      (Market.rivalize b w ε hb hw hε).rivalDem p :=
  Rivalize.rivalize_allocRule_mem_aux hb hw (fun _ ↦ rfl) (fun _ ↦ rfl) hε hεw A p hp

/-- The rivalrous allocation rule `Â(p) = A(p / n) / n` for `Î` from `\cref{thm:rivalize-2}`. -/
@[expose] public noncomputable def Market.AllocRule.rivalize {b : ℝ} {w : B → G → ℝ} {ε : ℝ}
    (hb : 0 < b) (hw : ∀ i j, 0 < w i j)
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    (A : (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).AllocRule .nonRival) :
    (Market.rivalize b w ε hb hw hε).AllocRule .rival where
  toFun p i j := A (fun j ↦ p j / Fintype.card B) i j / Fintype.card B
  mem_dem p hp := rivalize_allocRule_mem hb hw hε hεw A p hp

/-- `\label{thm:rivalize-2}`, item 2: `p` is a Nash equilibrium for `(Î, Â)`
iff `p / n` is a Nash equilibrium for `(I, A)`. -/
public theorem rivalize_isNashEq_iff [DecidableEq G] [Nonempty B] {b : ℝ} {w : B → G → ℝ} {ε : ℝ}
    (hb : 0 < b) (hw : ∀ i j, 0 < w i j)
    (hε : 0 < ε) (hεw : ε < minWeight w ^ 2 / maxWeight w)
    (A : (Market.ofLinear (fun _ ↦ b) w (fun _ ↦ hb) hw).AllocRule .nonRival) (p : G → ℝ) :
    IsNashEq (Market.AllocRule.rivalize hb hw hε hεw A) p ↔
      IsNashEq A (fun j ↦ p j / Fintype.card B) :=
  Rivalize.rivalize_isNashEq_iff_aux A p
