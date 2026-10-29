module

public import RareForMarkets.NashEq.Defs
public import RareForMarkets.Defs.Market
import RareForMarkets.NashEq.Uncommon

/-! Main result from `\cref{sec:nasheq-uncommon:non-rival}` in the paper. -/

variable {B : Type*} [Fintype B]

/-- `\label{thm:nasheq-uncommon}`: for a market with 2 non-rivalrous goods and `n ≥ 1` buyers,
each with budget 1 and linear utility with `u_{i,j} ∈ [1, 2)`, and any allocation rule `A`,
a Nash equilibrium exists iff all buyers have the same utility ratio `u_{i,1} / u_{i,2}`.
(The paper's goods `1, 2` are `0, 1 : Fin 2`.) -/
public theorem nasheq_uncommon [Nonempty B] (w : B → Fin 2 → ℝ)
    (hw : ∀ i j, w i j ∈ Set.Ico 1 2)
    (A : (Market.ofLinear (fun _ ↦ 1) w (fun _ ↦ one_pos)
      (fun i j ↦ one_pos.trans_le (hw i j).1)).AllocRule .nonRival) :
    (∃ p, IsNashEq A p) ↔ ∀ i k, w i 0 / w i 1 = w k 0 / w k 1 :=
  TwoGoods.nasheq_uncommon_aux w hw A
