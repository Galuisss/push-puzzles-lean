/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RowOrder
public import Mathlib.Data.Finset.Sort

/-! Ordered occupancy slots for any finite line state. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

variable {w h n : ℕ}

private theorem position_injOn (axis : Direction) (lane : ℕ) (s : State w h) :
    Set.InjOn axis.position (lineBoxes axis lane s : Set (Cell w h)) := by
  intro p hp q hq he
  exact axis.cell_ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he

/-- Enumerate all occupied line cells in their strict directional order. -/
noncomputable def OrderedLineState.ofState (s : State w h) (axis : Direction) (lane : ℕ)
    (hc : (lineBoxes axis lane s).card = n) : OrderedLineState n w h axis lane := by
  classical
  let slots := (lineBoxes axis lane s).image axis.position
  have hslots : slots.card = n := (Finset.card_image_of_injOn (position_injOn axis lane s)).trans hc
  have hex (i : Fin n) : ∃ p ∈ lineBoxes axis lane s, axis.position p = slots.orderEmbOfFin hslots i :=
    Finset.mem_image.mp (Finset.orderEmbOfFin_mem slots hslots i)
  let f : Fin n → Cell w h := fun i => Classical.choose (hex i)
  have hf (i : Fin n) : f i ∈ lineBoxes axis lane s ∧ axis.position (f i) = slots.orderEmbOfFin hslots i :=
    Classical.choose_spec (hex i)
  have hinj : Function.Injective f := by
    intro i j he
    apply (slots.orderEmbOfFin hslots).injective
    rw [← (hf i).2, ← (hf j).2, he]
  refine { state := s, position := f, injective := hinj, boxes_image := ?_, ordered := ?_ }
  · apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact (hf i).1
    · rw [Finset.card_image_of_injective Finset.univ hinj, hc, Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    change axis.position (f i) < axis.position (f j)
    rw [(hf i).2, (hf j).2]
    exact (slots.orderEmbOfFin hslots).strictMono hij

/-- Ordered slots retain the exact state being enumerated. -/
theorem OrderedLineState.ofState_state (s : State w h) (axis : Direction) (lane : ℕ)
    (hc : (lineBoxes axis lane s).card = n) : (OrderedLineState.ofState s axis lane hc).state = s := by
  unfold OrderedLineState.ofState
  rfl

/-- Lift both sides of an actual intermediate state with the same marks and exact ordered target slots. -/
theorem OrderedLineState.lift_at {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
    (S U : OrderedLineState n w h axis lane) {u t : State w h}
    (hpre : Relation.ReflTransGen (LineAdmissible B cap axis lane) S.state u)
    (hpost : Relation.ReflTransGen (LineAdmissible B cap axis lane) u t)
    (hsol : lineBoxes axis lane t = lineBoxes axis lane U.state) :
    ∃ M V : LineState (Fin n) w h axis lane,
      M.state = u ∧ V.state = t ∧ LineReachable B cap S.toLineState M ∧
        LineReachable B cap M V ∧ V.position = U.position := by
  obtain ⟨M, hM, hSM⟩ := lift_reachable S.toLineState hpre
  obtain ⟨V, hV, hMV⟩ := lift_reachable M (hM ▸ hpost)
  exact ⟨M, V, hM, hV, hSM, hMV,
    OrderedLineState.matches_target (hSM.trans hMV) (hV ▸ hsol)⟩

end PushPuzzle.PushS.RowLabels
