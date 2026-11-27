/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutReject

/-! Complete inventory on either neighbor row of the two private horizontal tracks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

private theorem Y_neighbor_readout (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (side : Bool)
    (hsignal : S.signal.2 = (layout storage I).wireY i e) {p : ℕ × ℕ}
    (hy : p.2 = Layout.beside side ((layout storage I).wireY i e))
    (hp : p ∈ S.rawBoxes storage) :
    side = e.sourceSouth ∧ p = (Layout.wireA i,
      Layout.beside e.sourceSouth ((layout storage I).wireY i e)) := by
  have hi := (List.mem_zipIdx' hei).1
  have hout := (layout storage I).wireY_neighbor_outer i e hi side
  have hpos : 0 < (layout storage I).wireY i e := by
    dsimp [Layout.wireY, Layout.level]
    split <;> omega
  have hnonpin : p ∉ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage := by
    intro hb
    have hb := S.nonpin_row_band storage hb
    omega
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact pins_at_Y_neighbor storage I hei side hp hy
        · exact False.elim (hnonpin (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
      · exact False.elim (hnonpin (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
    · exact False.elim (hnonpin (Finset.mem_union_right _ hp))
  · have heq := congrArg Prod.snd (Finset.mem_singleton.mp hp)
    cases side <;> dsimp [Layout.beside] at hy <;> omega

private theorem V_neighbor_readout (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (side : Bool)
    (hsignal : S.signal.2 = (layout storage I).wireV i e) {p : ℕ × ℕ}
    (hy : p.2 = Layout.beside side ((layout storage I).wireV i e))
    (hp : p ∈ S.rawBoxes storage) :
    side = decide ((layout storage I).wireY i e < (layout storage I).wireV i e) ∧
      p = (Layout.wireB i, Layout.beside
        (decide ((layout storage I).wireY i e < (layout storage I).wireV i e))
        ((layout storage I).wireV i e)) := by
  have hi := (List.mem_zipIdx' hei).1
  have hout := (layout storage I).wireV_neighbor_outer i e hi side
  have hpos : 0 < (layout storage I).wireV i e := by
    dsimp [Layout.wireV, Layout.level]
    split <;> omega
  have hnonpin : p ∉ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage := by
    intro hb
    have hb := S.nonpin_row_band storage hb
    omega
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact pins_at_V_neighbor storage I hei side hp hy
        · exact False.elim (hnonpin (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
      · exact False.elim (hnonpin (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
    · exact False.elim (hnonpin (Finset.mem_union_right _ hp))
  · have heq := congrArg Prod.snd (Finset.mem_singleton.mp hp)
    cases side <;> dsimp [Layout.beside] at hy <;> omega

theorem middle_corner_reverse_clear (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 3)
    (hsign : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
      (layout storage I).wireV index.val (layout storage I).wires[index]) ≠
        (layout storage I).wires[index].sourceSouth) : S.ReverseClear index 3 := by
  let e := (layout storage I).wires[index]
  let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) 3
  let side := decide ((layout storage I).wireY index.val e < (layout storage I).wireV index.val e)
  have hdir : wireDirection (layout storage I) index.val e 3 =
      if side then .south else .north := by simp [wireDirection, side]
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hsprivate : signal.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e 3 (by decide) (by decide)
  intro landed ha
  change Adjacent (wireDirection (layout storage I) index.val e 3) signal landed at ha
  rw [hdir] at ha
  have hx : landed.1 = signal.1 := by
    cases hs : side <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at ha <;> exact ha.1
  have hy : landed.2.val = Layout.beside side ((layout storage I).wireY index.val e) := by
    have hsy : signal.2.val = (layout storage I).wireY index.val e := rfl
    cases hs : side <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true,
      Adjacent, Layout.beside] at ha ⊢ <;> omega
  refine ⟨by rw [hx]; exact hsprivate, ?_⟩
  intro d q hq hl hne
  have hqraw := ((layout storage I).mem_raster _ _).mp hq
  have hsy : S.signal.2 = (layout storage I).wireY index.val e := congrArg Prod.snd hsignal
  cases d with
  | north => exact hne (congrArg Fin.val hx)
  | south => exact hne (congrArg Fin.val hx)
  | east => exact hsign (S.Y_neighbor_readout storage hei side hsy (hl.trans hy) hqraw).1
  | west => exact hsign (S.Y_neighbor_readout storage hei side hsy (hl.trans hy) hqraw).1

theorem last_vertical_reverse_clear (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 5)
    (hsign : (layout storage I).wires[index].targetSouth ≠
      decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index])) : S.ReverseClear index 5 := by
  let e := (layout storage I).wires[index]
  let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) 5
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hsprivate : signal.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e 5 (by decide) (by decide)
  intro landed ha
  have hx : landed.1 = signal.1 := by
    change Adjacent (if e.targetSouth then .south else .north) signal landed at ha
    cases hs : e.targetSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at ha <;> exact ha.1
  have hy : landed.2.val = Layout.beside e.targetSouth ((layout storage I).wireV index.val e) := by
    have hsy : signal.2.val = (layout storage I).wireV index.val e := rfl
    change Adjacent (if e.targetSouth then .south else .north) signal landed at ha
    cases hs : e.targetSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true,
      Adjacent, Layout.beside] at ha ⊢ <;> omega
  refine ⟨by rw [hx]; exact hsprivate, ?_⟩
  intro d q hq hl hne
  have hqraw := ((layout storage I).mem_raster _ _).mp hq
  have hsy : S.signal.2 = (layout storage I).wireV index.val e := congrArg Prod.snd hsignal
  cases d with
  | north => exact hne (congrArg Fin.val hx)
  | south => exact hne (congrArg Fin.val hx)
  | east => exact hsign (S.V_neighbor_readout storage hei e.targetSouth hsy (hl.trans hy) hqraw).1
  | west => exact hsign (S.V_neighbor_readout storage hei e.targetSouth hsy (hl.trans hy) hqraw).1

end PushPuzzle.PushPush.Doors.Source.Stock
