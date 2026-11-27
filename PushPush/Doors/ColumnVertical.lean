/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnFault
public import PushPush.Doors.WireReadoutSameSignSourceMove

/-! Vertical private faults exceed their original pin-column budgets. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction)

variable {I : Instance}

theorem private_vertical_pin_reject_columns (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    (hvertical : wireDirection (layout storage I) index.val (layout storage I).wires[index] corner = .north ∨
      wireDirection (layout storage I) index.val (layout storage I).wires[index] corner = .south)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner.castSucc)
    (hregister : ∀ door, S.register door ≠ .erase) (hclear : S.ReverseClear index corner)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) : False := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let signal := wirePosition storage I index.val index.isLt e he corner.castSucc
  let before : Fin 7 := ⟨corner.val - 1, by omega⟩
  let previous := wireStop storage I index.val index.isLt e he before
  let removed := wireStop storage I index.val index.isLt e he corner
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  obtain ⟨landed, ha, hboxes⟩ := S.internal_pin_fault storage index corner hlo hhi hsignal hstock ht r hn hk hb hfirst
  have hf := hclear landed ha
  have hc := wire_private_corner_geometry storage I hei corner.castSucc hlo hhi
  have hsignalprivate : signal.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e corner.castSucc hlo corner.isLt
  have hremoved := wireStopRaw_pin_mem storage I hei corner hhi
  have hr := S.reverse_corner_deadStock storage _ signal previous removed landed hsignal.symm hc
    (wireStopRaw_pin_mem storage I hei before (by dsimp [before]; omega)) hremoved ha
    hsignalprivate hf.1 hregister (ht.of_boxes_eq hboxes.symm) hf.2
  apply deadStock_reject_columns hsuffix hcorridor hterminal
    (by rw [hboxes]; exact hr.1)
  rw [hboxes]
  exact S.reverse_vertical_excess signal previous removed landed hsignal.symm hc ha hsignalprivate hvertical

end PushPuzzle.PushPush.Doors.Source.Stock
