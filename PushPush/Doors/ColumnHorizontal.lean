/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnVertical

/-! Horizontal private pin faults put a box into an originally empty column. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem horizontal_pin_reject_columns (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hc : corner.val = 2 ∨ corner.val = 4)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner)
    (hregister : ∀ door, S.register door ≠ .erase)
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
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hlo : 0 < corner.val := by omega
  have hhi : corner.val < 6 := by omega
  let here : Fin 7 := ⟨corner.val, by omega⟩
  let before : Fin 7 := ⟨corner.val - 1, by omega⟩
  let signal := wirePosition storage I index.val index.isLt e he corner
  let previous := wireStop storage I index.val index.isLt e he before
  let stop := wireStop storage I index.val index.isLt e he here
  let forward := wireDirection (layout storage I) index.val e here
  have hcorner : here.castSucc = corner := Fin.ext rfl
  obtain ⟨landed, ha, hboxes⟩ := S.internal_pin_fault storage index here hlo hhi
    (by rw [hcorner]; exact hsignal) hstock ht r hn hk hb hfirst
  have hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei before (by dsimp [before]; omega)
  have hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei here hhi
  have hgeometry : Wire.Corner forward signal previous stop :=
    wire_private_corner_geometry storage I hei corner hlo hhi
  have ha : Adjacent forward signal landed := by simpa only [hcorner] using ha
  have hforward : forward = .east ∨ forward = .west := by
    rcases hc with hc | hc
    · have heq : here = 2 := Fin.ext hc
      simp [forward, heq, wireDirection]
    · have heq : here = 4 := Fin.ext hc
      simp [forward, heq, wireDirection]
  have hsraw : (signal.1.val, signal.2.val) = S.signal := hsignal.symm
  have hsprivate : signal.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e corner hlo (by omega)
  have hlandprivate : landed.1.val < (layout storage I).rackX - 1 := by
    rcases hc with hc | hc
    · have heq : corner = 2 := Fin.ext hc
      have hheq : here = 2 := Fin.ext hc
      change Adjacent forward signal landed at ha
      simp [forward, hheq, wireDirection, Adjacent] at ha
      have hx : signal.1.val = Layout.wireA index.val := by
        change (wirePositionRaw (layout storage I) index.val e corner).1 = _
        rw [heq]
        rfl
      have hi := index.isLt
      change landed.1.val < (30 * (layout storage I).wires.length + 40) - 1
      dsimp [Layout.wireA] at hx
      omega
    · have heq : corner = 4 := Fin.ext hc
      have hheq : here = 4 := Fin.ext hc
      simp [forward, hheq, wireDirection, Adjacent] at ha
      omega
  have hfree : ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val := by
    intro p hp
    have hf := (layout storage I).pins_not_free_column index.val hp
    rcases hc with hc | hc
    · have heq : corner = 2 := Fin.ext hc
      have hheq : here = 2 := Fin.ext hc
      simp [forward, hheq, wireDirection, Adjacent] at ha
      have hx : signal.1.val = Layout.wireA index.val := by
        change (wirePositionRaw (layout storage I) index.val e corner).1 = _
        rw [heq]
        rfl
      omega
    · have heq : corner = 4 := Fin.ext hc
      have hheq : here = 4 := Fin.ext hc
      simp [forward, hheq, wireDirection, Adjacent] at ha
      have hx : signal.1.val = Layout.wireB index.val := by
        change (wirePositionRaw (layout storage I) index.val e corner).1 = _
        rw [heq]
        rfl
      omega
  have hdead := (S.reverse_corner_deadStock storage forward signal previous stop landed
    hsraw hgeometry hprevious hstop ha hsprivate hlandprivate hregister
    (ht.of_boxes_eq hboxes.symm)
    (S.horizontal_neighbor_free_line storage forward signal landed hforward ha hsraw hlandprivate hfree)).1
  apply deadStock_reject_columns hsuffix hcorridor hterminal
    (by rw [hboxes]; exact hdead)
  apply Or.inr
  refine ⟨landed, ?_, hlandprivate, hfree⟩
  rw [hboxes]
  exact Finset.mem_insert_self _ _

end PushPuzzle.PushPush.Doors.Source.Stock
