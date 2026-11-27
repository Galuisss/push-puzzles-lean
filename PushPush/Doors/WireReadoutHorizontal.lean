/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutAdvance
public import PushPush.Doors.WireReadoutReverse

/-! Consuming the distant pin of either horizontal private leg is fatal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem horizontal_pin_reject (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hc : corner.val = 2 ∨ corner.val = 4)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable t final)
    (hgoal : final.boxes = (puzzle storage I).board.goals)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hmove : Step s t) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) : False := by
  have hn1 := (S.pin_slide storage hstock r hn hk
    (by rw [← hb]; exact ht.interior) _ hfirst rfl).1
  subst n
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
  have hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei before (by dsimp [before]; omega)
  have hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei here hhi
  have hgeometry : Wire.Corner forward signal previous stop :=
    wire_private_corner_geometry storage I hei corner hlo hhi
  have hread := S.wire_internal_slide storage hei corner hlo hhi hsignal hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inl hfirst)
  change 1 = 1 ∧ ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) stop) ∨
    (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) signal)) at hread
  rcases hread.2 with hforward | hreverse
  · have hclear := S.wire_private_empty index here hlo
    have hsame : here.castSucc = corner := Fin.ext rfl
    rw [hsame] at hclear
    change signal ∉ S.stationary storage at hclear
    have hp : r.cell ⟨1, by omega⟩ ∈ S.stationary storage :=
      ((layout storage I).mem_raster _ _).mpr
      (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hfirst)))
    exact hclear (hforward.2.1 ▸ hp)
  · obtain ⟨hd, hfirsteq, hlast⟩ := hreverse
    let landed := r.cell ⟨1 + k, by omega⟩
    have ha : Adjacent forward signal landed := by
      have h := hlast.reverse
      simpa only [hd, Direction.opposite_opposite] using h
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
    have hboxes : t.boxes = insert landed ((S.boxes storage).erase stop) := by
      rw [hb, single_slide_boxes r, hfirsteq, hstock]
      simp only [landed, Nat.add_comm]
    obtain ⟨hdead, hmissing⟩ := S.reverse_corner_deadStock storage forward signal previous stop landed
      hsraw hgeometry hprevious hstop ha hsprivate hlandprivate hregister
      (ht.of_boxes_eq hboxes.symm)
      (S.horizontal_neighbor_free_line storage forward signal landed hforward ha hsraw hlandprivate hfree)
    apply deadStock_reject storage I (hprefix.trans (.single hmove)) hsuffix hgoal
      (by rw [hboxes]; exact hdead) stop hstop
    rw [hboxes]
    exact hmissing

end PushPuzzle.PushPush.Doors.Source.Stock
