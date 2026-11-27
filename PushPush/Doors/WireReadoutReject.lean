/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutAdvance
public import PushPush.Doors.WireReadoutReverse
public import PushPush.Doors.WireReadoutDeparture

/-! Reverse-pin rejection from a verified empty landing line. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

/-- The newly opened line of a reverse-pin landing contains no original box. -/
def Stock.ReverseClear {storage : Bool} {I : Instance} (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7) : Prop :=
  let e := (layout storage I).wires[index]
  let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) corner.castSucc
  ∀ landed : Cell (layout storage I).width (layout storage I).height,
    Adjacent (wireDirection (layout storage I) index.val e corner) signal landed →
      landed.1.val < (layout storage I).rackX - 1 ∧
      ∀ (d : Direction) q, q ∈ S.boxes storage → d.lane q = d.lane landed →
        d.lane landed ≠ d.lane signal → False

namespace Stock

variable {I : Instance}

theorem private_pin_reject (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner.castSucc)
    (hregister : ∀ door, S.register door ≠ .erase) (hclear : S.ReverseClear index corner)
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
  let before : Fin 7 := ⟨corner.val - 1, by omega⟩
  let signal := wirePosition storage I index.val index.isLt e he corner.castSucc
  let previous := wireStop storage I index.val index.isLt e he before
  let stop := wireStop storage I index.val index.isLt e he corner
  let forward := wireDirection (layout storage I) index.val e corner
  have hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei before (by dsimp [before]; omega)
  have hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins :=
    wireStopRaw_pin_mem storage I hei corner hhi
  have hgeometry : Wire.Corner forward signal previous stop :=
    wire_private_corner_geometry storage I hei corner.castSucc hlo hhi
  have hread := S.wire_internal_slide storage hei corner.castSucc hlo hhi hsignal hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inl hfirst)
  change 1 = 1 ∧ ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) stop) ∨
    (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) signal)) at hread
  rcases hread.2 with ⟨_, hfirsteq, _⟩ | ⟨hd, hfirsteq, hlast⟩
  · have hsource := S.wire_private_empty index corner hlo
    change signal ∉ S.stationary storage at hsource
    have hp : r.cell ⟨1, by omega⟩ ∈ S.stationary storage :=
      ((layout storage I).mem_raster _ _).mpr
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hfirst)))
    exact hsource (hfirsteq ▸ hp)
  · let landed := r.cell ⟨1 + k, by omega⟩
    change d = forward.opposite at hd
    have ha : Adjacent forward signal landed := by
      have h := hlast.reverse
      simpa only [hd, Direction.opposite_opposite] using h
    have hf := hclear landed ha
    have hsprivate : signal.1.val < (layout storage I).rackX - 1 :=
      wire_private_position _ _ index.isLt e corner.castSucc hlo corner.isLt
    have hboxes : t.boxes = insert landed ((S.boxes storage).erase stop) := by
      rw [hb, single_slide_boxes r, hfirsteq, hstock]
      simp only [landed, Nat.add_comm]
    obtain ⟨hdead, hmissing⟩ := S.reverse_corner_deadStock storage forward signal previous stop landed
      hsignal.symm hgeometry hprevious hstop ha hsprivate hf.1 hregister
      (ht.of_boxes_eq hboxes.symm) hf.2
    apply deadStock_reject storage I (hprefix.trans (.single hmove)) hsuffix hgoal
      (by rw [hboxes]; exact hdead) stop hstop
    rw [hboxes]
    exact hmissing

theorem first_corner_reverse_clear (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] 1) : S.ReverseClear index 1 := by
  let e := (layout storage I).wires[index]
  let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) 1
  have hraw : (signal.1.val, signal.2.val) = (Layout.wireA index.val,
      e.source + (layout storage I).shift) := rfl
  have hsprivate : signal.1.val < (layout storage I).rackX - 1 :=
    wire_private_position _ _ index.isLt e 1 (by decide) (by decide)
  intro landed ha
  have hx : landed.1 = signal.1 := by
    change Adjacent (if e.sourceSouth then .south else .north) signal landed at ha
    cases hs : e.sourceSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at ha <;>
      exact ha.1
  have hy : landed.2.val = Layout.beside e.sourceSouth (e.source + (layout storage I).shift) := by
    have hsy := congrArg Prod.snd hraw
    change Adjacent (if e.sourceSouth then .south else .north) signal landed at ha
    cases hs : e.sourceSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true,
      Adjacent, Layout.beside] at ha ⊢ <;> omega
  refine ⟨by rw [hx]; exact hsprivate, ?_⟩
  intro d q hq hl hne
  cases d with
  | north => exact hne (congrArg Fin.val hx)
  | south => exact hne (congrArg Fin.val hx)
  | east =>
      apply S.departure_row_empty storage (e := e) (p := (q.1.val, q.2.val))
        (List.getElem_mem index.isLt)
        (congrArg Prod.snd hsignal)
        (show q.2.val = Layout.beside e.sourceSouth (e.source + (layout storage I).shift) from hl.trans hy)
      exact ((layout storage I).mem_raster _ _).mp hq
  | west =>
      apply S.departure_row_empty storage (e := e) (p := (q.1.val, q.2.val))
        (List.getElem_mem index.isLt)
        (congrArg Prod.snd hsignal)
        (show q.2.val = Layout.beside e.sourceSouth (e.source + (layout storage I).shift) from hl.trans hy)
      exact ((layout storage I).mem_raster _ _).mp hq

end Stock
end PushPuzzle.PushPush.Doors.Source
