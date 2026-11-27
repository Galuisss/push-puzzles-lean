/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutSameSignSourceFault

/-! A reversed original pin creates exactly the emitted same-sign fault inventory. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem internal_pin_fault (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner.castSucc)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) :
    let e := (layout storage I).wires[index]
    let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) corner.castSucc
    let removed := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) corner
    ∃ near : Cell (layout storage I).width (layout storage I).height,
      Adjacent (wireDirection (layout storage I) index.val e corner) signal near ∧
        t.boxes = insert near ((S.boxes storage).erase removed) := by
  intro e signal removed
  have hn1 := (S.pin_slide storage hstock r hn hk (by rw [← hb]; exact ht.interior) _ hfirst rfl).1
  subst n
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hread := S.wire_internal_slide storage hei corner.castSucc hlo hhi hsignal hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inl hfirst)
  let before : Fin 7 := ⟨corner.val - 1, by omega⟩
  let previous := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) before
  let forward := wireDirection (layout storage I) index.val e corner
  change 1 = 1 ∧ ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) removed) ∨
    (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = removed ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) signal)) at hread
  rcases hread.2 with ⟨_, hsignalfirst, _⟩ | ⟨hd, hremovedfirst, hstop⟩
  · have hsource := S.wire_private_empty index corner hlo
    change signal ∉ S.stationary storage at hsource
    have hp : r.cell ⟨1, by omega⟩ ∈ S.stationary storage :=
      ((layout storage I).mem_raster _ _).mpr
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hfirst)))
    exact False.elim (hsource (hsignalfirst ▸ hp))
  · refine ⟨r.cell ⟨1 + k, by omega⟩, ?_, ?_⟩
    · have ha := hstop.reverse
      simpa only [hd, Direction.opposite_opposite] using ha
    · rw [hb, single_slide_boxes r, hremovedfirst, hstock]
      simp only [Nat.add_comm]

theorem sameSignB_pin_fault (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 3)
    (hsame : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
      (layout storage I).wireV index.val (layout storage I).wires[index]) =
        (layout storage I).wires[index].sourceSouth)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) :
    ∃ E : ExtendedFault storage I S, t.boxes = insert E.near ((S.boxes storage).erase E.removed) := by
  obtain ⟨near, ha, hboxes⟩ := S.internal_pin_fault storage index 3 (by decide) (by decide)
    hsignal hstock ht r hn hk hb hfirst
  exact ⟨S.sameSignBFault storage index hsignal hsame near ha, hboxes⟩

theorem sameSignC_pin_fault (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 5)
    (hsame : (layout storage I).wires[index].targetSouth =
      decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) :
    ∃ E : ExtendedFault storage I S, t.boxes = insert E.near ((S.boxes storage).erase E.removed) := by
  obtain ⟨near, ha, hboxes⟩ := S.internal_pin_fault storage index 5 (by decide) (by decide)
    hsignal hstock ht r hn hk hb hfirst
  exact ⟨S.sameSignCFault storage index hsignal hsame near ha, hboxes⟩

end PushPuzzle.PushPush.Doors.Source.Stock
