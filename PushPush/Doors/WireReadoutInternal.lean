/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutHorizontal
public import PushPush.Doors.WireReadoutSameSignSourceFault
public import PushPush.Doors.WireReadoutExtendedEngine

/-! No original routing pin can move on a successful execution at a private turn. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

private theorem same_sign_pin_reject (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 7)
    (hcorner : corner.val = 3 ∨ corner.val = 5)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner.castSucc)
    (hsame : if corner.val = 3 then
      decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]) =
          (layout storage I).wires[index].sourceSouth else
      (layout storage I).wires[index].targetSouth =
        decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
          (layout storage I).wireV index.val (layout storage I).wires[index]))
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
  let signal := wirePosition storage I index.val index.isLt e he corner.castSucc
  let stop := wireStop storage I index.val index.isLt e he corner
  let forward := wireDirection (layout storage I) index.val e corner
  have hlo : 0 < corner.val := by omega
  have hhi : corner.val < 6 := by omega
  have hread := S.wire_internal_slide storage hei corner.castSucc hlo hhi hsignal hstock r hn hk
    (by rw [← hb]; exact ht.interior) (Or.inl hfirst)
  change 1 = 1 ∧ ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) stop) ∨
    (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
    Adjacent d (r.cell ⟨1 + k, by omega⟩) signal)) at hread
  rcases hread.2 with ⟨_, hf, _⟩ | ⟨hd, hf, ha⟩
  · have hsource := S.wire_private_empty index corner hlo
    change signal ∉ S.stationary storage at hsource
    have hp : r.cell ⟨1, by omega⟩ ∈ S.stationary storage :=
      ((layout storage I).mem_raster _ _).mpr
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hfirst)))
    exact hsource (hf ▸ hp)
  · let near := r.cell ⟨1 + k, by omega⟩
    have hnear : Adjacent forward signal near := by
      have h := ha.reverse
      simpa only [hd, Direction.opposite_opposite] using h
    have hboxes : t.boxes = insert near ((S.boxes storage).erase stop) := by
      rw [hb, single_slide_boxes r, hf, hstock]
      simp only [near, Nat.add_comm]
    have hpref : Reachable (puzzle storage I).initial t := hprefix.tail hmove
    rcases hcorner with hc | hc
    · have hc' : corner = 3 := Fin.ext hc
      subst corner
      have hsame' : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
          (layout storage I).wireV index.val (layout storage I).wires[index]) =
            (layout storage I).wires[index].sourceSouth := by simpa using hsame
      let E := S.sameSignBFault storage index hsignal hsame' near hnear
      exact E.reject hregister hboxes hpref hsuffix hgoal
    · have hc' : corner = 5 := Fin.ext hc
      subst corner
      have hsame' : (layout storage I).wires[index].targetSouth =
          decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
            (layout storage I).wireV index.val (layout storage I).wires[index]) := by
        simpa using hsame
      let E := S.sameSignCFault storage index hsignal hsame' near hnear
      exact E.reject hregister hboxes hpref hsuffix hgoal

/-- Every original-pin push at any of the five internal wire corners is fatal.
This theorem uses the actual global pin inventory and the actual successful suffix. -/
theorem internal_pin_reject (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
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
  have hc : corner = 1 ∨ corner = 2 ∨ corner = 3 ∨ corner = 4 ∨ corner = 5 := by
    have hcv : corner.val = 1 ∨ corner.val = 2 ∨ corner.val = 3 ∨ corner.val = 4 ∨ corner.val = 5 := by omega
    simpa [Fin.ext_iff] using hcv
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact S.private_pin_reject storage index 1 (by decide) (by decide) hsignal hregister
      (S.first_corner_reverse_clear storage index hsignal) hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
  · exact S.horizontal_pin_reject storage index 2 (Or.inl rfl) hsignal hregister
      hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
  · by_cases hsame : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]) =
          (layout storage I).wires[index].sourceSouth
    · exact S.same_sign_pin_reject storage index 3 (Or.inl rfl) hsignal
        (by simpa using hsame) hregister
        hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
    · exact S.private_pin_reject storage index 3 (by decide) (by decide) hsignal hregister
        (S.middle_corner_reverse_clear storage index hsignal hsame)
        hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
  · exact S.horizontal_pin_reject storage index 4 (Or.inr rfl) hsignal hregister
      hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
  · by_cases hsame : (layout storage I).wires[index].targetSouth =
        decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
          (layout storage I).wireV index.val (layout storage I).wires[index])
    · exact S.same_sign_pin_reject storage index 5 (Or.inr rfl) hsignal
        (by simpa using hsame) hregister
        hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst
    · exact S.private_pin_reject storage index 5 (by decide) (by decide) hsignal hregister
        (S.last_vertical_reverse_clear storage index hsignal hsame)
        hstock ht hprefix hsuffix hgoal r hn hk hmove hb hfirst

end PushPuzzle.PushPush.Doors.Source.Stock
