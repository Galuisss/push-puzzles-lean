/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasForward
public import Push.CyclicReaderFamily

/-! Fixed reader shape and the initial height payment of the seven-round door family. -/

public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

theorem readerRounds_shapes (I : Instance) :
    (readerRounds I).map Round.shape =
      [(true, .south), (true, .west), (true, .north), (true, .east),
        (true, .south), (true, .west), (true, .north)] := by
  rw [readerRounds, Layout.quotaProgram, emit_shapes]
  rfl

private theorem reference_left_empty (I : Instance)
    (p : Cell (layout false I).width (layout false I).height) (hx : p.1.val = 0) :
    p ∈ (layout false I).referenceHoles := by
  apply Finset.mem_compl.mpr
  intro hp
  have hi := (layout_fits false I).goalsRaw_interior (((layout false I).mem_raster _ _).mp hp)
  dsimp at hi
  omega

theorem firstQuota_height (I : Instance) :
    ((layout false I).referenceHoles.filter fun p =>
      p ∈ (Push.Scan.lineCells .south 0).take (layout false I).height).card = (layout false I).height := by
  let L := layout false I
  let line := Push.Scan.lineCells (w := L.width) (h := L.height) .south 0
  have hline : line.length = L.height := by
    have hw := L.width_pos
    simp [line, Push.Scan.lineCells, hw]
  have ht : line.take L.height = line := List.take_of_length_le (by rw [hline])
  have hfilter : (L.referenceHoles.filter fun p => p ∈ line) = line.toFinset := by
    ext p
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · exact And.right
    · intro hp
      exact ⟨reference_left_empty I p ((Push.Scan.mem_lineCells .south 0 p).mp hp), hp⟩
  change (L.referenceHoles.filter fun p => p ∈ line.take L.height).card = L.height
  rw [ht, hfilter, List.toFinset_card_of_nodup (Push.Scan.lineCells_nodup .south 0), hline]

/-- The first actual read request pays an entire source height. -/
private theorem readerRounds_first_request (I : Instance) :
    ∃ requests, Push.CyclicReader.firstRequests (readerRounds I) =
      (0, (layout false I).height) :: requests := by
  change ∃ requests,
    (0, ((layout false I).referenceHoles.filter fun p =>
      p ∈ (Push.Scan.lineCells .south 0).take (layout false I).height).card) :: _ =
      (0, (layout false I).height) :: requests
  rw [firstQuota_height]
  exact ⟨_, rfl⟩

theorem readerRounds_first_height (I : Instance) :
    (readerSource I).height ≤
      ((Push.CyclicReader.firstRequests (readerRounds I)).map Prod.snd).sum := by
  obtain ⟨requests, he⟩ := readerRounds_first_request I
  rw [he, List.map_cons, List.sum_cons]
  change (layout false I).height ≤ (layout false I).height + _
  omega

end PushPuzzle.PushPush.Doors.Source
