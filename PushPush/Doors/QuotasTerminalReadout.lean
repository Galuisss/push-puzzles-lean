/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasNeighborWitness
public import PushPush.Doors.QuotasTerminalFrame

/-! Actual seven-round whole-run execution restores the terminal frame and accepting signal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram WholeScan

theorem reader_frame_parked (I : Instance)
    {final : PushFS.State (layout false I).width (layout false I).height}
    (hactual : Reachable (readerSource I).initial final)
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (H : Exec (instructions (readerRounds I)) final.boxesᶜ G) :
    RestoredFrame false I final ∧
      workCell false I (targetRow I) (targetRow_fit false I) ∈ final.boxes := by
  obtain ⟨W⟩ := reader_neighbor_witness I H
  have hinterior : Interior final := by
    intro p hp hb
    exact Finset.mem_compl.mp (readerRounds_frame I final.boxesᶜ ⟨G, H.eval⟩ p hb) hp
  have hsupport := hactual.supported hinterior (initial_supported false I)
  have hrack := W.probe.rack_eq hactual hinterior
  have hmarker : ∀ p : Cell (layout false I).width (layout false I).height,
      p.1.val = (layout false I).rackX - 1 → p.2.val ∈ (layout false I).markerRows → p ∈ final.boxes := by
    intro p hx hy
    exact W.probe.marker_box hsupport hrack hy p hx rfl
  have hneighbor : ∀ p : Cell (layout false I).width (layout false I).height,
      p.1.val = (layout false I).rackX - 1 → p.2.val ∈ (layout false I).dividerNeighbors → p ∉ final.boxes := by
    intro p hx hy
    exact W.source_empty (fun _ hr _ hp hy => W.probe.neighbor_capacity hsupport hrack hr _ hp hy) p hx hy
  refine ⟨restoredFrame_of_probes hactual hinterior ?_ hmarker hneighbor, ?_⟩
  · intro p hp
    have hrow : p.2.val ∈ (layout false I).rackProbeRows :=
      List.mem_map.mpr ⟨(p.1.val, p.2.val), List.mem_toFinset.mp hp, rfl⟩
    exact W.probe.rack_box hsupport hrow p ((layout false I).rack_column hp) rfl
  · apply hmarker _ rfl
    apply List.mem_map.mpr
    exact ⟨(layout false I).stop, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

theorem reader_terminal_of_exec (I : Instance)
    {final : PushFS.State (layout false I).width (layout false I).height}
    (hactual : Reachable (readerSource I).initial final)
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (H : Exec (instructions (readerRounds I)) final.boxesᶜ G)
    (hcolumns : PrivateColumnInventory false I final.boxes) : ReaderTerminal I final := by
  obtain ⟨hframe, hpark⟩ := reader_frame_parked I hactual H
  exact ⟨hframe, hcolumns, hpark⟩

end PushPuzzle.PushPush.Doors.Source
