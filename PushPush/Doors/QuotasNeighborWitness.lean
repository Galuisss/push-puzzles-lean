/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasTerminalNeighbors
public import PushPush.Doors.QuotasTerminalProbe

/-! The sixth whole-run read begins at the exact fourth-round residual bitmap. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram WholeScan

private theorem readerRounds_probe_neighbor_prefix (I : Instance) :
    readerRounds I = frameRounds I ++
      [.read .east (probeQuotas I), .read .south [], .read .west (neighborQuotas I)] ++
        (readerRounds I).drop 6 := by
  rfl

structure NeighborWitness (I : Instance)
    (E G : Finset (Cell (layout false I).width (layout false I).height)) where
  probe : ProbeWitness I E
  after : Finset (Cell (layout false I).width (layout false I).height)
  run : Exec (Push.Scan.lines .west (neighborQuotas I)) probe.after after
  finish : Exec (instructions ((readerRounds I).drop 6)) after G

theorem reader_neighbor_witness (I : Instance)
    {E G : Finset (Cell (layout false I).width (layout false I).height)}
    (H : Exec (instructions (readerRounds I)) E G) : Nonempty (NeighborWitness I E G) := by
  have hframe := readerRounds_frame I E ⟨G, H.eval⟩
  rw [readerRounds_probe_neighbor_prefix] at H
  simp only [instructions, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Round.instructions, List.append_nil, List.append_assoc] at H
  change Exec (instructions (frameRounds I) ++ (Push.Scan.lines .east (probeQuotas I) ++
    (Push.Scan.lines .west (neighborQuotas I) ++ instructions ((readerRounds I).drop 6)))) E G at H
  obtain ⟨D, hfirst, hrest⟩ := (Exec.append_iff _ _ _ _).mp H
  have he : D = E \ frameCells I := Option.some.inj
    (hfirst.eval.symm.trans (frameRounds_remaining I E hframe))
  obtain ⟨F, hprobe, hrest⟩ := (Exec.append_iff _ _ _ _).mp hrest
  obtain ⟨J, hneighbor, hfinish⟩ := (Exec.append_iff _ _ _ _).mp hrest
  exact ⟨⟨⟨F, he ▸ hprobe⟩, J, hneighbor, hfinish⟩⟩

theorem NeighborWitness.source_empty {I : Instance}
    {s : PushFS.State (layout false I).width (layout false I).height}
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (W : NeighborWitness I s.boxesᶜ G)
    (hcapacity : ∀ row ∈ (layout false I).dividerNeighbors,
      ∀ p ∈ W.probe.after, p.2.val = row → 0 < p.1.val ∧ p.1.val < (layout false I).rackX)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX - 1)
    (hy : p.2.val ∈ (layout false I).dividerNeighbors) : p ∉ s.boxes :=
  sixth_neighbors_source_empty I W.run (W.probe.run.subset.trans Finset.sdiff_subset) hcapacity p hx hy

end PushPuzzle.PushPush.Doors.Source
