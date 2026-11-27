/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGatePrivateClosure
public import Push.AcceptanceGatePublicWalk

/-! The actual accepted private five-cell branch remains empty under the certified public-walk invariant. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The same actual accepted trajectory keeps every five-cell private gate walk empty. -/
theorem canonical_gate_privateWalk_empty_of_walks (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) : gatePrivateWalk p middle ⊆ holes u := by
  have guard := canonical_gate_private_avoiding_of_walks l p hl hM haxes initial target hgate hi hsu hut accepted deeper walks
  apply (l.gatePrivateWalk_emptyBoundary p hl hM haxes hi).reachable_holes
    (canonical_guarded_frame_prefix l p hl hM haxes initial target guard hut accepted)
  have initialHoles : (holes (l.canonicalInstance p hl hM haxes initial target).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  exact initialHoles.symm ▸ l.gatePrivateWalk_subset_encoded p (l.canonical initial) hi

end PushPuzzle.Push.AcceptanceSoundness
