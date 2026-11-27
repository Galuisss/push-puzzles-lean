/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideTerminal
public import Push.AcceptanceSoundnessPageFreeze
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all PushS.PortWideFreeze

/-! The actual guard payments protect every wide separator throughout accepted play. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- Actual terminal wide-hole stock and the frame-exit radius bound exclude every wide separator at every prefix. -/
theorem canonical_wide_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Blocked.Excluded (l.wideSeparatorHoles p) u := by
  have hsu' := canonical_central_fill_between l p hl hM haxes initial target .refl hsu hut ha
  have hut' := canonical_central_fill_between l p hl hM haxes initial target hsu hut .refl ha
  have hp := canonical_initial_frame l p hl hM haxes initial target
  have hf := canonical_filled_frame_empty l p target ha
  have hU := canonical_central_filled_supported_at l p hl hM haxes initial target hsu hut ha
  have hT := canonical_central_filled_supported_at l p hl hM haxes initial target (hsu.trans hut) .refl ha
  have hfinal := canonical_wide_separators_terminal l p hl hM haxes initial target hgate (hsu.trans hut) ha
  have hfar (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.wideSeparatorHoles p) :=
    wide_far_exits l p hl haxes (l.canonical initial) _
      (canonical_initial_holes l p hl hM haxes initial target) hq
  constructor
  · intro q hq
    have hfilled : q ∈ PushS.holes (Blocked.fill t (l.centralMarkers p)) := by
      apply (PushS.mem_holes _).mpr
      intro hb
      rcases Finset.mem_union.mp hb with hb | hc
      · exact (PushS.mem_holes _).mp (hfinal hq) hb
      · exact wide_not_central l p hq hc
    have hhole := Support.hole_at_of_frame_exits (l.streetColumnSet_separated p)
      (l.workingRowSet_separated p) hsu' hut' hp hf hT
      (l.wideSeparatorHoles_off_frame p hl hq) (hfar _ hq) hfilled
    exact (PushS.mem_holes _).mpr (fun hb => (PushS.mem_holes _).mp hhole (Finset.mem_union_left _ hb))
  · intro hq
    have hne := Support.player_ne_of_frame_exits (l.streetColumnSet_separated p)
      (l.workingRowSet_separated p) hsu' hp (Boundary.reachable_frame_empty hut' hf) hU
      (l.wideSeparatorHoles_off_frame p hl hq) (hfar _ hq)
    exact hne rfl

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
