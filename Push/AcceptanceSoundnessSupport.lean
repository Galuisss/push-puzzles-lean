/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportFirst
public import Push.AcceptanceSoundnessSupportCoordinatesGeometry
import all Push.AcceptanceSoundnessCentral

/-! Actual accepted endpoints and every real prefix have the original global street support. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical

variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- The two actual endpoint supports and initially full isolated intersections give original streets. -/
private theorem canonical_terminal_original_supported {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (supportCoordinates l p).original (Blocked.fill t (newCentralMarkers l p)) := by
  have hp := canonical_initial_frame l p hl hM haxes initial target
  have hs := canonical_initial_holes l p hl hM haxes initial target
  have hfirst := program_first_supported l p hl hM haxes initial target hr hp hs ha
  have hsecond := program_second_supported l p hl hM haxes initial target hr hp hs ha
  exact canonical_filled_original_of_intersection l p hl hM haxes initial target
    (canonical_newCentralMarkers_fill l p hl hM haxes initial target hr ha)
    (fun q hq => ⟨hfirst q hq, hsecond q hq⟩)

/-- Every actual successful prefix, with its added markers filled, has the original global streets. -/
theorem canonical_original_supported_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (supportCoordinates l p).original (Blocked.fill u (newCentralMarkers l p)) := by
  have hfilled := canonical_newCentralMarkers_fill_between l p hl hM haxes initial target hsu hut .refl ha
  exact (Support.streets_axisClosed (l.streetColumnSet_separated p) (l.workingRowSet_separated p)).reachable_source
    hfilled (canonical_terminal_original_supported l p hl hM haxes initial target (hsu.trans hut) ha)

/-- The real player remains on an original street without any prescribed terminal player position. -/
theorem canonical_player_on_original {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    u.player ∈ (supportCoordinates l p).original := by
  have hv := hsu.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid
  have hg := newCentralMarkers_excluded_at l p hl hM haxes initial target hsu hut
    (canonical_initial_frame l p hl hM haxes initial target) (canonical_initial_holes l p hl hM haxes initial target) ha
  apply canonical_original_supported_at l p hl hM haxes initial target hsu hut ha u.player
  exact fun hb => (Finset.mem_union.mp hb).elim hv.2.2 hg.player

/-- Every complete ray of an actual source push lies on an original street. -/
theorem canonical_push_run_on_original {s u t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hss : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial s)
    (run : Run (l.canonicalInstance p hl hM haxes initial target).board d s n) (hn : 0 < n)
    (hp : u.player = run.cell 1)
    (hb : u.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin (n + 2)) : run.cell i ∈ (supportCoordinates l p).original := by
  have hm : Move (l.canonicalInstance p hl hM haxes initial target).board none d s u :=
    .push (hss.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid) hn trivial run hp hb
  have hs := canonical_player_on_original l p hl hM haxes initial target hss
    ((Relation.ReflTransGen.single ⟨d, hm⟩).trans hut) ha
  have hu := canonical_player_on_original l p hl hM haxes initial target (hss.tail ⟨d, hm⟩) hut ha
  exact Support.streets_axisClosed (l.streetColumnSet_separated p) (l.workingRowSet_separated p)
    (players_adjacent hm) hs hu _ (run.lane i)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
