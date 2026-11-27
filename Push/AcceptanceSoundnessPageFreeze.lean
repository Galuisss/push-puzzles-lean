/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPages
public import PushS.PortPageBackground
import all PushS.PortBackground

/-! The actual accepted path freezes every full box outside the separated physical page streets. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Central marker holes together with the actual full separate-page background. -/
noncomputable def pageGeometryBlockers (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Finset (Cell (p.W + 1) (p.H + 1)) := l.centralMarkers p ∪ l.pageBackgroundBoxes p hl

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- Every actual accepted push ray avoids the central holes and every full separate-page background box. -/
theorem canonical_page_geometry_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Freeze.AvoidingStep (l.canonicalInstance p hl hM haxes initial target).board none
      (pageGeometryBlockers l p hl) u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb i hblock
  rcases Finset.mem_union.mp hblock with hc | hbackground
  · exact Blocked.run_avoids run
      (canonical_central_markers_excluded_at l p hl hM haxes initial target hsu
        ((Relation.ReflTransGen.single hm).trans hvt) ha)
      (canonical_central_markers_excluded_at l p hl hM haxes initial target (hsu.tail hm) hvt ha) hb i hc
  · exact ((l.mem_pageBackgroundBoxes p hl (run.cell i)).mp hbackground).1
      (canonical_push_run_on_pages l p hl hM haxes initial target hsu run hn hp hb hvt ha i)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
