/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCut
public import PushS.PortCentralFreeze
import all PushS.PortBackground
import all PushS.PortInstance
import all PushS.PortSegments

/-! The established common certificate supplies the original geometric and central first-motion closure. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- All original off-street background cells are occupied throughout an actual accepted play. -/
theorem canonical_background_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.backgroundBoxes p ⊆ u.boxes := by
  intro q hq
  obtain ⟨hstreet, hcentral⟩ := (l.mem_backgroundBoxes p q).mp hq
  by_contra hbox
  apply hstreet
  exact canonical_central_filled_supported_at l p hl hM haxes initial target hsu hut ha q
    (fun h => (Finset.mem_union.mp h).elim hbox hcentral)

/-- The true accepted source step avoids every actual geometric blocker along its whole push ray. -/
theorem canonical_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Freeze.AvoidingStep (l.canonicalInstance p hl hM haxes initial target).board none
      (l.geometricBlockers p) u v := by
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb i hblock
  have hGu := canonical_central_markers_excluded_at l p hl hM haxes initial target hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ha
  have hGv := canonical_central_markers_excluded_at l p hl hM haxes initial target (hsu.tail hm) hvt ha
  rcases Finset.mem_union.mp hblock with hcentral | hbackground
  · exact Blocked.run_avoids run hGu hGv hb i hcentral
  · have hstreet := canonical_push_run_on_original l p hl hM haxes initial target hsu run hn hp hb hvt ha i
    exact ((l.mem_backgroundBoxes p (run.cell i)).mp hbackground).1 hstreet

/-- Every real accepted prefix supplies the geometric-blocker trajectory needed by the existing closures. -/
theorem canonical_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep (l.canonicalInstance p hl hM haxes initial target).board none
      (l.geometricBlockers p)) (l.canonicalInstance p hl hM haxes initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact canonical_step_avoiding l p hl hM haxes initial target hsa hm (hbu.trans hut) ha

/-- All full original central auxiliary components remain occupied on the common accepted trajectory. -/
theorem canonical_central_auxiliary_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.centralAuxiliaryBoxes p ⊆ u.boxes :=
  (Freeze.anchored_closure (l.centralAuxiliaryBoxes_anchored p)
    (canonical_avoiding_prefix l p hl hM haxes initial target hsu hut ha)
    (l.centralAuxiliaryBoxes_initial_full p hl hM haxes (l.canonical initial) (l.canonical target))).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
