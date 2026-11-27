/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessInterlevel
public import Push.AcceptanceSoundnessPageClosure
public import PushS.PortEndpointTail
import all PushS.PortBackground

/-! Actual descending-layer page and endpoint-tail closure under the deeper-walk invariant. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- Current-layer interlevel holes join the actual complete page blockers along the same true step. -/
theorem canonical_interlevel_page_step_avoiding_of_deeper {u v t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) :
    Freeze.AvoidingStep (l.canonicalInstance p hl hM haxes initial target).board none
      (l.pageBlockers p hl ∪ l.interlevelMarkers p j) u v :=
  (canonical_page_step_avoiding l p hl hM haxes initial target hgate hsu hm hvt ha).union_excluded
    (canonical_interlevel_excluded_at_of_deeper l p hl hM haxes initial target j hj hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ha hP)
    (canonical_interlevel_excluded_at_of_deeper l p hl hM haxes initial target j hj (hsu.tail hm) hvt ha hP)

/-- Every actual accepted prefix avoids the full page blockers and its current descending layer's holes. -/
theorem canonical_interlevel_page_avoiding_prefix_of_deeper {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none
      (l.pageBlockers p hl ∪ l.interlevelMarkers p j))
      (l.canonicalInstance p hl hM haxes initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact canonical_interlevel_page_step_avoiding_of_deeper l p hl hM haxes initial target hgate
    j hj hsa hm (hbu.trans hut) ha hP

/-- The actual descending prefix freezes every page-background box while retaining its current interlevel blockers. -/
private theorem canonical_interlevel_page_closure_avoiding_of_deeper {u t : State (p.W + 1)
    (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none
      (l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p j))
      (l.canonicalInstance p hl hM haxes initial target).initial u :=
  ((l.pageBackground_closure p hl hM haxes (l.canonical initial) (l.canonical target)).adjoin_blockers
    (l.interlevelMarkers p j)).reachable
    (canonical_interlevel_page_avoiding_prefix_of_deeper l p hl hM haxes initial target hgate j hj hsu hut ha hP)

/-- Every actual current-level tail box remains present under the same descending induction invariant. -/
theorem canonical_endpoint_tail_full_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (street : EndpointStreet) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) :
    endpointTail p e street ⊆ u.boxes :=
  (Freeze.anchored_closure
    (l.endpointTail_anchored p hl hM e he heM street _ Finset.subset_union_left Finset.subset_union_right)
    (canonical_interlevel_page_closure_avoiding_of_deeper l p hl hM haxes initial target hgate e.level
      (l.endpoints_level_bounds p hl hM he).1 hsu hut ha hP)
    (l.endpointTail_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) e he street)).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
