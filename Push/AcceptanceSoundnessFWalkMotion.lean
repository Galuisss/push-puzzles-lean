/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessInterlevelPage
public import PushS.PortEndpointLevelFWalk
import all PushS.PortEndpointLevelFWalk
import all PushS.PortEndpointFStock
import all PushS.PortBackground

/-! Real accepted source moves do not export boxes from the current endpoint's f inventory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- Every actual step retains boxes inside a highest-level endpoint's literal f corridor. -/
private theorem canonical_last_fwalk_forward (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Inventory.ForwardStep (l.canonicalInstance p hl hM haxes initial target).board none (endpointFWalk p e) u v := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hpre := canonical_page_avoiding_prefix l p hl hM haxes initial target hgate hsu hut ha
  have hstep := canonical_page_step_avoiding l p hl hM haxes initial target hgate hsu hm hvt ha
  have hguard := (l.endpointOuterWalls_closure p hl hM haxes (l.canonical initial) (l.canonical target)
    e he heM).step hpre hstep
  apply fwalk_forward l p hl haxes e he ?_ ?_ hguard
    (canonical_frame_empty_at l p hl hM haxes initial target hut ha)
    (canonical_player_on_original l p hl hM haxes initial target hsu hut ha)
    (canonical_player_on_original l p hl hM haxes initial target (hsu.tail hm) hvt ha)
  · intro q hq hqf hy r hadj
    have hq' := (mem_endpointFWalk_iff p e q).mp hq
    apply l.endpointOuterWalls_guard p hl hM haxes e he heM hq'.1 hy hqf ?_ hadj
    have hd : readDepth p e.level = p.Y p.levels := by
      rw [heM, readDepth_eq p p.levels_pos le_rfl]
    have hqy := q.2.isLt
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, hd] at hq' ⊢ <;> omega
  · intro q hx hy
    have hd : readDepth p e.level = p.Y p.levels := by
      rw [heM, readDepth_eq p p.levels_pos le_rfl]
    exact Finset.mem_union_right _ (l.endpointStreet_deep_blocker p hl hM haxes e he heM .f hx
      (by simpa only [hd] using hy))

/-- Once deeper walks stay empty, every actual current-level step retains its f-corridor boxes. -/
private theorem canonical_level_fwalk_forward_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) :
    Inventory.ForwardStep (l.canonicalInstance p hl hM haxes initial target).board none (endpointFWalk p e) u v := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hj := (l.endpoints_level_bounds p hl hM he).1
  have hpre := canonical_interlevel_page_avoiding_prefix_of_deeper l p hl hM haxes initial target hgate
    e.level hj hsu hut ha hP
  have hstep := canonical_interlevel_page_step_avoiding_of_deeper l p hl hM haxes initial target hgate
    e.level hj hsu hm hvt ha hP
  have hguard := (l.endpointFBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target)
    e he heM).step hpre hstep
  apply fwalk_forward l p hl haxes e he ?_ ?_ hguard
    (canonical_frame_empty_at l p hl hM haxes initial target hut ha)
    (canonical_player_on_original l p hl hM haxes initial target hsu hut ha)
    (canonical_player_on_original l p hl hM haxes initial target (hsu.tail hm) hvt ha)
  · intro q hq hf hy r hadj
    have hq' := (mem_endpointFWalk_iff p e q).mp hq
    have hqH := q.2.isLt
    have hY := readDepth_add_lt_H p e.level
    have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ readDepth p e.level + 2 := by
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hq' ⊢ <;> omega
    have hg := l.endpointLevelOuterWalls_guard p hl hM haxes e he hq'.1 hy hf hdepth hadj
    rcases Finset.mem_union.mp hg with hw | hp
    · exact Finset.mem_union_right _ hw
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  · intro q hx hy
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (l.endpointTail_start_mem p hl hM e he heM .f hx hy))

/-- Any segment of the actual accepted trajectory preserves the highest-level f inventory monotonically. -/
theorem canonical_last_fwalk_forward_between (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (Inventory.ForwardStep
      (l.canonicalInstance p hl hM haxes initial target).board none (endpointFWalk p e)) u v := by
  apply enrich_path huv
  intro a b hua hm hbv
  exact canonical_last_fwalk_forward l p hl hM haxes initial target hgate e he heM
    (hsu.trans hua) hm (hbv.trans hvt) ha

/-- The actual current-level f inventory is monotone on every segment under the deeper-walk invariant. -/
theorem canonical_level_fwalk_forward_between_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) :
    Relation.ReflTransGen (Inventory.ForwardStep
      (l.canonicalInstance p hl hM haxes initial target).board none (endpointFWalk p e)) u v := by
  apply enrich_path huv
  intro a b hua hm hbv
  exact canonical_level_fwalk_forward_of_deeper l p hl hM haxes initial target hgate e he heM
    (hsu.trans hua) hm (hbv.trans hvt) ha hP

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
