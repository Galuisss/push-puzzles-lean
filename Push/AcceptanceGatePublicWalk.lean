/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateMarkers
public import Push.AcceptanceSoundnessPageClosure
public import Push.FirstExit
public import PushS.PortGatePublicWalk
import all PushS.PortBackground
import all PushS.PortDeeperBudget
import all PushS.PortSegments

/-! The actual gate public corridors stay empty by their certified boundary closure and accepted frame. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- An actual accepted avoiding prefix carries the empty frame at every intermediate target state. -/
theorem canonical_guarded_frame_prefix {G : Finset (Cell (p.W + 1) (p.H + 1))}
    {u t : State (p.W + 1) (p.H + 1)}
    (guard : Relation.ReflTransGen (Freeze.AvoidingStep (I).board none G) (I).initial u)
    (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (fun a b => Freeze.AvoidingStep (I).board none G a b ∧ Boundary.frame ⊆ holes b) (I).initial u := by
  apply Path.enrich guard
  intro a b _ move hbu
  refine ⟨move, ?_⟩
  have hbt : Reachable (I).board none b t :=
    (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu).trans hut
  intro q hq
  exact (mem_holes _).mpr (fun hb => Finset.disjoint_left.mp
    (canonical_frame_empty_at l p hl hM haxes initial target hbt accepted) hb hq)

include hgate

/-- The actual accepted next step avoids the page blockers and every protected gate interlevel marker. -/
private theorem canonical_gate_marker_step_avoiding_of_deeper {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t) :
    Freeze.AvoidingStep (I).board none (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) u v :=
  (canonical_page_step_avoiding l p hl hM haxes initial target hgate hsu step hvt accepted).union_excluded
    (canonical_gate_interlevel_excluded_of_deeper l p hl hM haxes initial target hsu
      ((Relation.ReflTransGen.single step).trans hvt) accepted deeper)
    (canonical_gate_interlevel_excluded_of_deeper l p hl hM haxes initial target (hsu.tail step) hvt accepted deeper)

/-- Every actual accepted prefix avoids the same page and gate-marker basis. -/
private theorem canonical_gate_marker_avoiding_of_deeper {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p))
      (I).initial u := by
  apply Path.enrich hsu
  intro a b hsa step hbu
  exact canonical_gate_marker_step_avoiding_of_deeper l p hl hM haxes initial target hgate hsa step
    (hbu.trans hut) accepted deeper

/-- All four actual public gate columns remain holes on the complete accepted trajectory. -/
theorem canonical_gate_publicWalk_empty_of_deeper {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t) : gatePublicWalk p middle ⊆ holes u := by
  have guard := (l.gatePublicBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target) hi).reachable
    (canonical_gate_marker_avoiding_of_deeper l p hl hM haxes initial target hgate hsu hut accepted deeper)
  apply (l.gatePublicWalk_emptyBoundary p hl hM haxes hi).reachable_holes
    (canonical_guarded_frame_prefix l p hl hM haxes initial target guard hut accepted)
  have initialHoles : (holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  exact initialHoles.symm ▸ l.gatePublicWalk_subset_encoded p (l.canonical initial) hi

/-- The complete ordinary walk certificate also supplies the four gate corridors and full public-walk invariant. -/
theorem canonical_publicWalkInvariant_of_ordinary {t : State (p.W + 1) (p.H + 1)}
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (ordinary : DeeperWalkInvariant l p hl hM haxes initial target 0 t) :
    PublicWalkInvariant l p hl hM haxes initial target t := by
  intro u hsu hut q hq
  have deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t :=
    fun s hss hst => (l.deeperWalkHoles_antitone p (show 0 ≤ 1 by omega)).trans (ordinary s hss hst)
  rcases Finset.mem_union.mp hq with frame | publicHole
  · exact ordinary u hsu hut (Finset.mem_union_left _ frame)
  obtain ⟨segment, hs, contains⟩ := (SegmentRecipe.mem_holes _ q).mp publicHole
  rcases List.mem_append.mp hs with endpoint | gate
  · obtain ⟨e, he, hsegment⟩ := List.mem_flatMap.mp endpoint
    apply ordinary u hsu hut
    apply Finset.mem_union_right
    apply (SegmentRecipe.mem_holes _ q).mpr
    exact ⟨segment, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he,
      decide_eq_true (by have := (l.endpoints_level_bounds p hl hM he).1; omega)⟩, hsegment⟩, contains⟩
  · obtain ⟨middle, hi, hsegment⟩ := List.mem_flatMap.mp gate
    exact canonical_gate_publicWalk_empty_of_deeper l p hl hM haxes initial target hgate hi hsu hut accepted deeper
      (gatePublicSegments_subset_walk p middle ((SegmentRecipe.mem_holes _ q).mpr ⟨segment, hsegment, contains⟩))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
