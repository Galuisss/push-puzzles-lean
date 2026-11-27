/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessInterlevel
public import PushS.PortGateHalfMarkers
import all PushS.PortGateHalfMarkers
import all PushS.PortGateMarkers
import all PushS.PortBackground

/-! Actual accepted gate markers are excluded by the established deeper and public walk budgets. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- All public corridor cells are holes at every prefix of the same actual source trajectory. -/
abbrev PublicWalkInvariant (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (t : State (p.W + 1) (p.H + 1)) : Prop :=
  ∀ u, Reachable (l.canonicalInstance p hl hM haxes initial target).board none
    (l.canonicalInstance p hl hM haxes initial target).initial u →
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t → l.allPublicWalkHoles p ⊆ holes u

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- The actual accepted five-column gate markers stay empty and unvisited under the first deeper-walk invariant. -/
theorem canonical_gate_interlevel_excluded_of_deeper {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (walks : DeeperWalkInvariant l p hl hM haxes initial target 1 t) :
    Blocked.Excluded (l.gateInterlevelMarkers p) u := by
  have before := canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target 1 .refl hsu hut walks
  have after := canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target 1 hsu hut .refl walks
  have empty := walks _ .refl (hsu.trans hut)
  have player : (I).initial.player ∈ l.deeperWalkHoles p 1 :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target))
  have terminal := canonical_gate_interlevel_markers_terminal l p hl hM haxes initial target (hsu.trans hut) accepted
  have far (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.gateInterlevelMarkers p) :
      ∀ a ∈ l.deeperWalkHoles p 1, (holes (I).initial \ l.deeperWalkHoles p 1).card < distance a q := by
    have budget := l.encodedSegments_outside_deeperWalk_card_le p hl hM haxes (l.canonical initial) le_rfl
    rw [← l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)] at budget
    exact fun a ha => budget.trans_lt (l.gateInterlevelMarkers_far p hl haxes hq a ha)
  constructor
  · intro q hq
    exact Radius.distant_hole_at before after empty player (far q hq) (terminal hq)
  · intro hq
    exact Radius.player_ne_distant before empty player (far u.player hq) rfl

private theorem canonical_public_between_of_public {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (huv : Reachable (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Relation.ReflTransGen (PublicStep l p (I).board) u v := by
  apply enrich_path huv
  intro a b hua move hbv
  have hsa := hsu.trans hua
  have hsb := hsa.tail move
  have hbt := hbv.trans hvt
  exact ⟨⟨move, walks _ hsb hbt⟩,
    canonical_player_on_original l p hl hM haxes initial target hsa ((Relation.ReflTransGen.single move).trans hbt) accepted,
    canonical_player_on_original l p hl hM haxes initial target hsb hbt accepted⟩

/-- Both actual half-depth gate markers stay empty and unvisited once the public walks are certified empty. -/
theorem canonical_gate_half_excluded_of_public {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Blocked.Excluded (l.gateHalfMarkers p) u := by
  have before := canonical_public_between_of_public l p hl hM haxes initial target .refl hsu hut accepted walks
  have after := canonical_public_between_of_public l p hl hM haxes initial target hsu hut .refl accepted walks
  have empty := walks _ .refl (hsu.trans hut)
  have player : (I).initial.player ∈ l.allPublicWalkHoles p :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target))
  have terminal := canonical_gate_half_markers_terminal l p hl hM haxes initial target (hsu.trans hut) accepted
  have far (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.gateHalfMarkers p) :
      ∀ a ∈ l.publicWalkExitSet p, (holes (I).initial \ l.allPublicWalkHoles p).card < distance a q := by
    obtain ⟨middle, hi, hx, hy⟩ := half_marker_data l p hq
    have budget := l.encodedSegments_outside_allPublicWalk_card_le p hl hM haxes (l.canonical initial)
    rw [← l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)] at budget
    exact fun a ha => budget.trans_lt (l.publicWalkExitSet_halfDepth_far p haxes (gate_center_lt l hl hi)
      (by omega) hy a ha)
  constructor
  · intro q hq
    exact Radius.distant_hole_at_from_exits (R := PublicStep l p (I).board)
      (fun {_ _} step => step.1) (fun {_ _} step hin hout => public_step_exit l p hl hM step hin hout)
      before after empty player (half_marker_not_public l p hl haxes (l.canonical initial) hq) (far q hq) (terminal hq)
  · intro hq
    exact Radius.player_ne_distant_from_exits (R := PublicStep l p (I).board)
      (fun {_ _} step => step.1) (fun {_ _} step hin hout => public_step_exit l p hl hM step hin hout)
      before empty player (half_marker_not_public l p hl haxes (l.canonical initial) hq) (far u.player hq) rfl

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
