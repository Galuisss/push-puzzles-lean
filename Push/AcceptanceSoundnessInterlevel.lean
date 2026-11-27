/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessMarkers
public import Push.AcceptanceSoundnessSupportFreeze
import all PushS.PortInterlevelFreeze
import all PushS.PortBackground

/-! Actual accepted trajectories exclude the current interlevel markers under the deeper-walk induction invariant. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The descending induction hypothesis: all deeper public walks are holes at every actual prefix. -/
abbrev DeeperWalkInvariant (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (j : ℕ) (t : State (p.W + 1) (p.H + 1)) : Prop :=
  ∀ s, Reachable (l.canonicalInstance p hl hM haxes initial target).board none
    (l.canonicalInstance p hl hM haxes initial target).initial s →
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none s t →
    l.deeperWalkHoles p j ⊆ PushS.holes s

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- The actual deeper-walk invariant supplies the precise preserving relation used by the radius bound. -/
theorem canonical_deeper_preserving_between_of_deeper {u v t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) :
    Relation.ReflTransGen (Radius.PreservingStep
      (l.canonicalInstance p hl hM haxes initial target).board none (l.deeperWalkHoles p j)) u v :=
  deeper_preserving_between l p hl hM haxes (l.canonical initial) (l.canonical target) j hsu huv hvt hP

/-- Actual accepted endpoints and the deeper-walk invariant protect every current ordinary interlevel marker. -/
theorem canonical_interlevel_excluded_at_of_deeper {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) :
    Blocked.Excluded (l.interlevelMarkers p j) u := by
  have hsu' := canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target
    j .refl hsu hut hP
  have hut' := canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target
    j hsu hut .refl hP
  have hPi := hP _ .refl (hsu.trans hut)
  have hp : (l.canonicalInstance p hl hM haxes initial target).initial.player ∈ l.deeperWalkHoles p j :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target))
  have hfinal := canonical_ordinary_interlevel_markers_terminal l p hl hM haxes initial target
    (hsu.trans hut) ha j
  constructor
  · intro q hq
    exact Radius.distant_hole_at hsu' hut' hPi hp (interlevel_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hj hq) (hfinal hq)
  · intro hq
    exact Radius.player_ne_distant hsu' hPi hp (interlevel_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hj hq) rfl

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
