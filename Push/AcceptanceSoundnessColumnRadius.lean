/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalks
public import PushS.PortColumnRadius
import all PushS.PortColumnRadius
import all Push.AcceptanceSoundnessCentral

/-! Actual accepted paths keep all initially full deep column crossings occupied and unvisited. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- No successful physical player enters the deep band of an actual shallower endpoint axis. -/
theorem canonical_endpoint_deep_unvisited (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p e.side e.port e.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : u.player ≠ q := by
  apply Radius.player_ne_distant
    (canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target e.level .refl hsu hut
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level hs ht ha))
    (canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level .refl (hsu.trans hut) ha)
    (Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target))
  exact ordinary_deep_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) e he heM hq

/-- An initially occupied point in an actual ordinary axis's deep band remains occupied. -/
theorem canonical_endpoint_deep_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p e.side e.port e.level)
    (hbox : q ∈ (l.canonicalInstance p hl hM haxes initial target).initial.boxes)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : q ∈ u.boxes := by
  by_contra hno
  have hh := Radius.distant_hole_source
    (canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target e.level .refl hsu hut
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level hs ht ha))
    (canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level .refl (hsu.trans hut) ha)
    (Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target))
    (ordinary_deep_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) e he heM hq) ((mem_holes _).mpr hno)
  exact (mem_holes _).mp hh hbox

/-- The lower middle axis of an actual three-port group has no deeper player access. -/
theorem canonical_gate_deep_unvisited (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hlevels : 1 < p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p .lower middle 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : u.player ≠ q := by
  apply Radius.player_ne_distant
    (canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target 1 .refl hsu hut
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht ha))
    (canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 .refl (hsu.trans hut) ha)
    (Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target))
  exact gate_deep_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hi hlevels hq

/-- Initially occupied cells in an actual lower gate axis's deep band remain occupied. -/
theorem canonical_gate_deep_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hlevels : 1 < p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisDeepBand p .lower middle 1)
    (hbox : q ∈ (l.canonicalInstance p hl hM haxes initial target).initial.boxes)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : q ∈ u.boxes := by
  by_contra hno
  have hh := Radius.distant_hole_source
    (canonical_deeper_preserving_between_of_deeper l p hl hM haxes initial target 1 .refl hsu hut
      (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht ha))
    (canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 .refl (hsu.trans hut) ha)
    (Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target))
    (gate_deep_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hi hlevels hq) ((mem_holes _).mpr hno)
  exact (mem_holes _).mp hh hbox

end PushPuzzle.Push.AcceptanceSoundness
