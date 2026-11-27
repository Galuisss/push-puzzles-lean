/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGatePlayerColumns
public import Push.AcceptanceRailReadoutFailure
public import PushS.PortGateRelayFailure
import all PushS.PortGateRelayFailure
import all PushS.PortGateCoreFailure
import all PushS.PortGateIndexing

/-! The actual accepted two-page support keeps a relay fault's true J inaccessible. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- The next actual accepted player cannot enter a relay fault's previous J from outside it. -/
private theorem canonical_gate_relay_no_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) :
    v.player ∉ gateRightGap p g (gateTrainPlacement p g b) := by
  intro inside
  have bounds := gateRightGap_relay_bounds p g _ fault.short fault.right inside
  have row := (Finset.mem_filter.mp inside).2.1
  have hut := (Relation.ReflTransGen.single step).trans hvt
  obtain ⟨d, move⟩ := step
  have adjacent := players_adjacent move
  have playerHole : u.player ∈ holes u := (mem_holes _).mpr move.valid_source.2.2
  have shape := (placement_gate_shape l hg hk).2
  cases d with
  | north =>
    have hx := congrArg Fin.val adjacent.1
    have hy := adjacent.2
    exact canonical_gate_relay_vertical_excluded l p hl hM haxes initial target hg hk hsu hut accepted
      (Or.inr (by omega)) ⟨by omega, by omega⟩
  | south =>
    have hx := congrArg Fin.val adjacent.1
    have hy := adjacent.2
    exact canonical_gate_relay_vertical_excluded l p hl hM haxes initial target hg hk hsu hut accepted
      (Or.inl (by omega)) ⟨by omega, by omega⟩
  | east =>
    have hy := congrArg Fin.val adjacent.2
    exact horizontal_excluded fault.shape shape fault.short fault.right fault.outside inside
      (by omega) (Or.inl adjacent.1.symm) playerHole
  | west =>
    have hy := congrArg Fin.val adjacent.2
    exact horizontal_excluded fault.shape shape fault.short fault.right fault.outside inside
      (by omega) (Or.inr adjacent.1) playerHole

/-- Genuine rail motion on the actual accepted run preserves the full relay fault and its outside player. -/
private theorem canonical_gate_relay_failure_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (rails : RailMotions l p (I).board u v) {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) :
    ∃ c, GateRelayFault p g kind v c := by
  obtain ⟨before, after, motion⟩ := rails.gate g hg kind hk
  have equal := motion.before_shape.unique fault.shape
  subst before
  have shape := (placement_gate_shape l hg hk).2
  have thresholds := motion.relay_fault_preserved shape fault.outside fault.short fault.right
  have outside := canonical_gate_relay_no_entry l p hl hM haxes initial target hg hk hsu step hvt accepted fault
  exact ⟨after, motion.after_shape, thresholds.1, thresholds.2,
    fun inside => outside (motion.right_gap_subset shape fault.outside inside)⟩

/-- The same real accepted suffix preserves a relay fault under its genuine rail motions. -/
theorem canonical_gate_relay_failure_suffix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (rails : ∀ {a b}, Reachable (I).board none (I).initial a → Step (I).board none a b →
      Reachable (I).board none b t → RailMotions l p (I).board a b)
    {blocks : ThreeBlocks} (fault : GateRelayFault p g kind u blocks) :
    ∃ next, GateRelayFault p g kind t next := by
  apply readout_suffix hut (GateRelayFault p g kind) ?_ fault
  intro a b hua move hbt current currentFault
  exact canonical_gate_relay_failure_step l p hl hM haxes initial target hg hk (hsu.trans hua) move hbt accepted
    (rails (hsu.trans hua) move hbt) currentFault

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
