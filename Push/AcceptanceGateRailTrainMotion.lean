/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateRailProjection
public import Push.AcceptanceRailReadoutTrain

/-! Actual balanced gate rails inherit their complete train motions from an arbitrary genuine terminal layout. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

private theorem terminal_copy {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind} {t : State (p.W + 1) (p.H + 1)}
    {terminal : ThreeBlocks} (shape : GateTrainShape p g kind t terminal) (state : SignalState) :
    (gateTrainBlocks p g kind state).withStarts terminal.first terminal.middle terminal.last = terminal := by
  cases terminal
  simp only [ThreeBlocks.withStarts, gateTrainBlocks, ThreeBlocks.mk.injEq]
  exact ⟨trivial, trivial, trivial, shape.first_length.symm, shape.middle_length.symm, shape.last_length.symm⟩

private theorem terminal_line_slots {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind} {t : State (p.W + 1) (p.H + 1)}
    {terminal : ThreeBlocks} (shape : GateTrainShape p g kind t terminal) :
    (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep t (gateOpenRail p g))).image Direction.east.position = terminal.slots := by
  rw [BoxMask.lineBoxes_keep]
  · exact shape.slots
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

/-- A balanced actual gate rail with a genuine gapped terminal layout has the same three rigid trains at every prefix. -/
theorem canonical_gateRail_shape_of_terminal_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} {kind : Shuttle.Kind} (hg : g ∈ placements l) (hk : g.gate = some kind)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11)
    {terminal : ThreeBlocks} (shape : GateTrainShape p g kind t terminal) :
    ∃ blocks, GateTrainShape p g kind u blocks := by
  let b := gateTrainBlocks p g kind (l.canonical initial)
  have positive := gateTrainBlocks_positive p g kind (l.canonical initial)
  have gapped := gateTrainBlocks_gapped p g kind (l.canonical initial)
  have same := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.middle terminal.last).Gapped := same.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg ThreeBlocks.slots same.symm)
  have before := canonical_gateRail_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hg hk hsu hut accepted axisInventory railInventory
  have after := canonical_gateRail_admissible_suffix_of_terminal l p hl hM haxes initial target hgate
    hg hk hsu hut accepted axisInventory railInventory
  have source := l.physicalInstance_gate_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hg hk
  obtain ⟨blocks, copy, slots⟩ := b.admissible_at positive gapped terminal.first terminal.middle terminal.last terminalGap
    before after source terminalSlots
  refine ⟨blocks, copy.first_length, copy.middle_length, copy.last_length, copy.gapped, ?_⟩
  have mask : (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep u (gateOpenRail p g)) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ gateOpenRail p g :=
    BoxMask.lineBoxes_keep (R := gateOpenRail p g) (axis := .east) (lane := p.H - readDepth p 1)
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.east.position) mask).symm.trans slots

/-- A genuine terminal three-train layout and its balanced inventory determine every actual gate-rail train motion. -/
theorem canonical_gateRail_motion_of_terminal_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} {kind : Shuttle.Kind} (hg : g ∈ placements l) (hk : g.gate = some kind)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (step : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11)
    {terminal : ThreeBlocks} (shape : GateTrainShape p g kind t terminal) :
    ∃ before after, GateTrainMotion p g kind u v before after := by
  let b := gateTrainBlocks p g kind (l.canonical initial)
  have positive := gateTrainBlocks_positive p g kind (l.canonical initial)
  have gapped := gateTrainBlocks_gapped p g kind (l.canonical initial)
  have copy := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.middle terminal.last).Gapped := copy.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg ThreeBlocks.slots copy.symm)
  have before := canonical_gateRail_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hg hk hsu ((Relation.ReflTransGen.single step).trans hvt) accepted axisInventory railInventory
  have after := canonical_gateRail_admissible_suffix_of_terminal l p hl hM haxes initial target hgate
    hg hk (hsu.tail step) hvt accepted axisInventory railInventory
  have one := BoxMask.keep_admissible (axis := .east) (lane := p.H - readDepth p 1) (gateOpenRail_runClosed p g)
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) step
    (canonical_gateRail_inventory_step_of_terminal l p hl hM haxes initial target hgate
      hg hk hsu step hvt accepted axisInventory railInventory)
  have source := l.physicalInstance_gate_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hg hk
  obtain ⟨marked⟩ := b.admissible_step positive gapped terminal.first terminal.middle terminal.last terminalGap
    before one after source terminalSlots
  exact ⟨marked.beforeBlocks, marked.afterBlocks, AcceptanceRailReadout.gate_rail_motion_of_markedStep p g kind (l.canonical initial) positive marked⟩

end PushPuzzle.Push.AcceptanceSoundness
