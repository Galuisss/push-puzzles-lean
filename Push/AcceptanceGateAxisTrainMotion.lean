/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisInventory
public import Push.AcceptanceAxisReadoutTrain

/-! Actual balanced gate axes inherit the original marked two-train dynamics from any genuine terminal rigid layout. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

private theorem terminal_copy {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {t : State (p.W + 1) (p.H + 1)} {terminal : TwoBlocks}
    (shape : GateAxisTrainShape p g upper t terminal) (state : SignalState) :
    (gateAxisTrainBlocks p upper state).withStarts terminal.first terminal.last = terminal := by
  cases terminal
  simp only [TwoBlocks.withStarts, gateAxisTrainBlocks, TwoBlocks.mk.injEq]
  exact ⟨trivial, trivial, shape.first_length.symm, shape.last_length.symm⟩

private theorem terminal_line_slots {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {t : State (p.W + 1) (p.H + 1)} {terminal : TwoBlocks} (shape : GateAxisTrainShape p g upper t terminal) :
    (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t (gateAxis p (g.left + 1)))).image Direction.south.position = terminal.slots := by
  rw [BoxMask.lineBoxes_keep]
  · exact shape.slots
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hport : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hg hk hu hsuSide hport

/-- A balanced actual gate axis has the same two gapped rigid trains at every prefix. -/
theorem canonical_gateAxis_shape_of_terminal_shape {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    {terminal : TwoBlocks} (shape : GateAxisTrainShape p g upper t terminal) :
    ∃ blocks, GateAxisTrainShape p g upper u blocks := by
  let b := gateAxisTrainBlocks p upper (l.canonical initial)
  have positive := l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  have gapped := l.gateAxisTrainBlocks_gapped p hl hM hu (l.canonical initial)
  have same := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.last).Gapped := same.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg TwoBlocks.slots same.symm)
  have before := canonical_gateAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate hg hk hsu hut accepted inventory
  have after := canonical_gateAxis_admissible_suffix_of_terminal l p hl hM haxes initial target hgate hg hk hsu hut accepted inventory
  have source := l.physicalInstance_gateAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target) hg hk hu hsuSide hport
  obtain ⟨blocks, copy, slots⟩ := b.admissible_at positive gapped terminal.first terminal.last terminalGap before after source terminalSlots
  refine ⟨blocks, copy.first_length, copy.last_length, copy.gapped, ?_⟩
  have mask : (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep u (gateAxis p (g.left + 1))) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ gateAxis p (g.left + 1) :=
    BoxMask.lineBoxes_keep (R := gateAxis p (g.left + 1)) (axis := .south) (lane := p.x (g.left + 1))
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.south.position) mask).symm.trans slots

/-- The arbitrary genuine terminal two-train layout determines every actual gate-axis step motion. -/
theorem canonical_gateAxis_motion_of_terminal_shape {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    {terminal : TwoBlocks} (shape : GateAxisTrainShape p g upper t terminal) :
    ∃ before after, GateAxisTrainMotion p g upper u v before after := by
  let b := gateAxisTrainBlocks p upper (l.canonical initial)
  have positive := l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  have gapped := l.gateAxisTrainBlocks_gapped p hl hM hu (l.canonical initial)
  have same := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.last).Gapped := same.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg TwoBlocks.slots same.symm)
  have before := canonical_gateAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate hg hk hsu
    ((Relation.ReflTransGen.single step).trans hvt) accepted inventory
  have after := canonical_gateAxis_admissible_suffix_of_terminal l p hl hM haxes initial target hgate hg hk (hsu.tail step) hvt accepted inventory
  have one := BoxMask.keep_admissible (axis := .south) (lane := p.x (g.left + 1)) (gateAxis_runClosed p (g.left + 1))
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) step
    (canonical_gateAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk hsu step hvt accepted inventory)
  have source := l.physicalInstance_gateAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target) hg hk hu hsuSide hport
  obtain ⟨marked⟩ := b.admissible_step positive gapped terminal.first terminal.last terminalGap before one after source terminalSlots
  exact ⟨marked.beforeBlocks, marked.afterBlocks, gate_motion_of_markedStep p g upper (l.canonical initial) positive marked⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
