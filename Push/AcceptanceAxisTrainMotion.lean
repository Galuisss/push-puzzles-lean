/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisInventory
public import Push.AcceptanceAxisReadoutTrain

/-! Actual balanced ordinary axes inherit the original marked train dynamics from their arbitrary terminal rigid layout. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

private theorem terminal_copy {p : Scales.Parameters} {upper lower : Endpoint} {t : State (p.W + 1) (p.H + 1)}
    {terminal : ThreeBlocks} (shape : OrdinaryAxisTrainShape p upper lower t terminal) (state : SignalState) :
    (ordinaryAxisTrainBlocks p upper lower state).withStarts terminal.first terminal.middle terminal.last = terminal := by
  cases terminal
  simp only [ThreeBlocks.withStarts, ordinaryAxisTrainBlocks, ThreeBlocks.mk.injEq]
  exact ⟨trivial, trivial, trivial, shape.first_length.symm, shape.middle_length.symm, shape.last_length.symm⟩

private theorem terminal_line_slots {p : Scales.Parameters} {upper lower : Endpoint} {t : State (p.W + 1) (p.H + 1)}
    {terminal : ThreeBlocks} (shape : OrdinaryAxisTrainShape p upper lower t terminal) :
    (lineBoxes .south (p.x upper.port) (BoxMask.keep t (ordinaryAxis p upper.port))).image Direction.south.position = terminal.slots := by
  rw [BoxMask.lineBoxes_keep]
  · exact shape.slots
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

/-- A balanced actual axis with a genuine gapped terminal layout has the same three rigid trains at every prefix. -/
theorem canonical_ordinaryAxis_shape_of_terminal_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5)
    {terminal : ThreeBlocks} (shape : OrdinaryAxisTrainShape p upper lower t terminal) :
    ∃ blocks, OrdinaryAxisTrainShape p upper lower u blocks := by
  let b := ordinaryAxisTrainBlocks p upper lower (l.canonical initial)
  have positive := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have gapped := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow (l.canonical initial)
  have same := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.middle terminal.last).Gapped := same.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg ThreeBlocks.slots same.symm)
  have before := canonical_ordinaryAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu hut accepted inventory
  have after := canonical_ordinaryAxis_admissible_suffix_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu hut accepted inventory
  have source := l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hu hlow hsuSide hslSide hport
  obtain ⟨blocks, copy, slots⟩ := b.admissible_at positive gapped terminal.first terminal.middle terminal.last terminalGap
    before after source terminalSlots
  refine ⟨blocks, copy.first_length, copy.middle_length, copy.last_length, copy.gapped, ?_⟩
  have mask : (lineBoxes .south (p.x upper.port) (BoxMask.keep u (ordinaryAxis p upper.port)) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ ordinaryAxis p upper.port :=
    BoxMask.lineBoxes_keep (R := ordinaryAxis p upper.port) (axis := .south) (lane := p.x upper.port)
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.south.position) mask).symm.trans slots

/-- A genuine terminal three-train layout and its balanced inventory determine every actual ordinary-axis train motion. -/
theorem canonical_ordinaryAxis_motion_of_terminal_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (step : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5)
    {terminal : ThreeBlocks} (shape : OrdinaryAxisTrainShape p upper lower t terminal) :
    ∃ before after, OrdinaryAxisMotion p upper lower u v before after := by
  let b := ordinaryAxisTrainBlocks p upper lower (l.canonical initial)
  have positive := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have gapped := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow (l.canonical initial)
  have copy := terminal_copy shape (l.canonical initial)
  have terminalGap : (b.withStarts terminal.first terminal.middle terminal.last).Gapped := copy.symm ▸ shape.gapped
  have terminalSlots := (terminal_line_slots shape).trans (congrArg ThreeBlocks.slots copy.symm)
  have before := canonical_ordinaryAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu ((Relation.ReflTransGen.single step).trans hvt) accepted inventory
  have after := canonical_ordinaryAxis_admissible_suffix_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport (hsu.tail step) hvt accepted inventory
  have one := BoxMask.keep_admissible (axis := .south) (lane := p.x upper.port) (ordinaryAxis_runClosed p upper.port)
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) step
    (canonical_ordinaryAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hsu step hvt accepted inventory)
  have source := l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hu hlow hsuSide hslSide hport
  obtain ⟨marked⟩ := b.admissible_step positive gapped terminal.first terminal.middle terminal.last terminalGap
    before one after source terminalSlots
  exact ⟨marked.beforeBlocks, marked.afterBlocks, ordinary_motion_of_markedStep p upper lower (l.canonical initial) positive marked⟩

end PushPuzzle.Push.AcceptanceSoundness
