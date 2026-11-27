/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisNoExport
public import PushS.PortRailProjection

/-! A terminal five-hole certificate balances the actual one-way ordinary axis and its complete line dynamics. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {upper lower : Endpoint}
  (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hu hlow hsuSide hslSide hport

/-- The original five-hole terminal inventory fixes the count at every actual ordinary-axis prefix. -/
theorem canonical_ordinaryAxis_holes_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ ordinaryAxis p upper.port).card = 5) : (holes u ∩ ordinaryAxis p upper.port).card = 5 := by
  have initialHoles : (holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  have start : (holes (I).initial ∩ ordinaryAxis p upper.port).card = 5 :=
    (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => (E ∩ ordinaryAxis p upper.port).card) initialHoles).trans
      (l.encodedSegments_ordinaryAxis_card p hl hM haxes (l.canonical initial) hu hlow hsuSide hslSide hport)
  exact Inventory.holes_of_balanced
    (canonical_ordinaryAxis_no_export_prefix l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport hsu hut accepted)
    (canonical_ordinaryAxis_no_export_suffix l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport hsu hut accepted)
    start terminal

/-- A balanced terminal axis makes every actual accepted source step preserve that axis's box inventory. -/
theorem canonical_ordinaryAxis_inventory_step_of_terminal {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    Inventory.count (ordinaryAxis p upper.port) u = Inventory.count (ordinaryAxis p upper.port) v := by
  have before := canonical_ordinaryAxis_holes_of_terminal l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport
    hsu ((Relation.ReflTransGen.single step).trans hvt) accepted terminal
  have after := canonical_ordinaryAxis_holes_of_terminal l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport
    (hsu.tail step) hvt accepted terminal
  have cu := Inventory.count_add_holes (ordinaryAxis p upper.port) u
  have cv := Inventory.count_add_holes (ordinaryAxis p upper.port) v
  omega

/-- The real accepted prefix consists entirely of balanced ordinary-axis steps. -/
private theorem canonical_ordinaryAxis_balanced_prefix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (ordinaryAxis p upper.port) a = Inventory.count (ordinaryAxis p upper.port) b) (I).initial u := by
  apply Path.enrich hsu
  intro a b hsa step hbu
  exact ⟨step, canonical_ordinaryAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsa step (hbu.trans hut) accepted terminal⟩

/-- Masking that real balanced prefix supplies the existing ordinary-axis line dynamics. -/
theorem canonical_ordinaryAxis_admissible_prefix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x upper.port))
      (BoxMask.keep (I).initial (ordinaryAxis p upper.port)) (BoxMask.keep u (ordinaryAxis p upper.port)) := by
  apply BoxMask.keep_admissible_reachable (ordinaryAxis_runClosed p upper.port) ?_
    (canonical_ordinaryAxis_balanced_prefix_of_terminal l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hsu hut accepted terminal)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The remainder of the same actual trajectory supplies balanced ordinary-axis line dynamics as well. -/
theorem canonical_ordinaryAxis_admissible_suffix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x upper.port))
      (BoxMask.keep u (ordinaryAxis p upper.port)) (BoxMask.keep t (ordinaryAxis p upper.port)) := by
  apply BoxMask.keep_admissible_reachable (ordinaryAxis_runClosed p upper.port) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply Path.enrich hut
    intro a b hua step hbt
    exact ⟨step, canonical_ordinaryAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport (hsu.trans hua) step hbt accepted terminal⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
