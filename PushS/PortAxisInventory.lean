/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisNoExport
public import PushS.PortWireInventory
import all PushS.PortBackground

/-! Exact storage goals close the five-hole inventory of each actual ordinary main axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful prefix retains the actual ordinary axis's initial five holes. -/
theorem physicalInstance_ordinaryAxis_holes {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : (holes u ∩ ordinaryAxis p upper.port).card = 5 := by
  let R := ordinaryAxis p upper.port
  let s : State (p.W + 1) (p.H + 1) := (I).initial
  have hstart : (holes s ∩ R).card = 5 := by
    change (holes (I).initial ∩ R).card = 5
    rw [l.physicalInstance_initial_holes p hl hM ha initial target]
    exact l.encodedSegments_ordinaryAxis_card p hl hM ha initial hu hlow hsuSide hslSide hport
  have hend : (holes t ∩ R).card = 5 := by
    have hgoal : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
      change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
      rw [ht]
      exact l.physicalInstance_goal_holes p hl hM ha initial target
    rw [hgoal]
    exact l.encodedSegments_ordinaryAxis_card p hl hM ha target hu hlow hsuSide hslSide hport
  exact Inventory.holes_of_balanced
    (l.physicalInstance_ordinaryAxis_no_export_prefix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht)
    (l.physicalInstance_ordinaryAxis_no_export_suffix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht)
    hstart hend

/-- The actual ordinary axis's box inventory is fixed by the common storage endpoint count. -/
theorem physicalInstance_ordinaryAxis_inventory_step {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.count (ordinaryAxis p upper.port) u = Inventory.count (ordinaryAxis p upper.port) v := by
  have hbefore := l.physicalInstance_ordinaryAxis_holes p hl hM ha initial target hu hlow hsuSide hslSide hport
    hsu ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hafter := l.physicalInstance_ordinaryAxis_holes p hl hM ha initial target hu hlow hsuSide hslSide hport
    (hsu.tail hm) hvt ht
  have hcu := Inventory.count_add_holes (ordinaryAxis p upper.port) u
  have hcv := Inventory.count_add_holes (ordinaryAxis p upper.port) v
  omega

/-- No successful physical push transfers a box across an ordinary main-axis boundary. -/
theorem physicalInstance_ordinaryAxis_transfer_iff {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ ordinaryAxis p upper.port ↔ run.cell ⟨n + 1, by omega⟩ ∈ ordinaryAxis p upper.port := by
  have he := l.physicalInstance_ordinaryAxis_inventory_step p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hm hvt ht
  exact Inventory.transfer_iff_of_count run hn hb he

/-- The complete actual prefix retains the ordinary axis's inventory at every step. -/
theorem physicalInstance_ordinaryAxis_balanced_prefix {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (ordinaryAxis p upper.port) a = Inventory.count (ordinaryAxis p upper.port) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, l.physicalInstance_ordinaryAxis_inventory_step p hl hM ha initial target hu hlow hsuSide hslSide hport hsa hm (hbu.trans hut) ht⟩

end Solution
end PushPuzzle.PushS.PortLayout
