/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RailMaskGeometry
public import PushS.PortAxisInventory
public import PushS.PortGateInventory
import all PushS.PortBackground
import all PushS.PortLayoutCoordinates

/-! Every actual closed signal rail projects to the existing line-label dynamics. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Ordinary WIRE open rails contain every intervening occupied push cell. -/
theorem wireOpenRail_runClosed (p : Scales.Parameters) (g : Placement) : BoxMask.RunClosed (wireOpenRail p g) := by
  have he : wireOpenRail p g = BoxMask.rectangle (p.x g.left + 1) (p.x g.right - 1)
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) := by
    ext q
    simp only [wireOpenRail, BoxMask.rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := readLength_add_lt_x p g.right 0
    omega
  rw [he]
  exact @BoxMask.rectangle_runClosed _ _ _ _ _ _

/-- The complete ordinary main-axis open region contains every intervening occupied push cell. -/
theorem ordinaryAxis_runClosed (p : Scales.Parameters) (port : ℕ) : BoxMask.RunClosed (ordinaryAxis p port) := by
  have he : ordinaryAxis p port = BoxMask.rectangle (p.x port) (p.x port) 1 (p.H - 1) := by
    ext q
    simp only [ordinaryAxis, BoxMask.rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := readDepth_add_lt_H p 0
    omega
  rw [he]
  exact @BoxMask.rectangle_runClosed _ _ _ _ _ _

/-- Gate middle-axis open segments contain every intervening occupied push cell. -/
theorem gateAxis_runClosed (p : Scales.Parameters) (middle : ℕ) : BoxMask.RunClosed (gateAxis p middle) := by
  have he : gateAxis p middle = BoxMask.rectangle (p.x middle) (p.x middle) 1 (p.H - readDepth p 1 - 1) := by
    ext q
    simp only [gateAxis, BoxMask.rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := readDepth_add_lt_H p 1
    omega
  rw [he]
  exact @BoxMask.rectangle_runClosed _ _ _ _ _ _

/-- Three-port horizontal open rails contain every intervening occupied push cell. -/
theorem gateOpenRail_runClosed (p : Scales.Parameters) (g : Placement) : BoxMask.RunClosed (gateOpenRail p g) := by
  have he : gateOpenRail p g = BoxMask.rectangle (p.x g.left + 1) (p.x g.right - 1)
      (p.H - readDepth p 1) (p.H - readDepth p 1) := by
    ext q
    simp only [gateOpenRail, BoxMask.rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := readLength_add_lt_x p g.right 0
    omega
  rw [he]
  exact @BoxMask.rectangle_runClosed _ _ _ _ _ _

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The actual ordinary WIRE occupancy follows the existing admissible horizontal line dynamics. -/
theorem physicalInstance_wire_admissible_prefix {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level))
      (BoxMask.keep (I).initial (wireOpenRail p g)) (BoxMask.keep u (wireOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (wireOpenRail_runClosed p g) ?_
    (l.physicalInstance_wire_balanced_prefix p hl hM ha initial target hg hw hsu hut ht)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The actual ordinary main-axis occupancy follows the existing vertical line dynamics. -/
theorem physicalInstance_ordinaryAxis_admissible_prefix {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x upper.port))
      (BoxMask.keep (I).initial (ordinaryAxis p upper.port)) (BoxMask.keep u (ordinaryAxis p upper.port)) := by
  apply BoxMask.keep_admissible_reachable (ordinaryAxis_runClosed p upper.port) ?_
    (l.physicalInstance_ordinaryAxis_balanced_prefix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The actual gate middle-axis occupancy follows the existing vertical line dynamics. -/
theorem physicalInstance_gateAxis_admissible_prefix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x (g.left + 1)))
      (BoxMask.keep (I).initial (gateAxis p (g.left + 1))) (BoxMask.keep u (gateAxis p (g.left + 1))) := by
  apply BoxMask.keep_admissible_reachable (gateAxis_runClosed p (g.left + 1)) ?_
    (l.physicalInstance_gateAxis_balanced_prefix p hl hM ha initial target hg hk hsu hut ht)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The actual three-port horizontal occupancy follows the existing line-label dynamics. -/
theorem physicalInstance_gateRail_admissible_prefix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .east (p.H - readDepth p 1))
      (BoxMask.keep (I).initial (gateOpenRail p g)) (BoxMask.keep u (gateOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (gateOpenRail_runClosed p g) ?_
    (l.physicalInstance_gateRail_balanced_prefix p hl hM ha initial target hg hk hsu hut ht)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The remaining successful trajectory preserves the same admissible gate-rail marks. -/
theorem physicalInstance_gateRail_admissible_suffix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .east (p.H - readDepth p 1))
      (BoxMask.keep u (gateOpenRail p g)) (BoxMask.keep t (gateOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (gateOpenRail_runClosed p g) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply enrich_path hut
    intro a b hua hm hbt
    exact ⟨hm, l.physicalInstance_gateRail_inventory_step p hl hM ha initial target hg hk (hsu.trans hua) hm hbt ht⟩

/-- The remaining successful trajectory preserves the same ordinary-axis occupancy marks. -/
theorem physicalInstance_ordinaryAxis_admissible_suffix {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x upper.port))
      (BoxMask.keep u (ordinaryAxis p upper.port)) (BoxMask.keep t (ordinaryAxis p upper.port)) := by
  apply BoxMask.keep_admissible_reachable (ordinaryAxis_runClosed p upper.port) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply enrich_path hut
    intro a b hua hm hbt
    exact ⟨hm, l.physicalInstance_ordinaryAxis_inventory_step p hl hM ha initial target hu hlow hsuSide hslSide hport
      (hsu.trans hua) hm hbt ht⟩

/-- The remaining successful trajectory preserves the same middle-axis occupancy marks. -/
theorem physicalInstance_gateAxis_admissible_suffix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x (g.left + 1)))
      (BoxMask.keep u (gateAxis p (g.left + 1))) (BoxMask.keep t (gateAxis p (g.left + 1))) := by
  apply BoxMask.keep_admissible_reachable (gateAxis_runClosed p (g.left + 1)) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply enrich_path hut
    intro a b hua hm hbt
    exact ⟨hm, l.physicalInstance_gateAxis_inventory_step p hl hM ha initial target hg hk (hsu.trans hua) hm hbt ht⟩

end Solution
end PushPuzzle.PushS.PortLayout
