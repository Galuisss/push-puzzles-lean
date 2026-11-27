/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSignalRegions
public import Push.AcceptanceAxisClosure
public import Push.AcceptanceGateRailNoInput
public import Push.AcceptanceSoundnessWireBalanced
import all Push.AcceptanceProgramAxisReadStock
import all PushS.PortAxisGroups
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortSegments
import all PushS.Scales

/-! Actual numerical axis balance makes every signal-region hole account nondecreasing. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSignalRegions

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The real numerical terminal certificate preserves every original principal-axis account. -/
theorem canonical_axis_region_holes_eq {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) (i : Fin l.portCount) :
    (holes t ∩ axisRegion l p i).card = ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ axisRegion l p i).card := by
  obtain ⟨upper, hu, hupper, hp⟩ := l.endpoints_upper_exists hl i.isLt
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl i.isLt
  have outer (side : i.val = groups.lower.left ∨ i.val = groups.lower.right) :
      (holes t ∩ axisRegion l p i).card = ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ axisRegion l p i).card := by
    obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem side
    have hlower := hls.trans groups.lower_side
    have hport := hlp.trans hp.symm
    have notCore : i.val ∉ l.gateCenterCoordinates := by
      intro center
      have col : p.x lower.port ∈ cores l p := List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨i.val, center, by rw [hlp]⟩)
      exact ordinary_axis_not_core l p hl lower hlow hlower col
    have terminal := inventory.ordinary upper lower hu hlow hupper hlower hport
    have start := canonical_ordinaryAxis_holes_of_terminal l p hl hM haxes initial target hgate
      hu hlow hupper hlower hport .refl hr accepted terminal
    have initialCount : ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ ordinaryAxis p upper.port).card = 5 := start
    simp only [axisRegion, ite_eq_right notCore]
    simpa only [hp] using terminal.trans initialCount.symm
  rcases groups.lower_port with left | right | ⟨gate, middle⟩
  · exact outer (Or.inl left)
  · exact outer (Or.inr right)
  · cases kindEq : groups.lower.gate with
    | none => simp only [kindEq, Option.isSome_none, Bool.false_eq_true] at gate
    | some kind =>
      have center : i.val ∈ l.gateCenterCoordinates :=
        middle ▸ center_of_gate l (placement_gate_mem l groups.lower_mem kindEq)
      have terminal := inventory.gate groups.lower groups.lower_mem kind kindEq
      have start := canonical_gateAxis_holes_of_terminal l p hl hM haxes initial target hgate
        groups.lower_mem kindEq .refl hr accepted terminal
      have initialCount : ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ gateAxis p (groups.lower.left + 1)).card = 4 := start
      simp only [axisRegion, ite_eq_left center]
      simpa only [middle] using terminal.trans initialCount.symm

/-- Every actual rail has at least its original hole inventory after the principal axes balance. -/
private theorem canonical_rail_region_holes_ge {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) (g : Placement) (hg : g ∈ placements l) :
    ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ railRegion p g).card ≤ (holes t ∩ railRegion p g).card := by
  cases kindEq : g.gate with
  | none =>
    simp only [railRegion, kindEq]
    exact canonical_wire_holes_mono l p hl hM haxes initial target hgate hg kindEq .refl hr .refl accepted
  | some kind =>
    have path := canonical_gateRail_no_input_prefix_of_axis_inventory l p hl hM haxes initial target hgate
      hg kindEq hr .refl accepted (inventory.gate g hg kind kindEq)
    let R : Finset (Cell (p.W + 1) (p.H + 1)) := gateOpenRail p g
    let start : State (p.W + 1) (p.H + 1) := (I).initial
    have mono : Inventory.count Rᶜ start ≤ Inventory.count Rᶜ t := Inventory.reachable_mono path
    have si := Inventory.count_add_compl R start
    have st := Inventory.count_add_compl R t
    have hi := Inventory.count_add_holes R start
    have ht := Inventory.count_add_holes R t
    have boxes : t.boxes.card = start.boxes.card := hr.card_boxes
    have lower : (holes start ∩ R).card ≤ (holes t ∩ R).card := by
      omega
    simpa only [railRegion, kindEq] using lower

/-- Each member of the actual finite signal family retains at least its original inventory. -/
theorem canonical_signal_family_lower {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) (i : Option (RegionIndex l)) :
    (family l p (holes (I).initial) i).card ≤ (family l p (holes t) i).card := by
  classical
  cases i with
  | none => exact le_rfl
  | some index =>
    cases index with
    | inl axis => exact (canonical_axis_region_holes_eq l p hl hM haxes initial target hgate hr accepted inventory axis).symm.le
    | inr g =>
      exact canonical_rail_region_holes_ge l p hl hM haxes initial target hgate hr accepted inventory g.val
        (List.mem_toFinset.mp g.property)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
