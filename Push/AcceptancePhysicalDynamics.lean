/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisClosure
public import Push.AcceptanceGateRailTerminal
public import Push.AcceptanceWireTrainMotion
public import Push.AcceptanceOrdinaryReaderClosure
public import Push.AcceptanceOrdinaryFailureTrace
import all PushS.PortGateIndexing
import all PushS.PortWireTrains
import all PushS.PortSegments

/-! Terminal numerical inventories supply complete actual train dynamics and both words at every endpoint. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

/-- The physical open-rail hole inventory of every actual three-port gate at one terminal state. -/
structure GateRailInventories (l : PortLayout) (p : Scales.Parameters)
    (t : State (p.W + 1) (p.H + 1)) : Prop where
  gate : ∀ g, g ∈ placements l → ∀ kind, g.gate = some kind →
    (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hlegal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hlegal

/-- Numerical terminal axis and gate-rail stocks supply every actual horizontal train motion. -/
private theorem canonical_rail_motions_of_inventory {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : AxisInventories l p t) (railInventory : GateRailInventories l p t) :
    RailMotions l p (I).board u v := by
  constructor
  · intro g hg hw
    exact canonical_wire_train_step l p hl hM haxes initial target hgate hg hw hsu step hvt accepted
  · intro g hg kind hk
    exact canonical_gateRail_motion_of_terminal l p hl hM haxes initial target hgate hlegal hg hk hsu step hvt accepted
      (axisInventory.gate g hg kind hk) (railInventory.gate g hg kind hk)

/-- Each actual endpoint has its own complete horizontal word throughout the same numerically balanced trace. -/
private theorem canonical_endpoint_horizontal_readout_of_inventory (e : Endpoint)
    (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : AxisInventories l p t) (railInventory : GateRailInventories l p t) :
    ∃ horizontal, EndpointHorizontalReadout p e u horizontal := by
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨first, shape⟩ := canonical_wire_train_shape l p hl hM haxes initial target hgate hg hk hsu hut accepted
    have word := shape.readout (l.wireTrainLength_positive p hl hg hk)
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · exact ⟨_, word.left_endpoint hl hg hk⟩
    · exact ⟨_, word.right_endpoint hl hg hk⟩
  | some kind =>
    obtain ⟨b, shape⟩ := canonical_gateRail_shape_at l p hl hM haxes initial target hgate hlegal hg hk hsu hut accepted
      (axisInventory.gate g hg kind hk) (railInventory.gate g hg kind hk)
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · exact ⟨(gateTrainPlacement p g b).left, shape.left_endpoint hl hg hk⟩
    · exact ⟨(gateTrainPlacement p g b).right, shape.right_endpoint hl hg hk⟩

/-- The terminal numerical stocks and actual acceptance give complete physical dynamics on every trajectory to that endpoint. -/
theorem canonical_physical_dynamics_of_inventory {t : State (p.W + 1) (p.H + 1)}
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : AxisInventories l p t) (railInventory : GateRailInventories l p t) :
    AcceptanceOrdinaryFailure.Dynamics l p (I).board (I).initial t := by
  constructor
  · intro u v hsu step hvt
    exact canonical_axis_motions_of_inventory l p hl hM haxes initial target hgate hsu step hvt accepted axisInventory
  · intro u v hsu step hvt
    exact canonical_rail_motions_of_inventory l p hl hM haxes initial target hgate hlegal hsu step hvt accepted axisInventory railInventory
  · intro u hsu hut e he
    obtain ⟨parameter, shift, axis⟩ := canonical_endpoint_axis_readout_of_inventory l p hl hM haxes initial target hgate
      e he hsu hut accepted axisInventory
    obtain ⟨horizontal, rail⟩ := canonical_endpoint_horizontal_readout_of_inventory l p hl hM haxes initial target hgate hlegal
      e he hsu hut accepted axisInventory railInventory
    exact ⟨parameter, shift, horizontal, axis, rail⟩
  · intro u hsu hut e he
    exact canonical_ordinary_boundary l p hl hM haxes initial target hgate e he hsu hut accepted

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
