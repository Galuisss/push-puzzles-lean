/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateCoreMotion
public import PushS.PortGateGapEntry
public import PushS.PortGateAxisNearEntry
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortLayoutCoordinates
import all PushS.PortGatePageWindow

/-! The actual G, private branch and core near interval have no external player entry in each core fault. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Every genuine lower middle-axis hole lies in its current closed core near interval. -/
theorem GateAxisReadout.hole_mem_near {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement} (hr : GateAxisReadout p g upper u a)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : p.D ≤ q.2.val ∧ q.2.val < p.H - readDepth p 1) (hh : q ∈ holes u) :
    q ∈ gateAxisNear p g a.parameter := by
  have h := (hr.core_holes q hx hy).mp hh
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by omega⟩

private theorem branch_to_gap_four (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : GateCorePlacement) {q r : Cell (p.W + 1) (p.H + 1)} {d : Direction}
    (ha : Adjacent d q r) (hq : q ∈ gatePrivateCells p (g.left + 1))
    (hr : r ∈ gateLeftGap p g kind (gateTrainPlacement p g state.rail)) : gateFourInG p g kind state := by
  have hH := readDepth_add_lt_H p 1
  obtain ⟨_, hy, hlo, hhi⟩ := Finset.mem_filter.mp hr
  have hp := (Finset.mem_filter.mp hq).2
  change ((q.1.val = p.x (g.left + 1) + 4 ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
    (q.2.val = p.H - (readDepth p 1 + 2) ∧ p.x (g.left + 1) + 1 ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 4)) at hp
  constructor <;> cases d <;> simp only [Adjacent] at ha <;> omega

private theorem axis_to_gap_zero (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : GateCorePlacement) {q r : Cell (p.W + 1) (p.H + 1)} {d : Direction}
    (ha : Adjacent d q r) (hx : q.1.val = p.x (g.left + 1)) (hy : q.2.val + 1 = p.H - readDepth p 1)
    (hr : r ∈ gateLeftGap p g kind (gateTrainPlacement p g state.rail)) :
    ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1 ≤ 0 := by
  obtain ⟨_, hry, hlo, hhi⟩ := Finset.mem_filter.mp hr
  cases d <;> simp only [Adjacent] at ha <;> omega

private theorem four_mem_gap (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : GateCorePlacement) {q : Cell (p.W + 1) (p.H + 1)}
    (hfour : gateFourInG p g kind state) (hx : q.1.val = p.x (g.left + 1) + 4)
    (hy : q.2.val = p.H - readDepth p 1) : q ∈ gateLeftGap p g kind (gateTrainPlacement p g state.rail) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, ?_⟩
  constructor <;> omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The previous combined G/axis private region cannot be entered from outside in a low-core or private-branch state. -/
theorem physicalInstance_gate_low_private_no_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {state : GateCorePlacement} (readout : GateCoreReadout p g kind upper u state)
    (hleft : -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1)
    (hshort : (gateTrainPlacement p g state.rail).short ≤ 5)
    (hguard : state.axis.parameter ≤ 1 ∨ gateFourInG p g kind state)
    (hout : u.player ∉ gateLowCorePrivate p g kind state) : v.player ∉ gateLowCorePrivate p g kind state := by
  have hG : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g state.rail) :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hA : u.player ∉ gateAxisNear p g state.axis.parameter :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hB (hfour : gateFourInG p g kind state) : u.player ∉ gatePrivateCells p (g.left + 1) := fun h =>
    hout (Finset.mem_union_right _ (by rw [ite_eq_left hfour]; exact h))
  have hh : u.player ∈ holes u := (mem_holes _).mpr hm.choose_spec.valid_source.2.2
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have haStep := players_adjacent hm.choose_spec
  have axis_inside (hx : u.player.1.val = p.x (g.left + 1))
      (hy : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - (readDepth p 1 + 2)) : False := by
    apply hA
    exact readout.axis_readout.hole_mem_near hx (by rcases hy with h | h <;> omega) hh
  intro hin
  rcases Finset.mem_union.mp hin with hin | hin
  · rcases Finset.mem_union.mp hin with hin | hin
    · rcases l.physicalInstance_gate_left_gap_entry p hl hM ha initial target hg hk hsu hm hvt ht
        readout.rail_shape hleft hshort hG hin with hb | ⟨hx, hy⟩
      · exact hB (branch_to_gap_four p g kind state haStep hb hin) hb
      · exact axis_inside hx (Or.inl hy)
    · rcases l.physicalInstance_gate_axis_near_entry p hl hM ha initial target hg hk hsu hm hvt ht
        readout.axis_readout readout.rail_shape hleft hA hin with hg' | ⟨hlarge, hb⟩
      · exact hG hg'
      · rcases hguard with hlow | hfour
        · omega
        · exact hB hfour hb
  · by_cases hfour : gateFourInG p g kind state
    · rw [ite_eq_left hfour] at hin
      have hi : g.left + 1 ∈ l.gateCenterCoordinates := center_of_gate l (placement_gate_mem l hg hk)
      rcases l.physicalInstance_gate_private_entry p hl hM ha initial target hi hsu hm hvt ht (hB hfour) hin with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hG (four_mem_gap p g kind state hfour hx hy)
      · exact axis_inside hx (Or.inr hy)
    · rw [ite_eq_right hfour] at hin
      exact Finset.notMem_empty _ hin

/-- The previous AND left-fault private region cannot be entered from outside. -/
theorem physicalInstance_gate_and_left_private_no_entry {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {state : GateCorePlacement} (readout : GateCoreReadout p g .andGate upper u state)
    (hleft : 2 ≤ (gateTrainPlacement p g state.rail).left)
    (hshort : (gateTrainPlacement p g state.rail).short ≤ 5)
    (hout : u.player ∉ gateAndLeftPrivate p g state) : v.player ∉ gateAndLeftPrivate p g state := by
  have hlower : 1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - Shuttle.Kind.andGate.kappa + 1 := by
    change 1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - 2 + 1
    omega
  by_cases hfour : gateFourInG p g .andGate state
  · have heq : gateAndLeftPrivate p g state = gateLowCorePrivate p g .andGate state := by
      let G : Finset (Cell (p.W + 1) (p.H + 1)) := gateLeftGap p g .andGate (gateTrainPlacement p g state.rail)
      let A : Finset (Cell (p.W + 1) (p.H + 1)) := gateAxisNear p g state.axis.parameter
      let P : Finset (Cell (p.W + 1) (p.H + 1)) := gatePrivateCells p (g.left + 1)
      calc
        _ = G ∪ (P ∪ A) := congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => G ∪ S) (ite_eq_left hfour)
        _ = (G ∪ A) ∪ P := (congrArg (fun S => G ∪ S) (Finset.union_comm P A)).trans (Finset.union_assoc G A P).symm
        _ = _ := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => (G ∪ A) ∪ S) (ite_eq_left hfour)).symm
    rw [heq] at hout ⊢
    exact l.physicalInstance_gate_low_private_no_entry p hl hM ha initial target hg hk hsu hm hvt ht readout
      (by omega) hshort (Or.inr hfour) hout
  · have heq : gateAndLeftPrivate p g state = gateLeftGap p g .andGate (gateTrainPlacement p g state.rail) := by
      simp only [gateAndLeftPrivate, hfour, ite_false, Finset.union_empty]
    rw [heq] at hout ⊢
    intro hin
    rcases l.physicalInstance_gate_left_gap_entry p hl hM ha initial target hg hk hsu hm hvt ht readout.rail_shape
      (by omega) hshort hout hin with hb | ⟨hx, hy⟩
    · exact hfour (branch_to_gap_four p g .andGate state (players_adjacent hm.choose_spec) hb hin)
    · have hzero := axis_to_gap_zero p g .andGate state (players_adjacent hm.choose_spec) hx hy hin
      omega

end Solution
end PushPuzzle.PushS.PortLayout
