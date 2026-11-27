/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateGapEntry
public import Push.AcceptanceGateAxisNearEntry
public import Push.AcceptanceGateCoreMotion
public import Push.AcceptanceGateWalks
import all PushS.PortGateCorePrivate
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing

/-! Actual accepted low-core and AND-left private regions exclude every external player entry. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM ha initial target

include hgate

/-- The previous combined G/axis private region cannot be entered from outside in a low-core or private-branch state. -/
theorem canonical_gate_low_private_no_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {state : GateCorePlacement} (readout : GateCoreReadout p g kind upper u state)
    (hleft : -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1)
    (hshort : (gateTrainPlacement p g state.rail).short ≤ 5)
    (hguard : state.axis.parameter ≤ 1 ∨ gateFourInG p g kind state)
    (hout : u.player ∉ gateLowCorePrivate p g kind state) : v.player ∉ gateLowCorePrivate p g kind state := by
  have deeper : DeeperWalkInvariant l p hl hM ha initial target 1 t :=
    fun _ hs ht => canonical_deeperWalk_empty l p hl hM ha initial target hgate 1 hs ht accepted
  have walks := canonical_publicWalkInvariant l p hl hM ha initial target hgate accepted
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
    · rcases canonical_gate_left_gap_entry_of_walks l p hl hM ha initial target hgate hg hk hsu hm hvt accepted deeper walks
        readout.rail_shape hleft hshort hG hin with hb | ⟨hx, hy⟩
      · exact hB (branch_to_gap_four p g kind state haStep hb hin) hb
      · exact axis_inside hx (Or.inl hy)
    · rcases canonical_gate_axis_near_entry_of_walks l p hl hM ha initial target hgate hg hk hsu hm hvt accepted deeper walks
        readout.axis_readout readout.rail_shape hleft hA hin with hg' | ⟨hlarge, hb⟩
      · exact hG hg'
      · rcases hguard with hlow | hfour
        · omega
        · exact hB hfour hb
  · by_cases hfour : gateFourInG p g kind state
    · rw [ite_eq_left hfour] at hin
      have hi : g.left + 1 ∈ l.gateCenterCoordinates := center_of_gate l (placement_gate_mem l hg hk)
      rcases canonical_gate_private_entry_of_walks l p hl hM ha initial target hgate hi hsu hm hvt accepted deeper walks (hB hfour) hin with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hG (four_mem_gap p g kind state hfour hx hy)
      · exact axis_inside hx (Or.inr hy)
    · rw [ite_eq_right hfour] at hin
      exact Finset.notMem_empty _ hin

/-- The previous AND left-fault private region cannot be entered from outside. -/
theorem canonical_gate_and_left_private_no_entry {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {state : GateCorePlacement} (readout : GateCoreReadout p g .andGate upper u state)
    (hleft : 2 ≤ (gateTrainPlacement p g state.rail).left)
    (hshort : (gateTrainPlacement p g state.rail).short ≤ 5)
    (hout : u.player ∉ gateAndLeftPrivate p g state) : v.player ∉ gateAndLeftPrivate p g state := by
  have deeper : DeeperWalkInvariant l p hl hM ha initial target 1 t :=
    fun _ hs ht => canonical_deeperWalk_empty l p hl hM ha initial target hgate 1 hs ht accepted
  have walks := canonical_publicWalkInvariant l p hl hM ha initial target hgate accepted
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
    exact canonical_gate_low_private_no_entry l p hl hM ha initial target hgate hg hk hsu hm hvt accepted readout
      (by omega) hshort (Or.inr hfour) hout
  · have heq : gateAndLeftPrivate p g state = gateLeftGap p g .andGate (gateTrainPlacement p g state.rail) := by
      simp only [gateAndLeftPrivate, hfour, ite_false, Finset.union_empty]
    rw [heq] at hout ⊢
    intro hin
    rcases canonical_gate_left_gap_entry_of_walks l p hl hM ha initial target hgate hg hk hsu hm hvt accepted deeper walks readout.rail_shape
      (by omega) hshort hout hin with hb | ⟨hx, hy⟩
    · exact hfour (branch_to_gap_four p g .andGate state (players_adjacent hm.choose_spec) hb hin)
    · have hzero := axis_to_gap_zero p g .andGate state (players_adjacent hm.choose_spec) hx hy hin
      omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
