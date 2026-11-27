/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateOuterMacro
public import PushS.PortGateAxisMacro
public import PushS.PortGateConnections
public import PushS.PortEndpointPocket
import all PushS.PortGateOuterMacro
import all PushS.PortGateConnections
import all PushS.PortEndpointPocket
import all PushS.PortEndpointConnections
import all PushS.PortGateRail
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortSegments

/-! Frame-to-frame actual signal macros for the two outer trains and three-port middle axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem complete_step_from_frame (l : PortLayout) (p : Scales.Parameters)
    (state target : SignalState) (B : Board (p.W + 1) (p.H + 1))
    (s t : HoleState (p.W + 1) (p.H + 1))
    (hs : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (ht : t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))
    (hstart : FrameConnection l p state B none s.player) (hm : Step B none s.toState t.toState)
    (hfinish : FrameConnection l p target B none t.player) :
    Reachable B none (l.cornerState p state).toState (l.cornerState p target).toState := by
  have hs' : s.toState = ⟨s.player,
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))ᶜ⟩ := by
    rw [HoleState.toState, hs]
  have ht' : t.toState = ⟨t.player,
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜ⟩ := by
    rw [HoleState.toState, ht]
  have hsource := hstart.toPoint
  have htarget := hfinish.toCorner
  rw [← hs'] at hsource
  rw [← ht'] at htarget
  exact hsource.trans ((Relation.ReflTransGen.single hm).trans htarget)

private theorem horizontal_station_connected (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (hinput : horizontalInput state e = true)
    (q : Cell (p.W + 1) (p.H + 1)) (dx : ℕ) (hlo : 1 ≤ dx) (hhi : dx ≤ 2)
    (hx : q.1.val = inward (p.x e.port) e.inward dx)
    (hy : q.2.val = onSide (coordinates p) e.side (readDepth p e.level))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) : FrameConnection l p state B none q := by
  apply l.endpointPocket_connected p hl hM ha state e he (Or.inr hinput) q ?_ B hB none
  apply (finite_take_drop p _ 1 q).mpr
  right
  exact horizontal_slot_mem p state e dx hlo (by rw [hinput]; simpa only [Bool.toNat_true] using hhi) hx hy

private theorem axis_station_connected (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (hinput : axisInput state e = true)
    (q : Cell (p.W + 1) (p.H + 1)) (v : ℕ) (hlo : readDepth p e.level ≤ v) (hhi : v ≤ readDepth p e.level + 2)
    (hx : q.1.val = p.x e.port) (hy : q.2.val = onSide (coordinates p) e.side v)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) : FrameConnection l p state B none q := by
  apply l.endpointPocket_connected p hl hM ha state e he (Or.inl hinput) q ?_ B hB none
  apply (finite_take_drop p _ 1 q).mpr
  left
  exact axis_slot_mem p state e hx v hlo (by rw [hinput]; simpa only [Bool.toNat_true, Nat.add_assoc] using hhi) hy

/-- The actual left internal-signal flip starts and finishes on the common empty frame. -/
theorem encodedSegments_gate_left_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (hi : g.internal < state.internal.length)
    (gain : Bool) (hbefore : state.internal.getD g.internal false = !gain)
    (hstand : if gain then state.axes.getD g.left false = false else
      state.internal.getD (g.internal + 1) false = true ∨
        (kind = .orGate ∧ state.axes.getD (g.left + 1) false = false))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := state.internal.set g.internal gain}).toState := by
  have hmid : g.left + 1 < p.axes := (gate_middle_lt l hl (placement_gate_mem l hg hk)).trans_le ha
  have hshape := placement_gate_shape l hg hk
  have hleft := (gate_endpoints l hg hk).1
  have hrow := gate_workrow l p hg hk
  cases gain
  · simp only [Bool.false_eq_true, ite_false] at hstand
    simp only [Bool.not_false] at hbefore
    have hxW := x_add_readLength_lt_W p hmid 0
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x (g.left + 1) + 3 - kind.kappa.toNat, by omega⟩, ⟨p.H - readDepth p 1, by omega⟩)
    have haccess : state.internal.getD (g.internal + 1) false = true ∨
        (kind = .orGate ∧ state.internal.getD g.internal false = false) ∨
        (state.axes.getD (g.left + 1) false = false ∧ (kind = .orGate ∨ state.internal.getD g.internal false = false)) :=
      hstand.elim Or.inl (fun h => Or.inr (Or.inr ⟨h.2, Or.inl h.1⟩))
    have hkappa : 2 ≤ kind.kappa.toNat := by cases kind <;> decide +kernel
    have hshort : 1 ≤ (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) := by split <;> decide +kernel
    have hstart := l.gateLeftGap_connected p state hg hk hmid haccess q rfl
      (by simp only [hbefore, Bool.toNat_true]; change _ ≤ p.x (g.left + 1) + 3 - kind.kappa.toNat; omega)
      (by change p.x (g.left + 1) + 3 - kind.kappa.toNat ≤ _; omega) B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_left_step p hl hM ha state hg hk hi false hbefore s rfl rfl B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have hshort' : ({state with internal := state.internal.set g.internal false} : SignalState).internal.getD (g.internal + 1) false =
        state.internal.getD (g.internal + 1) false := List.getD_set_ne (by omega)
    have hself : (state.internal.set g.internal false).getD g.internal false = false := List.getD_set_self hi
    have haccess' : ({state with internal := state.internal.set g.internal false} : SignalState).internal.getD (g.internal + 1) false = true ∨
        (kind = .orGate ∧ ({state with internal := state.internal.set g.internal false} : SignalState).internal.getD g.internal false = false) ∨
        (state.axes.getD (g.left + 1) false = false ∧ (kind = .orGate ∨ (state.internal.set g.internal false).getD g.internal false = false)) := by
      rcases hstand with h | ⟨hor, _⟩
      · exact Or.inl (hshort'.trans h)
      · exact Or.inr (Or.inl ⟨hor, hself⟩)
    have hshortMin : 1 ≤ (if (state.internal.set g.internal false).getD (g.internal + 1) false then 6 else 1 : ℕ) := by split <;> decide +kernel
    have hfinish := l.gateLeftGap_connected p {state with internal := state.internal.set g.internal false} hg hk hmid
      haccess' t.player hty (by simp only [hself, Bool.toNat_false]; simp only [Bool.false_eq_true, ite_false] at htx; omega)
      (by simp only [Bool.false_eq_true, ite_false] at htx; omega) B hB none
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish
  · simp only [ite_true] at hstand
    let q := pocketCell l p hl ha (gateLeft g) hleft 1 (readDepth p (gateLeft g).level) (by omega)
    have haxis : axisInput state (gateLeft g) = true := by
      simp only [axisInput, gateLeft, hshape.1, reduceCtorEq, ite_false, hstand, Bool.not_false]
    have hq := horizontal_slot_mem p state (gateLeft g) (q := q) 1 le_rfl (by omega) rfl rfl
    have hstart := l.endpointPocket_connected p hl hM ha state (gateLeft g) hleft (Or.inl haxis) q
      ((finite_take_drop p _ 1 q).mpr (Or.inr hq)) B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_left_step p hl hM ha state hg hk hi true hbefore s rfl
      (Prod.ext rfl hrow) B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have hrecv : horizontalInput {state with internal := state.internal.set g.internal true} (gateLeft g) = true := by
      exact List.getD_set_self hi
    have hfinish := horizontal_station_connected l p hl hM ha _ (gateLeft g) hleft hrecv t.player 2 (by omega) le_rfl htx
      (hty.trans hrow.symm) B hB
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish

/-- The actual relay-train signal flip starts and finishes on the common empty frame. -/
theorem encodedSegments_gate_right_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (hi : g.internal + 2 < state.internal.length)
    (gain : Bool) (hbefore : state.internal.getD (g.internal + 2) false = !gain)
    (hstand : if gain then state.internal.getD (g.internal + 1) false = false
      else state.axes.getD g.right false = false)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := state.internal.set (g.internal + 2) gain}).toState := by
  have hmid : g.left + 1 < p.axes := (gate_middle_lt l hl (placement_gate_mem l hg hk)).trans_le ha
  have hshape := placement_gate_shape l hg hk
  have hright := (gate_endpoints l hg hk).2
  have hrow := gate_workrow l p hg hk
  cases gain
  · simp only [Bool.false_eq_true, ite_false] at hstand
    let q := pocketCell l p hl ha (gateRight g) hright 1 (readDepth p (gateRight g).level) (by omega)
    have haxis : axisInput state (gateRight g) = true := by
      simp only [axisInput, gateRight, hshape.1, reduceCtorEq, ite_false, hstand, Bool.not_false]
    have hq := horizontal_slot_mem p state (gateRight g) (q := q) 1 le_rfl (by omega) rfl rfl
    have hstart := l.endpointPocket_connected p hl hM ha state (gateRight g) hright (Or.inl haxis) q
      ((finite_take_drop p _ 1 q).mpr (Or.inr hq)) B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_right_step p hl hM ha state hg hk hi false hbefore s rfl
      (Prod.ext rfl hrow) B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have hself : (state.internal.set (g.internal + 2) false).getD (g.internal + 2) false = false := List.getD_set_self hi
    have hrecv : horizontalInput {state with internal := state.internal.set (g.internal + 2) false} (gateRight g) = true := by
      change !((state.internal.set (g.internal + 2) false).getD (g.internal + 2) false) = true
      rw [hself]
      rfl
    have hfinish := horizontal_station_connected l p hl hM ha _ (gateRight g) hright hrecv t.player 2 (by omega) le_rfl htx
      (hty.trans hrow.symm) B hB
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish
  · simp only [ite_true] at hstand
    have hxW := x_add_readLength_lt_W p hmid 0
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x (g.left + 1) + 11, by omega⟩, ⟨p.H - readDepth p 1, by omega⟩)
    have hstart := l.gateRightGap_connected_of_low p state hg hk hmid hstand q rfl
      (by change _ + 4 ≤ p.x (g.left + 1) + 11; omega)
      (by change p.x (g.left + 1) + 11 ≤ _; omega) B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_right_step p hl hM ha state hg hk hi true hbefore s rfl rfl B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have hself : (state.internal.set (g.internal + 2) true).getD (g.internal + 2) false = true := List.getD_set_self hi
    have hshortMax : (if (state.internal.set (g.internal + 2) true).getD (g.internal + 1) false then 6 else 1 : ℕ) ≤ 6 := by
      split <;> decide +kernel
    have hfinish := l.gateRightGap_connected p {state with internal := state.internal.set (g.internal + 2) true}
      hg hk hmid hself t.player hty (by
        change p.x (g.left + 1) + (if (state.internal.set (g.internal + 2) true).getD (g.internal + 1) false then 6 else 1) + 3 ≤ t.player.1.val
        simp only [ite_true] at htx
        omega)
      (by simp only [ite_true] at htx; omega) B hB none
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish

/-- The actual middle-axis signal flip starts and finishes on the common empty frame. -/
theorem encodedSegments_gate_axis_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hport : upper.port = g.left + 1)
    (gain : Bool) (hi : g.left + 1 < state.axes.length) (hbefore : state.axes.getD (g.left + 1) false = !gain)
    (hstand : if gain then
      (if upper.inward then state.internal.getD upper.internal false else !(state.internal.getD upper.internal false)) = true
      else (state.internal.getD (g.internal + 1) false = true ∧
          (kind = .orGate ∨ state.internal.getD g.internal false = false)) ∨
        (kind = .orGate ∧ state.internal.getD g.internal false = false))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with axes := state.axes.set (g.left + 1) gain}).toState := by
  have hmid : g.left + 1 < p.axes := (gate_middle_lt l hl (placement_gate_mem l hg hk)).trans_le ha
  cases gain
  · simp only [Bool.false_eq_true, ite_false] at hstand
    have hxW := x_add_readLength_lt_W p hmid 0
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x (g.left + 1), by omega⟩, ⟨p.H - (readDepth p 1 + 1), by omega⟩)
    have hstart := l.gateAxisFirst_connected_of_gap p state hg hk hmid hstand q rfl rfl B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_axis_step p hl hM ha state hg hk hu hsu hport false hi hbefore s rfl rfl B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have hself : (state.axes.set (g.left + 1) false).getD (g.left + 1) false = false := List.getD_set_self hi
    have hH := readDepth_add_lt_H p 1
    have hfinish := l.gateAxisNear_connected_of_input p {state with axes := state.axes.set (g.left + 1) false}
      hg hk hmid hself t.player htx (by simp only [Bool.false_eq_true, ite_false] at hty; omega) B hB none
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish
  · simp only [ite_true] at hstand
    let q := pocketCell l p hl ha upper hu 0 (readDepth p upper.level + 1) (by omega)
    have hqx := pocket_axis_column l p hl ha upper hu (readDepth p upper.level + 1) (by omega)
    have hq := axis_slot_mem p state upper (q := q) hqx _ (by omega) (by omega) rfl
    have hstart := l.endpointPocket_connected p hl hM ha state upper hu (Or.inr hstand) q
      ((finite_take_drop p _ 1 q).mpr (Or.inl hq)) B hB none
    let s := (l.cornerState p state).walk q (hstart.point_hole hB)
    obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_gate_axis_step p hl hM ha state hg hk hu hsu hport true hi hbefore s rfl
      (Prod.ext (by
        have hx : s.player.1.val = p.x upper.port := hqx
        simpa only [hport] using hx) (by simp only [s, HoleState.walk, q, pocketCell, onSide, hsu, ite_true])) B hB
    have htx := congrArg Prod.fst hp
    have hty := congrArg Prod.snd hp
    have haxis : axisInput {state with axes := state.axes.set (g.left + 1) true} upper = true := by
      simp only [axisInput, hsu, ite_true, hport]
      exact List.getD_set_self hi
    have hfinish := axis_station_connected l p hl hM ha _ upper hu haxis t.player (readDepth p upper.level + 2)
      (by omega) le_rfl (by simpa only [hport] using htx) (by simpa only [onSide, hsu, ite_true] using hty) B hB
    exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish

end PushPuzzle.PushS.PortLayout
