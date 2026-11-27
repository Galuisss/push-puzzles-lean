/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateBridge
public import PushS.PortEndpointConnections
import all PushS.PortGateBridge
import all PushS.PortGateWalking
import all PushS.PortGateShuttle
import all PushS.PortEndpointConnections
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.ShuttleMacroSegments

/-! Actual core-gap and middle-axis frame connections used by complete-board signal macros. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem zero_in_left_bound (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind)
    (hleft : kind = .orGate ∨ state.internal.getD g.internal false = false) :
    p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ p.x (g.left + 1) := by
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  cases kind with
  | orGate => simp only [Shuttle.Kind.kappa, show (4 : ℤ).toNat = 4 from rfl]; omega
  | andGate =>
    have hl := hleft.resolve_left (by decide)
    simp only [hl, Bool.toNat_false, Shuttle.Kind.kappa, show (2 : ℤ).toNat = 2 from rfl]
    omega

/-- The same real private bridge reaches every low left-gap hole, including negative local offsets. -/
theorem gateLeftGap_connected_via_axis (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hs : state.internal.getD (g.internal + 1) false = false)
    (haxis : state.axes.getD (g.left + 1) false = false)
    (hleft : kind = .orGate ∨ state.internal.getD g.internal false = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + 1)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  let w := (ShuttleMacro.coreRail p g.left ha).cell 0
  have hzero := zero_in_left_bound p state g kind hleft
  have hw := l.gateLowLeft_connected_via_axis p state hg hk ha hs haxis hleft w rfl
    (by change p.x (g.left + 1) ≤ p.x (g.left + 1) ∧ p.x (g.left + 1) ≤ p.x (g.left + 1) + 1; omega) B hB cap
  apply hw.walk_horizontal q (Fin.ext hy) ?_ hB
  intro r hrow hmin hmax
  apply coreWork_hole l p state hg hk ((congrArg Fin.val hrow).trans (by rfl))
  left
  simp only [hs, Bool.false_eq_true, ite_false]
  change min (p.x (g.left + 1)) q.1.val ≤ r.1.val at hmin
  change r.1.val ≤ max (p.x (g.left + 1)) q.1.val at hmax
  omega

/-- The literal left gap meets the frame under exactly the supplied public/private entrance conditions. -/
theorem gateLeftGap_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes)
    (haccess : state.internal.getD (g.internal + 1) false = true ∨
      (kind = .orGate ∧ state.internal.getD g.internal false = false) ∨
      (state.axes.getD (g.left + 1) false = false ∧
        (kind = .orGate ∨ state.internal.getD g.internal false = false)))
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  rcases haccess with hs | ⟨rfl, hl⟩ | ⟨haxis, hleft⟩
  · exact l.gateLeftGap_connected_of_heavy p state hg hk ha hs q hy hlo (by simpa only [hs, ite_true] using hhi) B hB cap
  · apply l.gateLeftGap_connected_of_or p state hg hk ha hl q hy ?_ hhi B hB cap
    have hx0 := readLength_add_lt_x p (g.left + 1) 0
    simp only [hl, Bool.toNat_false, Shuttle.Kind.kappa, show (4 : ℤ).toNat = 4 from rfl] at hlo
    omega
  · by_cases hs : state.internal.getD (g.internal + 1) false = true
    · exact l.gateLeftGap_connected_of_heavy p state hg hk ha hs q hy hlo (by simpa only [hs, ite_true] using hhi) B hB cap
    · have hs0 : state.internal.getD (g.internal + 1) false = false := by
        cases h : state.internal.getD (g.internal + 1) false <;> simp_all
      exact l.gateLeftGap_connected_via_axis p state hg hk ha hs0 haxis hleft q hy hlo
        (by simpa only [hs0, Bool.false_eq_true, ite_false] using hhi) B hB cap

private theorem middle_walk_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1)
    (hx : p.x (g.left + 1) + 4 ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 6) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  apply coreWork_hole l p state hg hk hy
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  have hkappa : 2 ≤ kind.kappa.toNat := by cases kind <;> decide +kernel
  cases state.internal.getD (g.internal + 1) false
  · right
    simp only [Bool.false_eq_true, ite_false]
    omega
  · left
    simp only [ite_true]
    omega

private theorem gateFour_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap ((ShuttleMacro.coreRail p g.left ha).cell 4) := by
  have hxW := x_add_readLength_lt_W p ha 0
  let z : Fin (p.W + 1) := ⟨p.x (g.left + 1) + 6, by omega⟩
  apply workRow_connected l p state (center_of_gate l (placement_gate_mem l hg hk)) _ rfl z ?_ ?_ B hB cap
  · simp [z, gatePublicColumns]
  · intro r hrow hlo hhi
    apply middle_walk_hole l p state hg hk (congrArg Fin.val hrow)
    change min (p.x (g.left + 1) + 4) (p.x (g.left + 1) + 6) ≤ r.1.val at hlo
    change r.1.val ≤ max (p.x (g.left + 1) + 4) (p.x (g.left + 1) + 6) at hhi
    omega

/-- With lower middle-axis supply, its actual two-hole near segment reaches the frame through the private branch. -/
theorem gateAxisNear_connected_of_input (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (haxis : state.axes.getD (g.left + 1) false = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = p.x (g.left + 1))
    (hy : p.H - (readDepth p 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - (readDepth p 1 + 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  let a := bridgeCell p (g.left + 1) ha 4 0
  let b := bridgeCell p (g.left + 1) ha 4 2
  let c := bridgeCell p (g.left + 1) ha 0 2
  have hframe : FrameConnection l p state B cap a := l.gateFour_connected p state hg hk ha B hB cap
  have hbc := hframe.walk_vertical b rfl (fun r hcol hlo hhi =>
    bridgeColumn_hole l p state hg hk ((congrArg Fin.val hcol).trans (by rfl))
      (by dsimp [a, b, bridgeCell] at hlo hhi; omega)) hB
  have hcd := hbc.walk_horizontal c rfl (fun r hrow hlo hhi =>
    bridgeFloor_hole l p state hg hk haxis ((congrArg Fin.val hrow).trans (by rfl))
      (by dsimp [b, c, bridgeCell] at hlo hhi; omega)) hB
  apply hcd.walk_vertical q (Fin.ext hx) ?_ hB
  intro r hcol hlo hhi
  apply axisNear_hole l p state hg hk haxis ((congrArg Fin.val hcol).trans (by rfl))
  dsimp [c, bridgeCell] at hlo hhi
  omega

private theorem axis_first_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = p.H - (readDepth p 1 + 1)) :
    q ∈ (l.cornerState p state).empty := by
  change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)
  rw [gate_full_split l p state hg hk]
  apply Finset.mem_union_right
  apply (ShuttleMacro.coreHoles_mem p state kind g.left g.internal q).mpr
  right; right
  have hb := Bool.toNat_le (state.axes.getD (g.left + 1) false)
  have hH := readDepth_add_lt_H p 1
  exact ⟨hx, by omega, by omega⟩

/-- A supplied left gap reaches the first middle-axis hole, including when that axis has one hole. -/
theorem gateAxisFirst_connected_of_gap (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes)
    (hgap : (state.internal.getD (g.internal + 1) false = true ∧
        (kind = .orGate ∨ state.internal.getD g.internal false = false)) ∨
      (kind = .orGate ∧ state.internal.getD g.internal false = false))
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = p.H - (readDepth p 1 + 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  let w := (ShuttleMacro.coreRail p g.left ha).cell 0
  have hleft : kind = .orGate ∨ state.internal.getD g.internal false = false :=
    hgap.elim (fun h => h.2) (fun h => Or.inl h.1)
  have hw := l.gateLeftGap_connected p state hg hk ha
    (hgap.elim (fun h => Or.inl h.1) (fun h => Or.inr (Or.inl h))) w rfl
    (zero_in_left_bound p state g kind hleft) (by
      change p.x (g.left + 1) ≤ p.x (g.left + 1) + _
      omega) B hB cap
  apply hw.walk_adjacent q (axis_first_hole l p state hg hk hx hy) .north ?_ hB
  have hH := readDepth_add_lt_H p 1
  exact ⟨Fin.ext hx, by change q.2.val + 1 = p.H - readDepth p 1; omega⟩

end PushPuzzle.PushS.PortLayout
