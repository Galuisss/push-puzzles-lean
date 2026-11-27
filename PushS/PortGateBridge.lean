/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateWalking
public import PushS.PortGatePrivateWalk
import all PushS.PortGateWalking
import all PushS.PortGatePrivateWalk
import all PushS.PortGateShuttle
import all PushS.ShuttleMacroSegments
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortSegments

/-! The actual three-port private bridge connects the low left gap to the empty frame. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem private_core_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : PrivatePosition p (g.left + 1) (q.1.val, q.2.val)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) :=
  l.gatePrivateWalk_subset_encoded p state (center_of_gate l (placement_gate_mem l hg hk))
    ((mem_gatePrivateWalk p (g.left + 1)).mpr (Or.inr hq))

private theorem axisNear_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : state.axes.getD (g.left + 1) false = false) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x (g.left + 1))
    (hy : p.H - (readDepth p 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - (readDepth p 1 + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [gate_full_split l p state hg hk]
  apply Finset.mem_union_right
  apply (ShuttleMacro.coreHoles_mem p state kind g.left g.internal q).mpr
  right; right
  simpa only [ha, Bool.toNat_false, Nat.sub_zero] using And.intro hx hy

private theorem lowLeft_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (hs : state.internal.getD (g.internal + 1) false = false)
    (hleft : kind = .orGate ∨ state.internal.getD g.internal false = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1)
    (hx : p.x (g.left + 1) ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  apply coreWork_hole l p state hg hk hy
  left
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  rw [hs]
  cases kind with
  | orGate =>
    simp only [Shuttle.Kind.kappa, show (4 : ℤ).toNat = 4 from rfl, Bool.false_eq_true, ite_false]
    omega
  | andGate =>
    have hl := hleft.resolve_left (by decide)
    simp only [hl, Bool.toNat_false, Shuttle.Kind.kappa, show (2 : ℤ).toNat = 2 from rfl,
      Bool.false_eq_true, ite_false]
    omega

private theorem bridgeColumn_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1) + 4)
    (hy : p.H - (readDepth p 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - readDepth p 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  by_cases he : q.2.val = p.H - readDepth p 1
  · apply coreWork_hole l p state hg hk he
    have hb := Bool.toNat_le (state.internal.getD g.internal false)
    have hkappa : 2 ≤ kind.kappa.toNat := by cases kind <;> decide +kernel
    cases hs : state.internal.getD (g.internal + 1) false
    · right
      simp only [Bool.false_eq_true, ite_false]
      omega
    · left
      simp only [ite_true]
      omega
  · apply private_core_hole l p state hg hk
    have hY := readDepth_add_lt_H p 1
    dsimp only [PrivatePosition]
    exact Or.imp (fun h => ⟨hx, h⟩) (fun h => ⟨h, by omega, by omega⟩)
      (show q.2.val = p.H - (readDepth p 1 + 1) ∨ q.2.val = p.H - (readDepth p 1 + 2) by omega)

private theorem bridgeFloor_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : state.axes.getD (g.left + 1) false = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - (readDepth p 1 + 2))
    (hx : p.x (g.left + 1) ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 4) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  by_cases he : q.1.val = p.x (g.left + 1)
  · exact axisNear_hole l p state hg hk ha he ⟨by omega, by omega⟩
  · apply private_core_hole l p state hg hk
    exact Or.inr ⟨hy, by omega, hx.2⟩

private theorem bridgeAxis_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (hs : state.internal.getD (g.internal + 1) false = false)
    (ha : state.axes.getD (g.left + 1) false = false)
    (hleft : kind = .orGate ∨ state.internal.getD g.internal false = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : p.H - (readDepth p 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - readDepth p 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  by_cases he : q.2.val = p.H - readDepth p 1
  · exact lowLeft_hole l p state hg hk hs hleft he (by omega)
  · apply axisNear_hole l p state hg hk ha hx
    have hY := readDepth_add_lt_H p 1
    omega

/-- With the short train leftward, its whole right gap meets public column six. -/
theorem gateRightGap_connected_of_low (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hs : state.internal.getD (g.internal + 1) false = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) + 4 ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + 11 + (state.internal.getD (g.internal + 2) false).toNat)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hxW := x_add_readLength_lt_W p ha 0
  let z : Fin (p.W + 1) := ⟨p.x (g.left + 1) + 6, by omega⟩
  apply workRow_connected l p state (center_of_gate l (placement_gate_mem l hg hk)) q hy z ?_ ?_ B hB cap
  · simp [z, gatePublicColumns]
  · intro r hrow hleft hright
    apply coreWork_hole l p state hg hk ((congrArg Fin.val hrow).trans hy)
    right
    simp only [hs, Bool.false_eq_true, ite_false]
    dsimp only [z] at hleft hright
    omega

private def bridgeCell (p : Scales.Parameters) (middle : ℕ) (ha : middle < p.axes)
    (dx : Fin 5) (depth : Fin 3) : Cell (p.W + 1) (p.H + 1) :=
  (⟨p.x middle + dx.val, by have := x_add_readLength_lt_W p ha 0; have := dx.isLt; omega⟩,
    ⟨p.H - (readDepth p 1 + depth.val), by omega⟩)

/-- The actual five-cell private branch and two axis holes give low-left access from the frame. -/
theorem gateLowLeft_connected_via_axis (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hs : state.internal.getD (g.internal + 1) false = false)
    (haxis : state.axes.getD (g.left + 1) false = false)
    (hleft : kind = .orGate ∨ state.internal.getD g.internal false = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hx : p.x (g.left + 1) ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 1)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  let a := bridgeCell p (g.left + 1) ha 4 0
  let b := bridgeCell p (g.left + 1) ha 4 2
  let c := bridgeCell p (g.left + 1) ha 0 2
  let d := bridgeCell p (g.left + 1) ha 0 0
  have haH := bridgeColumn_hole l p state hg hk (q := a) rfl (by dsimp [a, bridgeCell]; omega)
  have hbH := bridgeColumn_hole l p state hg hk (q := b) rfl (by dsimp [b, bridgeCell]; omega)
  have hcH := bridgeFloor_hole l p state hg hk haxis (q := c) rfl (by dsimp [c, bridgeCell]; omega)
  have hdH := bridgeAxis_hole l p state hg hk hs haxis hleft (q := d) rfl (by dsimp [d, bridgeCell]; omega)
  have hqH := lowLeft_hole l p state hg hk hs hleft hy hx
  have hframe := l.gateRightGap_connected_of_low p state hg hk ha hs a rfl
    (by dsimp [a, bridgeCell]; omega) (by dsimp [a, bridgeCell]; omega) B hB cap
  have hab := ((l.cornerState p state).walk a haH).walk_vertical b hbH rfl (fun r hcol hlo hhi =>
    bridgeColumn_hole l p state hg hk ((congrArg Fin.val hcol).trans (by rfl))
      (by dsimp [a, b, bridgeCell, HoleState.walk] at hlo hhi; omega)) B hB cap
  have hbc := ((l.cornerState p state).walk b hbH).walk_horizontal c hcH rfl (fun r hrow hlo hhi =>
    bridgeFloor_hole l p state hg hk haxis ((congrArg Fin.val hrow).trans (by rfl))
      (by dsimp [b, c, bridgeCell, HoleState.walk] at hlo hhi; omega)) B hB cap
  have hcd := ((l.cornerState p state).walk c hcH).walk_vertical d hdH rfl (fun r hcol hlo hhi =>
    bridgeAxis_hole l p state hg hk hs haxis hleft ((congrArg Fin.val hcol).trans (by rfl))
      (by dsimp [c, d, bridgeCell, HoleState.walk] at hlo hhi; omega)) B hB cap
  have hdq := ((l.cornerState p state).walk d hdH).walk_horizontal q hqH (Fin.ext hy)
    (fun r hrow hlo hhi => lowLeft_hole l p state hg hk hs hleft
      ((congrArg Fin.val hrow).trans (by rfl))
      (by dsimp [d, bridgeCell, HoleState.walk] at hlo hhi; omega)) B hB cap
  have hpath := twoWay_trans ⟨hframe.toPoint, hframe.toCorner⟩
    (twoWay_trans hab (twoWay_trans hbc (twoWay_trans hcd hdq)))
  exact ⟨hpath.1, hpath.2⟩

/-- An OR core with left input reaches its entire left gap through public column minus two. -/
theorem gateLeftGap_connected_of_or (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hk : g.gate = some .orGate)
    (ha : g.left + 1 < p.axes) (hl : state.internal.getD g.internal false = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) - 2 ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hxW := x_add_readLength_lt_W p ha 0
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  have hmin : 1 ≤ (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) := by
    split <;> decide +kernel
  let z : Fin (p.W + 1) := ⟨p.x (g.left + 1) - 2, by omega⟩
  apply workRow_connected l p state (center_of_gate l (placement_gate_mem l hg hk)) q hy z ?_ ?_ B hB cap
  · simp [z, gatePublicColumns]
  · intro r hrow hleft hright
    apply coreWork_hole l p state hg hk ((congrArg Fin.val hrow).trans hy)
    left
    simp only [hl, Bool.toNat_false, Shuttle.Kind.kappa, show (4 : ℤ).toNat = 4 from rfl]
    dsimp only [z] at hleft hright
    omega

/-- Either the OR left street or the literal axis/private bridge reaches the east-push station. -/
theorem gateLowLeftStart_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hs : state.internal.getD (g.internal + 1) false = false)
    (haccess : (kind = .orGate ∧ state.internal.getD g.internal false = false) ∨
      (state.axes.getD (g.left + 1) false = false ∧
        (kind = .orGate ∨ state.internal.getD g.internal false = false)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap ((ShuttleMacro.coreRail p g.left ha).cell 1) := by
  rcases haccess with ⟨rfl, hl⟩ | ⟨haxis, hleft⟩
  · apply l.gateLeftGap_connected_of_or p state hg hk ha hl _ rfl
      (by change p.x (g.left + 1) - 2 ≤ p.x (g.left + 1) + 1; omega) ?_ B hB cap
    change p.x (g.left + 1) + 1 ≤ _
    simp only [hs, Bool.false_eq_true, ite_false]
    omega
  · exact l.gateLowLeft_connected_via_axis p state hg hk ha hs haxis hleft _ rfl
      (by change p.x (g.left + 1) ≤ p.x (g.left + 1) + 1 ∧
        p.x (g.left + 1) + 1 ≤ p.x (g.left + 1) + 1; omega) B hB cap

/-- The complete eastward short-train macro also starts and ends at the actual frame corner. -/
theorem encodedSegments_core_east_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (ha : g.left + 1 < p.axes)
    (hi : g.internal + 1 < state.internal.length)
    (hs : state.internal.getD (g.internal + 1) false = false)
    (haccess : (kind = .orGate ∧ state.internal.getD g.internal false = false) ∨
      (state.axes.getD (g.left + 1) false = false ∧
        (kind = .orGate ∨ state.internal.getD g.internal false = false)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p (ShuttleMacro.withShort state g.internal true)).toState := by
  have hstart := l.gateLowLeftStart_connected p state hg hk ha hs haccess B hB none
  have hfinish := l.gateLeftGap_connected_of_heavy p (ShuttleMacro.withShort state g.internal true)
    hg hk ha (ShuttleMacro.withShort_short state g.internal true hi)
    ((ShuttleMacro.coreRail p g.left ha).cell 6) rfl (by
      have hb := Bool.toNat_le ((ShuttleMacro.withShort state g.internal true).internal.getD g.internal false)
      have hkappa : 2 ≤ kind.kappa.toNat := by cases kind <;> decide +kernel
      change _ ≤ p.x (g.left + 1) + 6
      omega) (by change p.x (g.left + 1) + 6 ≤ p.x (g.left + 1) + 6; rfl) B hB none
  exact hstart.toPoint.trans ((l.encodedSegments_core_east_five p hl hM haxes state hg hk ha hi hs B hB).trans hfinish.toCorner)

end PushPuzzle.PushS.PortLayout
