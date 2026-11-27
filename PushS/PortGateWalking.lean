/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.LineWalking
public import PushS.PortGatePublicWalk
public import PushS.PortGateShuttle
import all PushS.EndpointWalking
import all PushS.PortGatePublicWalk
import all PushS.PortGateShuttle
import all PushS.ShuttleMacroSegments

/-! Actual frame access to the four public streets of a three-port core. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Concrete walks between the fixed frame corner and a point of the complete physical encoding. -/
structure FrameConnection (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (B : Board (p.W + 1) (p.H + 1)) (cap : Option ℕ) (q : Cell (p.W + 1) (p.H + 1)) : Prop where
  /-- Reach the point while retaining the complete encoded box set. -/
  toPoint : Reachable B cap (l.cornerState p state).toState
    {player := q, boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))ᶜ}
  /-- Return to the fixed frame corner with the same complete box set. -/
  toCorner : Reachable B cap
    {player := q, boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))ᶜ}
    (l.cornerState p state).toState

private theorem twoWay_trans {w h : ℕ} {B : Board w h} {cap : Option ℕ}
    {s u t : State w h} (hs : Reachable B cap s u ∧ Reachable B cap u s)
    (ht : Reachable B cap u t ∧ Reachable B cap t u) :
    Reachable B cap s t ∧ Reachable B cap t s := ⟨hs.1.trans ht.1, ht.2.trans hs.2⟩

private theorem lowerFrame_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) (x : Fin (p.W + 1)) :
    Reachable B cap (l.cornerState p state).toState (l.pageFrameState p state .lower x).toState ∧
      Reachable B cap (l.pageFrameState p state .lower x).toState (l.cornerState p state).toState := by
  have hw := (l.cornerState p state).walk_line (pageFrameCell p .lower 0)
    (l.pageFrame_hole p state .lower 0) .south p.H rfl (by
      simp only [Direction.position, cornerState, pageFrameCell, reduceCtorEq, ite_false,
        Int.natCast_zero, Int.zero_add])
    (fun r hl _ _ => by
      have hx : r.1 = 0 := Fin.ext hl
      have hr : r = (0, r.2) := Prod.ext hx rfl
      rw [hr]
      exact west_frame_hole l p state r.2) B hB cap
  have he := (l.pageFrameState p state .lower 0).walk_line (pageFrameCell p .lower x)
    (l.pageFrame_hole p state .lower x) .east x.val rfl (by
      simp only [Direction.position, pageFrameCell, pageFrameState, HoleState.walk,
        Fin.val_zero, Int.natCast_zero, Int.zero_add])
    (fun r hl _ _ => by
      have hy : r.2.val = p.H := hl
      have hr : r = pageFrameCell p .lower r.1 := Prod.ext rfl (Fin.ext hy)
      rw [hr]
      exact l.pageFrame_hole p state .lower r.1) B hB cap
  exact twoWay_trans hw he

/-- Every actual public gate-street point is connected to the frame by walks with fixed boxes. -/
theorem gatePublicStreet_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val ∈ gatePublicColumns p middle) (hy : p.H - readDepth p 1 < q.2.val)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hq := l.gatePublicWalk_subset_encoded p state hi
    ((mem_gatePublicWalk p middle).mpr (Or.inr ⟨hx, hy⟩))
  have hv := (l.pageFrameState p state .lower q.1).walk_line q hq .north (p.H - q.2.val) rfl (by
    have hb := q.2.isLt
    simp only [Direction.position, pageFrameState, HoleState.walk, pageFrameCell,
      reduceCtorEq, ite_false]
    omega) (fun r hl hlo hhi => by
      apply l.gatePublicWalk_subset_encoded p state hi
      apply (mem_gatePublicWalk p middle).mpr
      right
      have hcol : r.1.val = q.1.val := hl
      refine ⟨hcol ▸ hx, ?_⟩
      simp only [Direction.position] at hlo hhi
      change -(p.H : ℤ) ≤ -(r.2.val : ℤ) at hlo
      omega) B hB cap
  have hpath := twoWay_trans (lowerFrame_connected l p state B hB cap q.1) hv
  exact ⟨hpath.1, hpath.2⟩

private theorem workRow_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) (q : Cell (p.W + 1) (p.H + 1))
    (hy : q.2.val = p.H - readDepth p 1) (z : Fin (p.W + 1))
    (hz : z.val ∈ gatePublicColumns p middle)
    (hh : ∀ r : Cell (p.W + 1) (p.H + 1), r.2 = q.2 →
      min q.1.val z.val ≤ r.1.val → r.1.val ≤ max q.1.val z.val →
        r ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  let w : Cell (p.W + 1) (p.H + 1) := (z, q.2)
  let a : Cell (p.W + 1) (p.H + 1) := (z, ⟨q.2.val + 1, by omega⟩)
  have hw : w ∈ (l.cornerState p state).empty := hh w rfl (by dsimp [w]; omega) (by dsimp [w]; omega)
  have hq : q ∈ (l.cornerState p state).empty := hh q rfl (by omega) (by omega)
  have ha : a ∈ (l.cornerState p state).empty := l.gatePublicWalk_subset_encoded p state hi
    ((mem_gatePublicWalk p middle).mpr (Or.inr ⟨hz, by dsimp [a]; omega⟩))
  have hcross := ((l.cornerState p state).walk a ha).walk_line w hw .north 1 rfl (by
    change -(q.2.val : ℤ) = -((q.2.val + 1 : ℕ) : ℤ) + 1
    omega) (fun r hl hlo hhi => by
      have hx : r.1.val = z.val := hl
      change -((q.2.val + 1 : ℕ) : ℤ) ≤ -(r.2.val : ℤ) at hlo
      change -(r.2.val : ℤ) ≤ -(q.2.val : ℤ) at hhi
      by_cases hr : r.2 = q.2
      · exact hh r hr (by omega) (by omega)
      · apply l.gatePublicWalk_subset_encoded p state hi
        apply (mem_gatePublicWalk p middle).mpr
        refine Or.inr ⟨hx ▸ hz, ?_⟩
        have hn : r.2.val ≠ q.2.val := fun he => hr (Fin.ext he)
        omega) B hB cap
  have hline := ((l.cornerState p state).walk w hw).walk_horizontal q hq rfl
    (fun r hrow hlo hhi => hh r hrow (by dsimp only [HoleState.walk, w] at hlo; omega)
      (by dsimp only [HoleState.walk, w] at hhi; omega)) B hB cap
  have hframe := l.gatePublicStreet_connected p state hi a hz (by dsimp [a]; omega) B hB cap
  have hpath := twoWay_trans ⟨hframe.toPoint, hframe.toCorner⟩ (twoWay_trans hcross hline)
  exact ⟨hpath.1, hpath.2⟩

private theorem coreWork_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1)
    (hx : (p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1)) ∨
      (p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (g.left + 1) + 11 + (state.internal.getD (g.internal + 2) false).toNat)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [gate_full_split l p state hg hk]
  apply Finset.mem_union_right
  apply (ShuttleMacro.coreHoles_mem p state kind g.left g.internal q).mpr
  exact hx.elim (fun h => Or.inl ⟨h, hy⟩) (fun h => Or.inr (Or.inl ⟨h, hy⟩))

/-- With relay input present, every actual right-gap hole connects to the public frame. -/
theorem gateRightGap_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hr : state.internal.getD (g.internal + 2) false = true)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) + (if state.internal.getD (g.internal + 1) false then 6 else 1) + 3 ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + 12)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hxW := x_add_readLength_lt_W p ha 0
  let z : Fin (p.W + 1) := ⟨p.x (g.left + 1) + 12, by omega⟩
  apply workRow_connected l p state (center_of_gate l (placement_gate_mem l hg hk)) q hy z ?_ ?_ B hB cap
  · simp [z, gatePublicColumns]
  · intro r hrow hleft hright
    apply coreWork_hole l p state hg hk ((congrArg Fin.val hrow).trans hy)
    right
    simp only [hr, Bool.toNat_true]
    dsimp only [z] at hleft hright
    omega

/-- When the short train is rightward, the actual left gap reaches the public column at six. -/
theorem gateLeftGap_connected_of_heavy (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) (hs : state.internal.getD (g.internal + 1) false = true)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.H - readDepth p 1)
    (hlo : p.x (g.left + 1) + 2 + (state.internal.getD g.internal false).toNat - kind.kappa.toNat ≤ q.1.val)
    (hhi : q.1.val ≤ p.x (g.left + 1) + 6)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  have hxW := x_add_readLength_lt_W p ha 0
  let z : Fin (p.W + 1) := ⟨p.x (g.left + 1) + 6, by omega⟩
  apply workRow_connected l p state (center_of_gate l (placement_gate_mem l hg hk)) q hy z ?_ ?_ B hB cap
  · simp [z, gatePublicColumns]
  · intro r hrow hleft hright
    apply coreWork_hole l p state hg hk ((congrArg Fin.val hrow).trans hy)
    left
    simp only [hs, ite_true]
    dsimp only [z] at hleft hright
    omega

/-- The complete westward short-train macro starts and ends at the actual empty frame corner. -/
theorem encodedSegments_core_west_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (ha : g.left + 1 < p.axes)
    (hi : g.internal + 1 < state.internal.length)
    (hs : state.internal.getD (g.internal + 1) false = true)
    (hr : state.internal.getD (g.internal + 2) false = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p (ShuttleMacro.withShort state g.internal false)).toState := by
  have hstart := l.gateRightGap_connected p state hg hk ha hr ((ShuttleMacro.coreRail p g.left ha).cell 9)
    rfl (by change _ ≤ p.x (g.left + 1) + 9; simp only [hs, ite_true]; omega)
    (by change p.x (g.left + 1) + 9 ≤ p.x (g.left + 1) + 12; omega)
    B hB none
  have hr' : (ShuttleMacro.withShort state g.internal false).internal.getD (g.internal + 2) false = true := by
    rw [ShuttleMacro.withShort_other state g.internal false (g.internal + 2) (by omega), hr]
  have hfinish := l.gateRightGap_connected p (ShuttleMacro.withShort state g.internal false) hg hk ha hr'
    ((ShuttleMacro.coreRail p g.left ha).cell 4) rfl (by
      change _ ≤ p.x (g.left + 1) + 4
      rw [ShuttleMacro.withShort_short state g.internal false hi]
      simp only [Bool.false_eq_true, ite_false]
      omega) (by change p.x (g.left + 1) + 4 ≤ p.x (g.left + 1) + 12; omega) B hB none
  exact hstart.toPoint.trans ((l.encodedSegments_core_west_five p hl hM haxes state hg hk ha hi hs B hB).trans hfinish.toCorner)

end PushPuzzle.PushS.PortLayout
