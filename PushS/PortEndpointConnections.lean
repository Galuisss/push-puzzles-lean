/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateWalking
import all PushS.PortGateWalking
import all PushS.EndpointWalking

/-! Reversible frame and ordinary endpoint-street walks on the actual complete encoding. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Both physical page-frame rows have fixed-box routes to and from the actual corner. -/
theorem pageFrame_connected (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (side : Side) (x : Fin (p.W + 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap (pageFrameCell p side x) := by
  cases side with
  | lower =>
    have hpath := lowerFrame_connected l p state B hB cap x
    exact ⟨hpath.1, hpath.2⟩
  | upper =>
    have hpath := (l.cornerState p state).walk_horizontal (pageFrameCell p .upper x)
      (l.pageFrame_hole p state .upper x) rfl (fun r hrow _ _ => by
        have hy : r.2.val = 0 := congrArg Fin.val hrow
        have hr : r = pageFrameCell p .upper r.1 := Prod.ext rfl (Fin.ext hy)
        rw [hr]
        exact l.pageFrame_hole p state .upper r.1) B hB cap
    exact ⟨hpath.1, hpath.2⟩

/-- Every actual f/r endpoint-street point is reachable from the frame and can return by walks. -/
theorem endpointStreet_connected (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ) (hd : depth ≤ k.limit p e)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap (endpointStreetCell l p hl ha e he k depth hd) := by
  let q := endpointStreetCell l p hl ha e he k depth hd
  let d : Direction := if e.side = .upper then .south else .north
  have hlimit := k.limit_le p e
  have hq := l.endpointStreet_hole p hl hM ha state e he k depth hd
  have hline := (l.pageFrameState p state e.side q.1).walk_line q hq d depth (by
    cases hs : e.side <;> simp only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.lane,
      pageFrameState, HoleState.walk, pageFrameCell]) (by
    cases hs : e.side <;>
      simp only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.position, pageFrameState,
        HoleState.walk, pageFrameCell, q, endpointStreetCell] <;> omega) (fun r hLane hlo hhi => by
    let v := if e.side = .upper then r.2.val else p.H - r.2.val
    have hv : v ≤ k.limit p e := by
      cases hs : e.side <;>
        simp only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.position, pageFrameState,
          HoleState.walk, pageFrameCell, q, endpointStreetCell] at hlo hhi <;>
        dsimp only [v] <;> simp only [hs, reduceCtorEq, ite_true, ite_false] <;> omega
    have hr : r = endpointStreetCell l p hl ha e he k v hv := by
      apply Prod.ext <;> apply Fin.ext
      · cases hs : e.side <;>
          simpa only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.lane, pageFrameState,
            HoleState.walk, pageFrameCell, q, endpointStreetCell] using hLane
      · have hb := r.2.isLt
        cases hs : e.side <;> simp only [endpointStreetCell, v, hs, reduceCtorEq, ite_true, ite_false]
        omega
    rw [hr]
    exact l.endpointStreet_hole p hl hM ha state e he k v hv) B hB cap
  have hframe := l.pageFrame_connected p state e.side q.1 B hB cap
  have hpath := twoWay_trans ⟨hframe.toPoint, hframe.toCorner⟩ hline
  exact ⟨hpath.1, hpath.2⟩

namespace FrameConnection

variable {l : PortLayout} {p : Scales.Parameters} {state : SignalState}
  {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {q : Cell (p.W + 1) (p.H + 1)}

private theorem point_hole (h : FrameConnection l p state B cap q) (hB : B.walls = ∅) :
    q ∈ (l.cornerState p state).empty := by
  have hv := h.toPoint.valid ((l.cornerState p state).valid B hB)
  change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)
  simpa only [Finset.mem_compl, not_not] using hv.2.2

/-- Extend a concrete frame connection by one real walk and its reverse. -/
theorem walk_adjacent (h : FrameConnection l p state B cap q) (r : Cell (p.W + 1) (p.H + 1))
    (hr : r ∈ (l.cornerState p state).empty) (d : Direction) (ha : Adjacent d q r)
    (hB : B.walls = ∅) : FrameConnection l p state B cap r := by
  let s := (l.cornerState p state).walk q (h.point_hole hB)
  have hout := s.walk_move hr ha B hB cap
  have hback := (s.walk r hr).walk_move (h.point_hole hB) ha.reverse B hB cap
  have hpath := twoWay_trans ⟨h.toPoint, h.toCorner⟩
    ⟨Relation.ReflTransGen.single ⟨d, hout⟩, Relation.ReflTransGen.single ⟨d.opposite, hback⟩⟩
  exact ⟨hpath.1, hpath.2⟩

/-- Extend a concrete frame connection along a horizontal line of actual holes. -/
theorem walk_horizontal (h : FrameConnection l p state B cap q) (r : Cell (p.W + 1) (p.H + 1))
    (hy : r.2 = q.2)
    (he : ∀ z : Cell (p.W + 1) (p.H + 1), z.2 = q.2 →
      min q.1.val r.1.val ≤ z.1.val → z.1.val ≤ max q.1.val r.1.val → z ∈ (l.cornerState p state).empty)
    (hB : B.walls = ∅) : FrameConnection l p state B cap r := by
  have hr := he r hy (min_le_right _ _) (le_max_right _ _)
  have hpath := ((l.cornerState p state).walk q (h.point_hole hB)).walk_horizontal r hr hy he B hB cap
  have hboth := twoWay_trans ⟨h.toPoint, h.toCorner⟩ hpath
  exact ⟨hboth.1, hboth.2⟩

/-- Extend a concrete frame connection along a vertical line of actual holes. -/
theorem walk_vertical (h : FrameConnection l p state B cap q) (r : Cell (p.W + 1) (p.H + 1))
    (hx : r.1 = q.1)
    (he : ∀ z : Cell (p.W + 1) (p.H + 1), z.1 = q.1 →
      min q.2.val r.2.val ≤ z.2.val → z.2.val ≤ max q.2.val r.2.val → z ∈ (l.cornerState p state).empty)
    (hB : B.walls = ∅) : FrameConnection l p state B cap r := by
  have hr := he r hx (min_le_right _ _) (le_max_right _ _)
  have hpath := ((l.cornerState p state).walk q (h.point_hole hB)).walk_vertical r hr hx he B hB cap
  have hboth := twoWay_trans ⟨h.toPoint, h.toCorner⟩ hpath
  exact ⟨hboth.1, hboth.2⟩

end FrameConnection
end PushPuzzle.PushS.PortLayout
