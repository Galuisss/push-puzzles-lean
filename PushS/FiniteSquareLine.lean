/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteVerticalLineMacros

/-! One interface for horizontal and vertical sweeps on the square gate boards. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSquareLine

open PushFS FiniteLineMacros

structure Sweep (N : ℕ) where
  line : Line N N
  vertical : Bool

variable {N : ℕ}

namespace Sweep

def map (S : Sweep N) (p : Cell N N) : Cell N N := if S.vertical then p.swap else p

def position (S : Sweep N) (frontier : ℕ) (i : Fin S.line.count) : Cell N N :=
  S.map (S.line.position frontier i)

def hub (S : Sweep N) : Cell N N := S.map (S.line.hub, S.line.lane)

def boxes (S : Sweep N) (fixed : Finset (Cell N N)) (frontier : ℕ) : Finset (Cell N N) :=
  fixed ∪ Finset.univ.image (S.position frontier)

structure Frame (S : Sweep N) (B : Board N N) (fixed : Finset (Cell N N)) : Prop where
  fixed_floor : Disjoint fixed B.walls
  track_free : ∀ x, S.line.track x → Free B fixed (S.map (x, S.line.row))
  lane_free : ∀ x, S.line.laneSegment x → Free B fixed (S.map (x, S.line.lane))

theorem Frame.forward {S : Sweep N} {B : Board N N} {fixed : Finset (Cell N N)}
    (F : S.Frame B fixed) :
    Reachable B (some 1) ⟨S.hub, S.boxes fixed 0⟩ ⟨S.hub, S.boxes fixed S.line.count⟩ := by
  obtain ⟨L, vertical⟩ := S
  cases vertical with
  | false =>
    have hF : L.Frame B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed 0⟩
      ⟨(L.hub, L.lane), L.boxes fixed L.count⟩
    exact hF.forward
  | true =>
    have hF : FiniteVerticalLineMacros.Frame L B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1)
      ⟨(L.lane, L.hub), FiniteVerticalLineMacros.boxes L fixed 0⟩
      ⟨(L.lane, L.hub), FiniteVerticalLineMacros.boxes L fixed L.count⟩
    exact hF.forward

theorem Frame.backward {S : Sweep N} {B : Board N N} {fixed : Finset (Cell N N)}
    (F : S.Frame B fixed) :
    Reachable B (some 1) ⟨S.hub, S.boxes fixed S.line.count⟩ ⟨S.hub, S.boxes fixed 0⟩ := by
  obtain ⟨L, vertical⟩ := S
  cases vertical with
  | false =>
    have hF : L.Frame B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1) ⟨(L.hub, L.lane), L.boxes fixed L.count⟩
      ⟨(L.hub, L.lane), L.boxes fixed 0⟩
    exact hF.backward
  | true =>
    have hF : FiniteVerticalLineMacros.Frame L B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1)
      ⟨(L.lane, L.hub), FiniteVerticalLineMacros.boxes L fixed L.count⟩
      ⟨(L.lane, L.hub), FiniteVerticalLineMacros.boxes L fixed 0⟩
    exact hF.backward

end Sweep
end PushPuzzle.PushS.FiniteSquareLine
