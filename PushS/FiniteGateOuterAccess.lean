/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateFaceBridge
public import PushS.FiniteRoutingCoreSeparation
import Mathlib.Tactic.FinCases

/-! Literal gate-to-line outer-face corridors, including the exterior A/B/C links. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateOuterAccess

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteGateMacros FiniteGateTools
open FiniteGateAStraight FiniteSquareLine FiniteLineMacros

variable {W H : ℕ}

/-- Literal endpoints of the gate tail corridors and their first-line face links. -/
inductive Node | aInner | aDock | aBridge | cInner | cDock | bLeft | bRight

/-- The source coordinates of each tail and exterior face endpoint. -/
def nodePoint (w : ℕ) (kind : Bool) : Node → ℕ × ℕ
  | .aInner => if kind then (origin w-6*w-11,origin w-6*w-20) else (origin w+1,origin w-1)
  | .aDock => if kind then (origin w-8*w-17,origin w-5*w-20) else (origin w-2*w-8,origin w-w-1)
  | .aBridge => if kind then (origin w-8*w-17,origin w-7*w-22) else (origin w-2*w-8,origin w-w-1)
  | .cInner => (origin w+w+(if kind then 6 else 7),origin w-1)
  | .cDock => (origin w+3*w+(if kind then 13 else 14),origin w-w-1)
  | .bLeft => (FiniteGateFaceGeometry.leftX w kind,origin w-FiniteGateFaceGeometry.upperDepth w kind)
  | .bRight => (FiniteGateFaceGeometry.rightX w kind,origin w-FiniteGateFaceGeometry.upperDepth w kind)

/-- The same endpoints as bounded cells on the actual finite core board. -/
def node (w : ℕ) (kind : Bool) (n : Node) : Cell (side w) (side w) :=
  (⟨(nodePoint w kind n).1, by
    cases kind <;> cases n <;>
      dsimp [nodePoint,FiniteGateFaceGeometry.leftX,FiniteGateFaceGeometry.rightX,
        FiniteGateFaceGeometry.column,origin,FiniteGeometry.side] <;> omega⟩,
   ⟨(nodePoint w kind n).2, by
    cases kind <;> cases n <;>
      dsimp [nodePoint,FiniteGateFaceGeometry.upperDepth,origin,FiniteGeometry.side] <;> omega⟩)

attribute [local irreducible] FiniteGeometry.side

theorem aInner_and (w : ℕ) : node w true .aInner = (Segment.west.sweep w).hub := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [node,nodePoint,Segment.sweep,Sweep.hub,Sweep.map,Segment.hubCoordinate,Segment.lane,t]
  all_goals dsimp [s,origin]; omega

theorem bLeft_eq (w : ℕ) (kind : Bool) : node w kind .bLeft = FiniteGateFaceGeometry.dock w kind true := rfl

/-- Exact agreement with the no-inflow source anchor of the actual first arm line. -/
theorem aDock_world (w : ℕ) (kind : Bool) :
    FiniteRouting.coreWorld w (node w kind .aDock) =
      FiniteRouting.Line.outerStart w .west (FiniteRouting.corePort w kind 0) kind := by
  cases kind <;> apply Prod.ext <;>
    simp [FiniteRouting.coreWorld,node,nodePoint,FiniteRouting.Line.outerStart,
      FiniteRouting.corePort,FiniteRouting.coreOffset,FiniteRouting.spacing,
      FiniteRouting.padding,origin] <;> omega

/-- Exact agreement with the no-inflow source anchor of the actual first arm line. -/
theorem aBridge_world (w : ℕ) (kind : Bool) :
    FiniteRouting.coreWorld w (node w kind .aBridge) =
      FiniteRouting.Line.outerStart w .west (FiniteRouting.corePort w kind 0) false := by
  cases kind <;> apply Prod.ext <;>
    simp [FiniteRouting.coreWorld,node,nodePoint,FiniteRouting.Line.outerStart,
      FiniteRouting.corePort,FiniteRouting.coreOffset,FiniteRouting.spacing,
      FiniteRouting.padding,origin] <;> omega

/-- Both literal B docks are the real first line's two exposed starting hubs. -/
theorem bDock_world (w : ℕ) (kind north : Bool) :
    FiniteRouting.coreWorld w (FiniteGateFaceGeometry.dock w kind north) =
      FiniteRouting.Line.outerStart w .north (FiniteRouting.corePort w kind 1) north := by
  cases kind <;> cases north <;> apply Prod.ext <;>
    simp [FiniteRouting.coreWorld,FiniteGateFaceGeometry.dock,
      FiniteGateFaceGeometry.leftX,FiniteGateFaceGeometry.rightX,
      FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth,
      FiniteRouting.Line.outerStart,FiniteRouting.corePort,FiniteRouting.coreOffset,
      FiniteRouting.spacing,FiniteRouting.padding,origin] <;> omega

/-- The A tail face, its upper exterior link, the C tail face, and its right exterior link. -/
inductive Corridor | a | aBridge | c | cBridge

namespace Corridor

/-- The physical entrance of each exterior corridor. -/
def start : Corridor → Node
  | .a => .aInner | .aBridge => .aBridge | .c => .cInner | .cBridge => .cDock

/-- The physical exit of each exterior corridor. -/
def finish : Corridor → Node
  | .a => .aDock | .aBridge => .bLeft | .c => .cDock | .cBridge => .bRight

/-- Exactly the rectangle traversed by the real two-segment exterior walk. -/
def active (w : ℕ) (kind : Bool) (k : Corridor) : Finset (Cell (side w) (side w)) :=
  FiniteAtomFrames.walkActive (node w kind k.start) (node w kind k.finish)

-- Check all four literal corridor rectangles against every wall and every indexed box family.
set_option maxHeartbeats 1200000 in
/-- The complete actual AND mixed inventory leaves each exterior link and tail face free. -/
theorem and_free (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (k : Corridor)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w)) (hp : p ∈ k.active w true) :
    Free (andBoard w goals) (andMixedBoxes w X) p := by
  obtain ⟨hx,hx',hy,hy'⟩ := (FiniteAtomFrames.mem_walkActive _ _ _).mp hp
  constructor
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    cases k <;> fin_cases i <;>
      simp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,FiniteGateFaceGeometry.rightX,
        FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth,andRectangle,origin]
        at hx hx' hy hy' hi' <;> omega
  · intro hm
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases l with
    | west i =>
      have hb := Bool.toNat_le (X.west i)
      cases k <;>
        simp only [andMixedCell,andCell,andPoint] at hpx hpy
      all_goals dsimp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,
        FiniteGateFaceGeometry.rightX,FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth]
        at hx hx' hy hy'; unfold origin at *; omega
    | branchC i =>
      have hb := Bool.toNat_le (X.branchC i)
      cases k <;>
        simp only [andMixedCell,andCell,andPoint] at hpx hpy
      all_goals dsimp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,
        FiniteGateFaceGeometry.rightX,FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth]
        at hx hx' hy hy'; unfold origin at *; omega
    | upper i =>
      have hb := Bool.toNat_le (X.upper i)
      cases k <;> simp only [andMixedCell,andCell,andPoint] at hpx hpy
      all_goals dsimp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,
        FiniteGateFaceGeometry.rightX,FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth]
        at hx hx' hy hy'; unfold origin at *; omega
    | lower i =>
      have hb := Bool.toNat_le (X.lower i)
      cases k <;> simp only [andMixedCell,andCell,andPoint] at hpx hpy
      all_goals dsimp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,
        FiniteGateFaceGeometry.rightX,FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth]
        at hx hx' hy hy'; unfold origin at *; omega
    | _ =>
      cases k <;> simp only [andMixedCell,andCell,andPoint] at hpx hpy
      all_goals dsimp [node,nodePoint,start,finish,FiniteGateFaceGeometry.leftX,
        FiniteGateFaceGeometry.rightX,FiniteGateFaceGeometry.column,FiniteGateFaceGeometry.upperDepth]
        at hx hx' hy hy'; unfold origin at *; omega

-- Check all four literal corridor rectangles against every wall and every indexed box family.

/-- Replay an entire literal exterior link with every ambient box fixed. -/
theorem walk_ambient (w : ℕ) (kind : Bool) (k : Corridor)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (k.active w kind) e B stock) :
    Reachable B (some 1) ⟨e.cells (node w kind k.start),stock⟩
      ⟨e.cells (node w kind k.finish),stock⟩ :=
  FiniteAtomFrames.walk_ambient _ _ e F

/-- Return along the exact same literal exterior link, with the same narrow physical footprint. -/
theorem walk_reverse_ambient (w : ℕ) (kind : Bool) (k : Corridor)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (k.active w kind) e B stock) :
    Reachable B (some 1) ⟨e.cells (node w kind k.finish),stock⟩
      ⟨e.cells (node w kind k.start),stock⟩ := by
  apply FiniteAtomFrames.walk_ambient _ _ e
  apply F.mono_active
  intro p hp
  change p ∈ FiniteAtomFrames.walkActive (node w kind k.start) (node w kind k.finish)
  simpa only [FiniteAtomFrames.mem_walkActive,min_comm,max_comm] using hp

end Corridor
end PushPuzzle.PushS.FiniteGateOuterAccess
