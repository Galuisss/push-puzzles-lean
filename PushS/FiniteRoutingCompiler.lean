/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurns
public import PushS.FiniteGateCore
public import PushS.FiniteAssembly

/-! Concrete finite-force gate and wire bitmap tables, with all tools and working inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires
open Turing.MultiTapeTM ComputableInPolyTime

def segmentAt (segments : List Segment) (i : ℕ) : Segment := segments.getD i ⟨(0,0),(0,0)⟩

/-- The core's own guarding side in outward path coordinates. -/
def coreSide (kind : Bool) (role : Fin 3) : Bool := !kind && decide (role = 0)

/-- A consuming gate's no-inflow anchor is one cell inward from the shared reference boundary. -/
def armRoute (w : ℕ) (g : GateTileState) (role : Fin 3) : List Segment :=
  let segments := route w g.core.isAND (g.pattern,g.rotation,role)
  segments.mapIdx fun i s => if i+1 = segments.length then
    ⟨s.start,advance (segmentDirection s).opposite s.finish (g.incoming.get role).toNat⟩
  else s

def startTrim (segments : List Segment) (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if segmentDirection (segmentAt segments (i-1)) = segmentDirection (segmentAt segments i) then 0 else 1

def finishTrim (segments : List Segment) (i : ℕ) : ℕ :=
  if i+1 = segments.length then 0
  else if segmentDirection (segmentAt segments i) = segmentDirection (segmentAt segments (i+1)) then 0 else 2

def trimmedSegment (segments : List Segment) (i : ℕ) : Segment :=
  trimmed (segmentAt segments i) (startTrim segments i) (finishTrim segments i)

def entrySide (segments : List Segment) (initialSide : Bool) (i : ℕ) : Bool :=
  if i = 0 then initialSide
  else turnSide (segmentDirection (segmentAt segments (i-1))) (segmentDirection (segmentAt segments i))

def finalSide (segments : List Segment) (targetSide : Bool) (i : ℕ) : Bool :=
  if i+1 = segments.length then targetSide
  else turnSide (segmentDirection (segmentAt segments i)) (segmentDirection (segmentAt segments (i+1)))

def ownsLast (segments : List Segment) (keepEndpoint : Bool) (i : ℕ) : Bool :=
  if i+1 = segments.length then keepEndpoint
  else decide (segmentDirection (segmentAt segments i) = segmentDirection (segmentAt segments (i+1)))

/-- Each line owns its interior and selected final seam; each perpendicular junction owns exactly F/G. -/
def pathPatches (w : ℕ) (hw : 2 ≤ w) (segments : List Segment)
    (initialSide targetSide keepEndpoint initial target : Bool) : List Bitmap.Patch :=
  (List.range segments.length).flatMap fun i =>
    [linePatch w hw (trimmedSegment segments i) (entrySide segments initialSide i)
      false (ownsLast segments keepEndpoint i) initial target (finalSide segments targetSide i)] ++
    (if i+1 < segments.length ∧
        segmentDirection (segmentAt segments i) ≠ segmentDirection (segmentAt segments (i+1)) then
      [Turn.patch w (segmentDirection (segmentAt segments i))
        (segmentDirection (segmentAt segments (i+1))) (segmentAt segments i).finish initial target]
    else [])

def coreInstance (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) : PushFS.Instance :=
  if g.core.isAND then FiniteGateCore.andInstance w hw g.core.initial g.core.target
  else FiniteGateCore.orInstance w hw g.core.initial g.core.target

def corePatch (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) : Bitmap.Patch :=
  Bitmap.instancePatch (coreInstance w hw g) (padding w+coreOffset w) (padding w+coreOffset w)

/-- All auxiliary tools and stock on all three actual cyclicly matched gate arms. -/
def gatePatches (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) : List Bitmap.Patch :=
  corePatch w hw g :: (List.finRange 3).flatMap fun role =>
    pathPatches w hw (armRoute w g role) (coreSide g.core.isAND role)
      (g.incoming.get role) (!(g.incoming.get role))
      (portInflow g.core.initial.left g.core.initial.upper g.core.initial.right role)
      (portInflow g.core.target.left g.core.target.upper g.core.target.right role)

/-- Every source wire instruction keeps its original directed input and output faces. -/
def wireVertices (w : ℕ) : Catalog.Kind → List (ℕ × ℕ)
  | .east => [(0,25*spacing w),(tileStride w,25*spacing w)]
  | .west => [(tileStride w,25*spacing w),(0,25*spacing w)]
  | .south => [(25*spacing w,0),(25*spacing w,tileStride w)]
  | .westSouth => [(tileStride w,25*spacing w),(25*spacing w,25*spacing w),(25*spacing w,tileStride w)]
  | .eastSouth => [(0,25*spacing w),(25*spacing w,25*spacing w),(25*spacing w,tileStride w)]
  | .southEast => [(25*spacing w,0),(25*spacing w,25*spacing w),(tileStride w,25*spacing w)]
  | .southWest => [(25*spacing w,0),(25*spacing w,25*spacing w),(0,25*spacing w)]

def wireRoute (w : ℕ) (kind : Catalog.Kind) : List Segment :=
  (wireVertices w kind).zipWith Segment.mk (wireVertices w kind).tail

/-- Wire inputs leave their endpoint to the preceding source tile; wire outputs own the shared endpoint. -/
def wirePatches (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) : List Bitmap.Patch :=
  pathPatches w hw (wireRoute w q.1) false false true q.2.1 q.2.2

end PushPuzzle.PushS.FiniteRouting
