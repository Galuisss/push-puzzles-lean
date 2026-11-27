/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCompilerBounds
public import PushS.FiniteRoutingTurnMatching
public import PushS.FiniteGateMatching
public import PushFS.AxisIsometry

/-! Semantic primitive instances underlying exactly the emitted gate and wire bitmap patches. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

structure LineCode where
  segment : Segment
  above : Bool
  first : Bool
  last : Bool
  initial : Bool
  target : Bool
  desiredSide : Bool
  deriving DecidableEq

structure TurnCode where
  incoming : Direction
  outgoing : Direction
  corner : ℕ × ℕ
  initial : Bool
  target : Bool
  deriving DecidableEq

inductive PrimitiveCode
  | core (gate : GateTileState)
  | line (code : LineCode)
  | turn (code : TurnCode)
  deriving DecidableEq

namespace PrimitiveCode

def instanceOf (w : ℕ) (hw : 2 ≤ w) : PrimitiveCode → PushFS.Instance
  | .core g => coreInstance w hw g
  | .line c => lineInstance w hw c.segment c.above c.first c.last c.initial c.target c.desiredSide
  | .turn c => Turn.orientedPuzzle w c.incoming c.outgoing c.initial c.target

def offsetX (w : ℕ) : PrimitiveCode → ℕ
  | .core _ => padding w+coreOffset w
  | .line c => Line.offsetX w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
      (segmentDirection c.segment) c.segment.start
  | .turn c => Turn.offsetX w c.corner

def offsetY (w : ℕ) : PrimitiveCode → ℕ
  | .core _ => padding w+coreOffset w
  | .line c => Line.offsetY w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
      (segmentDirection c.segment) c.segment.start
  | .turn c => Turn.offsetY w c.corner

def patch (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : Bitmap.Patch :=
  Bitmap.instancePatch (c.instanceOf w hw) (c.offsetX w) (c.offsetY w)

def Labels (w : ℕ) : PrimitiveCode → Type
  | .core g => match g.core.isAND with
      | true => FiniteGeometry.AndLabel w
      | false => FiniteGeometry.OrLabel w
  | .line c => Line.OwnedLabel w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.first c.last
  | .turn _ => Fin 2

instance (w : ℕ) (c : PrimitiveCode) : Fintype (c.Labels w) := by
  cases c with
  | core g => cases h : g.core.isAND <;> simp only [Labels,h] <;> infer_instance
  | line c => unfold Labels; infer_instance
  | turn c => unfold Labels; infer_instance

/-- Every primitive includes its complete actual initial/target matching. -/
def matching (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : SlotMatching (c.instanceOf w hw) (c.Labels w) := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · exact FiniteGateMatching.orMatching w hw initial target
    · exact FiniteGateMatching.andMatching w hw initial target
  | line c =>
    exact (Line.ownedMatching w hw _ c.above c.first c.last c.initial c.target).reorient
      (Line.rotation w _ (segmentDirection c.segment))
  | turn c =>
    exact (Turn.matching w c.initial c.target).reorient (Turn.orientation w c.incoming c.outgoing)

/-- The exact primitive rectangle placement used by the dense patch renderer. -/
def placement (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (hc : PatchFits w (c.patch w hw)) :
    GridEmbedding (c.instanceOf w hw).width (c.instanceOf w hw).height (tileSide w) (tileSide w) :=
  GridEmbedding.translate (c.offsetX w) (c.offsetY w) hc.1 hc.2

end PrimitiveCode

/-- All owned primitives, in the same literal order as the physical path renderer. -/
def pathCodes (segments : List Segment) (initialSide targetSide keepEndpoint initial target : Bool) :
    List PrimitiveCode :=
  (List.range segments.length).flatMap fun i =>
    [.line ⟨trimmedSegment segments i,entrySide segments initialSide i,false,
      ownsLast segments keepEndpoint i,initial,target,finalSide segments targetSide i⟩] ++
    (if i+1 < segments.length ∧
        segmentDirection (segmentAt segments i) ≠ segmentDirection (segmentAt segments (i+1)) then
      [.turn ⟨segmentDirection (segmentAt segments i),segmentDirection (segmentAt segments (i+1)),
        (segmentAt segments i).finish,initial,target⟩]
    else [])

theorem pathPatches_eq_map (w : ℕ) (hw : 2 ≤ w) (segments : List Segment)
    (initialSide targetSide keepEndpoint initial target : Bool) :
    pathPatches w hw segments initialSide targetSide keepEndpoint initial target =
      (pathCodes segments initialSide targetSide keepEndpoint initial target).map (PrimitiveCode.patch w hw) := by
  simp only [pathPatches,pathCodes,List.map_flatMap,List.map_append]
  congr 1
  funext i
  split_ifs <;> rfl

def gateCodes (w : ℕ) (g : GateTileState) : List PrimitiveCode :=
  .core g :: (List.finRange 3).flatMap fun role =>
    pathCodes (armRoute w g role) (coreSide g.core.isAND role)
      (g.incoming.get role) (!(g.incoming.get role))
      (portInflow g.core.initial.left g.core.initial.upper g.core.initial.right role)
      (portInflow g.core.target.left g.core.target.upper g.core.target.right role)

def wireCodes (w : ℕ) (q : Catalog.Bitmap.Args) : List PrimitiveCode :=
  pathCodes (wireRoute w q.1) false false true q.2.1 q.2.2

theorem gatePatches_eq_map (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    gatePatches w hw g = (gateCodes w g).map (PrimitiveCode.patch w hw) := by
  simp [gatePatches,gateCodes,pathPatches_eq_map,List.map_flatMap,PrimitiveCode.patch,
    PrimitiveCode.instanceOf,PrimitiveCode.offsetX,PrimitiveCode.offsetY,corePatch]

theorem wirePatches_eq_map (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    wirePatches w hw q = (wireCodes w q).map (PrimitiveCode.patch w hw) :=
  pathPatches_eq_map w hw _ _ _ _ _ _

theorem gateCode_fits (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) {c : PrimitiveCode} (hc : c ∈ gateCodes w g) :
    PatchFits w (c.patch w hw) :=
  gatePatches_fit w hw g _ (by rw [gatePatches_eq_map]; exact List.mem_map.mpr ⟨c,hc,rfl⟩)

theorem wireCode_fits (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) {c : PrimitiveCode} (hc : c ∈ wireCodes w q) :
    PatchFits w (c.patch w hw) :=
  wirePatches_fit w hw q _ (by rw [wirePatches_eq_map]; exact List.mem_map.mpr ⟨c,hc,rfl⟩)

end PushPuzzle.PushS.FiniteRouting
