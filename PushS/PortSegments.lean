/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortLayoutPolyTime
public import PushS.SegmentRecipePolyTime
import Mathlib.Data.Nat.Dist
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The complete marked two-page hole recipe

Place the ordinary endpoints and the two-box three-port cores at the actual working levels.
Fixed segments contain the frame, f/r streets, branches, separators, and every central marker.
Signal segments use the physical axis and internal bits. Initial and target states share the
same fixed part and are emitted directly as the existing `SegmentRecipe`.

## Main definitions

* `PortLayout.fixedSegments`: the complete marked fixed-hole background.
* `PortLayout.signalSegments`: ordinary and three-port signal holes.
* `PortLayout.segmentRecipe`: complete initial and target segment lists on the same rectangle.
* `PortLayout.canonicalRecipe`: fill physical bits from the two interface vectors and emit them.
* `PortLayout.computableInPolyTime_canonicalRecipe`: standard PT for the actual complete recipe.
* `PortLayout.computableInPolyTime_canonicalInstance`: compose with the dense instance emitter.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction

open _root_.Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.PushS.PageLevels
  PushPuzzle.PushS.SegmentRecipe PushFS.Reduction

/-- Precomputed board extents and bounded working-coordinate tables shared by the emitter
and its geometric proofs. -/
structure Coordinates where
  /-- Number of allocated working levels. -/
  levels : ℕ
  /-- Axis spacing and central row. -/
  D : ℕ
  /-- Largest horizontal coordinate. -/
  W : ℕ
  /-- Largest vertical coordinate. -/
  H : ℕ
  /-- Actual bounded working-depth table. -/
  depths : List ℕ
  /-- Actual bounded branch-length table. -/
  lengths : List ℕ

/-- The literal scale extents and the actual finite coordinate tables. -/
@[expose] def coordinates (p : Scales.Parameters) : Coordinates :=
  ⟨p.levels, p.D, p.W, p.H, depthTable p, lengthTable p⟩

private def Coordinates.x (p : Coordinates) (i : ℕ) : ℕ := (i + 1) * p.D
private def Coordinates.depth (p : Coordinates) (i : ℕ) : ℕ := p.depths.getD i 0
private def Coordinates.length (p : Coordinates) (i : ℕ) : ℕ := p.lengths.getD i 0

private enc_structure encCoordinates : Coordinates where
  levels : encUnary, D : encUnary, W : encUnary, H : encUnary,
  depths : (encList encUnary), lengths : (encList encUnary)

/-- The upper page or the reflected lower page of the physical rectangle. -/
inductive Side where
  /-- Depth measured down from the upper frame. -/
  | upper
  /-- Depth measured up from the lower frame. -/
  | lower
  deriving DecidableEq

/-- One actual ordered WIRE or three-port group with its computed physical signal data. -/
structure Placement where
  /-- Physical page containing the group. -/
  side : Side
  /-- Leftmost port index. -/
  left : ℕ
  /-- Rightmost port index. -/
  right : ℕ
  /-- Computed working level. -/
  level : ℕ
  /-- First physical internal-signal position. -/
  internal : ℕ
  /-- AND/OR kind for a three-port group, or none for a WIRE. -/
  gate : Option Shuttle.Kind

/-- An actual ordinary endpoint, with its physical signal position. -/
structure Endpoint where
  /-- Page containing this endpoint. -/
  side : Side
  /-- Actual vertical port index. -/
  port : ℕ
  /-- True at a left endpoint; false at a right endpoint. -/
  inward : Bool
  /-- Actual working-level array entry. -/
  level : ℕ
  /-- Position of this endpoint's physical horizontal signal. -/
  internal : ℕ

instance : FinEnum Side := FinEnum.ofList [.upper, .lower] (by
  intro s
  cases s <;> simp)

private abbrev encSide : Side ↪ List Bool := encFinEnum Side

private enc_structure encPlacement : Placement where
  side : encSide, left : encUnary, right : encUnary, level : encUnary,
  internal : encUnary, gate : (encOption Shuttle.encKind)

private enc_structure encEndpoint : Endpoint where
  side : encSide, port : encUnary, inward : encBool, level : encUnary, internal : encUnary

/-- Actual upper pairs followed by lower groups, in physical signal order. -/
def placements (l : PortLayout) : List Placement :=
  (l.upperPairs.zipIdx.map fun ((a, b), i) =>
    ⟨.upper, a, b, l.upperLevel i, i, none⟩) ++
  (l.lowerGroups.zipIdx.map fun (g, i) => encLowerGroup_elim g
    (fun ab => ⟨.lower, ab.1, ab.2, l.lowerLevel i, l.lowerOffset i, none⟩)
    (fun ka => ⟨.lower, ka.2, ka.2 + 2, l.lowerLevel i, l.lowerOffset i, some ka.1⟩))

/-- Both ordinary endpoints of every actual upper and lower group, in emitter order. -/
def endpoints (l : PortLayout) : List Endpoint :=
  (placements l).flatMap fun g =>
    [⟨g.side, g.left, true, g.level, g.internal⟩,
      ⟨g.side, g.right, false, g.level, g.internal + if g.gate.isSome then 2 else 0⟩]

private def centers (l : PortLayout) : List ℕ :=
  l.lowerGroups.filterMap fun g => encLowerGroup_elim g
    (fun _ => none) (fun ka => some (ka.2 + 1))

private def onSide (p : Coordinates) (side : Side) (depth : ℕ) : ℕ :=
  if side = .upper then depth else p.H - depth

private def inward (x : ℕ) (direction : Bool) (distance : ℕ) : ℕ :=
  if direction then x + distance else x - distance

private def outward (x : ℕ) (direction : Bool) (distance : ℕ) : ℕ :=
  if direction then x - distance else x + distance

private def segment (x y u v : ℕ) : Segment :=
  ⟨(min x u, min y v), (max x u, max y v)⟩

private def point (x y : ℕ) : Segment := segment x y x y

private def frame (p : Coordinates) : List Segment :=
  [segment 0 0 p.W 0, segment 0 p.H p.W p.H, segment 0 0 0 p.H,
    segment p.W 0 p.W p.H]

private def workingRows (l : PortLayout) (p : Coordinates) : List ℕ :=
  (List.range p.levels).flatMap fun j =>
    let y := p.depth (j + 1)
    if (centers l).isEmpty then [y - 2, y, y + 2] else [y, y + 2]

private def auxiliary (p : Coordinates) (e : Endpoint) : ℕ × ℕ :=
  let x := p.x e.port
  (outward x e.inward (p.length e.level), inward x e.inward 2)

/-- Fixed f/r streets, branches, separators and interlevel markers of an actual endpoint. -/
def endpointFixedSegments (l : PortLayout) (p : Coordinates) (e : Endpoint) :
    List Segment :=
  let x := p.x e.port
  let y := p.depth e.level
  let (f, r) := auxiliary p e
  [segment f (onSide p e.side 1) f (onSide p e.side (y + 2)),
    segment r (onSide p e.side 1) r (onSide p e.side (y - 1)),
    segment (inward f e.inward 1) (onSide p e.side (y + 2))
      (outward x e.inward 1) (onSide p e.side (y + 2))] ++
  ((workingRows l p).flatMap fun v =>
    (if v ≤ y then [point ((f + x) / 2) (onSide p e.side v)] else []) ++
    (if v < y then [point (inward x e.inward 1) (onSide p e.side v)] else [])) ++
  if e.level < p.levels then
    let middle := (y + p.depth (e.level + 1)) / 2
    [point f (onSide p e.side middle), point r (onSide p e.side middle)]
  else []

private def specialColumns (p : Coordinates) (middle : ℕ) : List ℕ :=
  let x := p.x middle
  [x - 2, x + 4, x + 6, x + 8, x + 12]

/-- Public/private fixed streets, branches and markers at the supplied middle port index. -/
def gateFixedSegments (p : Coordinates) (middle : ℕ) : List Segment :=
  let x := p.x middle
  let y := p.depth 1
  ([x - 2, x + 6, x + 8, x + 12].map fun col =>
    segment col (onSide p .lower 1) col (onSide p .lower (y - 1))) ++
  [point (x + 4) (onSide p .lower (y + 1)),
    segment (x + 1) (onSide p .lower (y + 2)) (x + 4) (onSide p .lower (y + 2)),
    point x (onSide p .lower (y / 2)), point (x + 4) (onSide p .lower (y / 2))] ++
  if 1 < p.levels then
    let middleRow := (y + p.depth 2) / 2
    (specialColumns p middle).map fun col => point col (onSide p .lower middleRow)
  else []

private def pageColumns (l : PortLayout) (p : Coordinates) (side : Side) : List ℕ :=
  [0, p.W] ++
  ((endpoints l).filter (fun e => decide (e.side = side))).flatMap (fun e =>
    let (f, r) := auxiliary p e
    [f, p.x e.port, r]) ++
  if side = .lower then
    (centers l).flatMap fun i => p.x i :: specialColumns p i
  else []

private def axisColumns (l : PortLayout) (p : Coordinates) : List ℕ :=
  (List.range l.portCount).map p.x

private def originalAuxiliary (l : PortLayout) (p : Coordinates) : List ℕ :=
  (endpoints l).flatMap (fun e => let (f, r) := auxiliary p e; [f, r]) ++
    (centers l).flatMap (specialColumns p)

private def streetColumns (l : PortLayout) (p : Coordinates) : List ℕ :=
  [0, p.W] ++ axisColumns l p ++ originalAuxiliary l p

private def streetRows (p : Coordinates) : List ℕ :=
  [0, p.H] ++ (List.range p.levels).flatMap fun j =>
    let y := p.depth (j + 1)
    [y, y + 2, onSide p .lower y, onSide p .lower (y + 2)]

private def adjacentPairs (xs : List ℕ) : List (ℕ × ℕ) :=
  xs.flatMap fun a => xs.filterMap fun b =>
    if a < b ∧ !(xs.any fun c => decide (a < c ∧ c < b)) then some (a, b) else none

private def crosses (l : PortLayout) (p : Coordinates) (side : Side)
    (a b y : ℕ) : Bool :=
  (placements l).any fun g => decide (g.side = side ∧ p.depth g.level = y ∧
    p.x g.left ≤ a ∧ a < b ∧ b ≤ p.x g.right)

private def wideFixed (l : PortLayout) (p : Coordinates) (side : Side) : List Segment :=
  (adjacentPairs (pageColumns l p side)).flatMap fun (a, b) =>
    if p.length p.levels < b - a then
      (workingRows l p).filterMap fun y =>
        if crosses l p side a b y then none else some (point ((a + b) / 2) (onSide p side y))
    else []

private def interiorFixed (l : PortLayout) (p : Coordinates) : List Segment :=
  (endpoints l).flatMap (endpointFixedSegments l p) ++
    (centers l).flatMap (gateFixedSegments p) ++ wideFixed l p .upper ++ wideFixed l p .lower ++
      (originalAuxiliary l p).map (fun x => point x p.D)

private def guardColumns (l : PortLayout) (p : Coordinates) (ss : List Segment) : List ℕ :=
  ss.filterMap fun s =>
    if s.start = s.finish ∧ !((streetColumns l p).contains s.start.1) ∧
        (streetRows p).contains s.start.2 ∧
        (streetColumns l p).all (fun x => decide (14 < Nat.dist s.start.1 x)) then
      some s.start.1
    else none

private def shiftPoint (guards rows : List ℕ) (s : Segment) : Segment :=
  if s.start = s.finish ∧ guards.contains s.start.1 ∧ rows.contains s.start.2 then
    point (s.start.1 - s.start.1 % 2) s.start.2
  else s

private def markedInterior (l : PortLayout) (p : Coordinates) : List Segment :=
  let base := interiorFixed l p
  let guards := guardColumns l p (frame p ++ base)
  let shifted := if guards.any (fun x => guards.contains (x + 1)) then
      base.map (shiftPoint guards (streetRows p)) else base
  let aux := (streetColumns l p).filter fun x =>
    decide (x ≠ 0 ∧ x ≠ p.W) && !((axisColumns l p).contains x)
  let marked := shifted ++ aux.flatMap (fun x => [point x (p.D - 2), point x (p.D + 2)])
  marked ++ (guardColumns l p (frame p ++ marked)).map (fun x => point x (p.D - 4)) ++
    (centers l).flatMap fun i => [point (p.x i + 2) (p.D + 4), point (p.x i + 10) (p.D + 4)]

/-- The complete fixed-hole background, including all central acceptance markers. -/
def fixedSegments (l : PortLayout) (p : Scales.Parameters) : List Segment :=
  frame (coordinates p) ++ markedInterior l (coordinates p)

/-- The axis-near and horizontal-near signal segments of one actual physical endpoint. -/
def endpointSegments (p : Coordinates) (s : SignalState) (e : Endpoint) :
    List Segment :=
  let x := p.x e.port
  let y := p.depth e.level
  let input := if e.side = .upper then s.axes.getD e.port false else !(s.axes.getD e.port false)
  let horizontal := s.internal.getD e.internal false
  let receiving := if e.inward then horizontal else !horizontal
  [segment x (onSide p e.side y) x (onSide p e.side (y + 1 + input.toNat)),
    segment (inward x e.inward 1) (onSide p e.side y)
      (inward x e.inward (1 + receiving.toNat)) (onSide p e.side y)]

private def kappaNat (kind : Shuttle.Kind) : ℕ := kind.kappa.toNat

/-- The two horizontal gaps and center-axis near holes of one actual three-port core. -/
def gateSegments (p : Coordinates) (s : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) : List Segment :=
  let middle := first + 1
  let x := p.x middle
  let y := p.depth 1
  let left := s.internal.getD internal false
  let short := s.internal.getD (internal + 1) false
  let right := s.internal.getD (internal + 2) false
  let shuttle := if short then 6 else 1
  let axis := s.axes.getD middle false
  [segment (x + 2 + left.toNat - kappaNat kind) (onSide p .lower y)
    (x + shuttle) (onSide p .lower y),
    segment (x + shuttle + 3) (onSide p .lower y) (x + 11 + right.toNat) (onSide p .lower y),
    segment x (onSide p .lower (y + 1)) x (onSide p .lower (y + 2 - axis.toNat))]

private def tripleSignal (p : Coordinates) (s : SignalState) (g : Placement) : List Segment :=
  g.gate.elim [] fun kind => gateSegments p s kind g.left g.internal

private def rawSignals (l : PortLayout) (p : Coordinates) (s : SignalState) : List Segment :=
  (endpoints l).flatMap (endpointSegments p s) ++ (placements l).flatMap (tripleSignal p s)

/-- Every ordinary endpoint and three-port signal segment of the given physical state. -/
def signalSegments (l : PortLayout) (p : Scales.Parameters) (s : SignalState) : List Segment :=
  rawSignals l (coordinates p) s

/-- The full physical hole set as closed segments: one fixed background and actual signals. -/
@[expose] def encodedSegments (l : PortLayout) (p : Scales.Parameters) (s : SignalState) :
    List Segment :=
  l.fixedSegments p ++ l.signalSegments p s

/-- Emit complete initial and target recipes, with the initial player at the empty frame corner. -/
@[expose] def segmentRecipe (l : PortLayout) (p : Scales.Parameters) (initial target : SignalState) :
    SegmentRecipe where
  width := p.W + 1
  height := p.H + 1
  playerX := 0
  playerY := 0
  initialSegments := l.encodedSegments p initial
  targetSegments := l.encodedSegments p target

/-- Fill the actual physical internal bits of both interface states and emit their complete board. -/
@[expose] def canonicalRecipe (l : PortLayout) (p : Scales.Parameters)
    (initial target : List Bool) : SegmentRecipe :=
  l.segmentRecipe p (l.canonical initial) (l.canonical target)

@[local fun_prop] private theorem lowerGroupElim_polyTime
    {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {g : α → LowerGroup} {f0 : α → ℕ × ℕ → β}
    {f1 : α → Shuttle.Kind × ℕ → β}
    (hg : ComputableInPolyTime g enc encLowerGroup)
    (h0 : ComputableInPolyTime (fun p : α × ℕ × ℕ => f0 p.1 p.2)
      (encPair enc (encPair encUnary encUnary)) encB)
    (h1 : ComputableInPolyTime (fun p : α × Shuttle.Kind × ℕ => f1 p.1 p.2)
      (encPair enc (encPair Shuttle.encKind encUnary)) encB) :
    ComputableInPolyTime (fun a => encLowerGroup_elim (g a) (f0 a) (f1 a)) enc encB :=
  (encLowerGroup_elim_polyTime h0 h1).comp (ComputableInPolyTime.id'.pair hg)

@[local fun_prop] private theorem optionToList_polyTime {β : Type} {encB : β ↪ List Bool} :
    ComputableInPolyTime Option.toList (encOption encB) (encList encB) := by
  have h : ComputableInPolyTime (fun o : Option β => o.elim [] (fun b => [b]))
      (encOption encB) (encList encB) := by fun_prop
  exact h.of_enc_eq (by intro o; cases o <;> rfl)

@[local fun_prop] private theorem filterMap_polyTime
    {α β γ : Type} {enc : γ ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List α} {body : γ → α → Option β}
    (hlist : ComputableInPolyTime list enc (encList encA))
    (hbody : ComputableInPolyTime (fun p : γ × α => body p.1 p.2)
      (encPair enc encA) (encOption encB)) :
    ComputableInPolyTime (fun x => (list x).filterMap (body x)) enc (encList encB) := by
  have h : ComputableInPolyTime (fun x => (list x).flatMap (fun a => (body x a).toList))
      enc (encList encB) :=
    ComputableInPolyTime.flatMapWithInput hlist (optionToList_polyTime.comp hbody)
  exact h.of_enc_eq (fun x => congrArg _ (List.filterMap_eq_flatMap_toList _ _))

@[local fun_prop] private theorem unaryContains_polyTime :
    ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.contains p.1)
      (encPair encUnary (encList encUnary)) encBool := by
  simp only [List.contains_eq_any_beq]
  fun_prop

@[local fun_prop] private theorem unarySucc_polyTime :
    ComputableInPolyTime Nat.succ encUnary encUnary := by
  change ComputableInPolyTime (fun n : ℕ => n + 1) _ _
  fun_prop

@[local fun_prop] private theorem unaryDist_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.dist p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  simp only [Nat.dist_eq_max_sub_min]
  fun_prop

@[local fun_prop] private theorem sideEq_polyTime :
    ComputableInPolyTime (fun p : Side × Side => decide (p.1 = p.2))
      (encPair encSide encSide) encBool := .of_finite _

@[local fun_prop] private theorem kindKappa_polyTime :
    ComputableInPolyTime kappaNat Shuttle.encKind encUnary :=
  .of_finite _

@[local fun_prop] private theorem boolNat_polyTime :
    ComputableInPolyTime Bool.toNat encBool encUnary := .of_finite _

@[local fun_prop] private theorem Coordinates_x_polyTime :
    ComputableInPolyTime (fun p : Coordinates × ℕ => p.1.x p.2)
      (encPair encCoordinates encUnary) (encUnary) := by
  unfold Coordinates.x
  fun_prop

@[local fun_prop] private theorem Coordinates_depth_polyTime :
    ComputableInPolyTime (fun p : Coordinates × ℕ => p.1.depth p.2)
      (encPair encCoordinates encUnary) (encUnary) := by
  unfold Coordinates.depth
  fun_prop

@[local fun_prop] private theorem Coordinates_length_polyTime :
    ComputableInPolyTime (fun p : Coordinates × ℕ => p.1.length p.2)
      (encPair encCoordinates encUnary) (encUnary) := by
  unfold Coordinates.length
  fun_prop

@[local fun_prop] private theorem placements_polyTime :
    ComputableInPolyTime (fun p : PortLayout => placements p)
      (encPortLayout) (encList encPlacement) := by
  unfold placements
  fun_prop

@[local fun_prop] private theorem endpoints_polyTime :
    ComputableInPolyTime (fun p : PortLayout => endpoints p)
      (encPortLayout) (encList encEndpoint) := by
  unfold endpoints
  fun_prop

@[local fun_prop] private theorem centers_polyTime :
    ComputableInPolyTime (fun p : PortLayout => centers p)
      (encPortLayout) (encList encUnary) := by
  unfold centers
  fun_prop

@[local fun_prop] private theorem onSide_polyTime :
    ComputableInPolyTime (fun p : Coordinates × Side × ℕ => onSide p.1 p.2.1 p.2.2)
      (encPair encCoordinates (encPair encSide encUnary)) (encUnary) := by
  unfold onSide
  fun_prop

@[local fun_prop] private theorem inward_polyTime :
    ComputableInPolyTime (fun p : ℕ × Bool × ℕ => inward p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBool encUnary)) (encUnary) := by
  unfold inward
  fun_prop

@[local fun_prop] private theorem outward_polyTime :
    ComputableInPolyTime (fun p : ℕ × Bool × ℕ => outward p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBool encUnary)) (encUnary) := by
  unfold outward
  fun_prop

@[local fun_prop] private theorem segment_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => segment p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary encUnary))) (encSegment) := by
  unfold segment
  fun_prop

@[local fun_prop] private theorem point_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => point p.1 p.2)
      (encPair encUnary encUnary) (encSegment) := by
  unfold point
  fun_prop

@[local fun_prop] private theorem frame_polyTime :
    ComputableInPolyTime (fun p : Coordinates => frame p)
      (encCoordinates) (encList encSegment) := by
  unfold frame
  fun_prop

@[local fun_prop] private theorem workingRows_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => workingRows p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encUnary) := by
  unfold workingRows
  fun_prop

@[local fun_prop] private theorem auxiliary_polyTime :
    ComputableInPolyTime (fun p : Coordinates × Endpoint => auxiliary p.1 p.2)
      (encPair encCoordinates encEndpoint) (encPair encUnary encUnary) := by
  unfold auxiliary
  fun_prop

@[local fun_prop] private theorem endpointFixedSegments_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates × Endpoint => endpointFixedSegments p.1 p.2.1 p.2.2)
      (encPair encPortLayout (encPair encCoordinates encEndpoint)) (encList encSegment) := by
  dsimp only [endpointFixedSegments]
  fun_prop

@[local fun_prop] private theorem specialColumns_polyTime :
    ComputableInPolyTime (fun p : Coordinates × ℕ => specialColumns p.1 p.2)
      (encPair encCoordinates encUnary) (encList encUnary) := by
  unfold specialColumns
  fun_prop

@[local fun_prop] private theorem gateFixedSegments_polyTime :
    ComputableInPolyTime (fun p : Coordinates × ℕ => gateFixedSegments p.1 p.2)
      (encPair encCoordinates encUnary) (encList encSegment) := by
  dsimp only [gateFixedSegments]
  fun_prop

@[local fun_prop] private theorem pageColumns_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates × Side => pageColumns p.1 p.2.1 p.2.2)
      (encPair encPortLayout (encPair encCoordinates encSide)) (encList encUnary) := by
  unfold pageColumns
  fun_prop

@[local fun_prop] private theorem axisColumns_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => axisColumns p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encUnary) := by
  unfold axisColumns
  fun_prop

@[local fun_prop] private theorem originalAuxiliary_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => originalAuxiliary p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encUnary) := by
  unfold originalAuxiliary
  fun_prop

@[local fun_prop] private theorem streetColumns_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => streetColumns p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encUnary) := by
  unfold streetColumns
  fun_prop

@[local fun_prop] private theorem streetRows_polyTime :
    ComputableInPolyTime (fun p : Coordinates => streetRows p)
      (encCoordinates) (encList encUnary) := by
  unfold streetRows
  fun_prop

@[local fun_prop] private theorem adjacentPairs_polyTime :
    ComputableInPolyTime (fun p : List ℕ => adjacentPairs p)
      (encList encUnary) (encList (encPair encUnary encUnary)) := by
  unfold adjacentPairs
  fun_prop

@[local fun_prop] private theorem crosses_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates × Side × ℕ × ℕ × ℕ => crosses p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair encPortLayout (encPair encCoordinates (encPair encSide (encPair encUnary (encPair encUnary encUnary))))) (encBool) := by
  unfold crosses
  fun_prop

@[local fun_prop] private theorem wideFixed_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates × Side => wideFixed p.1 p.2.1 p.2.2)
      (encPair encPortLayout (encPair encCoordinates encSide)) (encList encSegment) := by
  unfold wideFixed
  fun_prop

@[local fun_prop] private theorem interiorFixed_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => interiorFixed p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encSegment) := by
  unfold interiorFixed
  fun_prop

@[local fun_prop] private theorem guardColumns_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates × List Segment => guardColumns p.1 p.2.1 p.2.2)
      (encPair encPortLayout (encPair encCoordinates (encList encSegment))) (encList encUnary) := by
  unfold guardColumns
  fun_prop

@[local fun_prop] private theorem shiftPoint_polyTime :
    ComputableInPolyTime (fun p : List ℕ × List ℕ × Segment => shiftPoint p.1 p.2.1 p.2.2)
      (encPair (encList encUnary) (encPair (encList encUnary) encSegment)) (encSegment) := by
  unfold shiftPoint
  fun_prop

@[local fun_prop] private theorem markedInterior_polyTime :
    ComputableInPolyTime (fun p : PortLayout × Coordinates => markedInterior p.1 p.2)
      (encPair encPortLayout encCoordinates) (encList encSegment) := by
  dsimp only [markedInterior]
  fun_prop

@[local fun_prop] private theorem endpointSegments_polyTime :
    ComputableInPolyTime (fun p : Coordinates × SignalState × Endpoint => endpointSegments p.1 p.2.1 p.2.2)
      (encPair encCoordinates (encPair encSignalState encEndpoint)) (encList encSegment) := by
  dsimp only [endpointSegments]
  fun_prop

@[local fun_prop] private theorem gateSegments_polyTime :
    ComputableInPolyTime (fun p : Coordinates × SignalState × Shuttle.Kind × ℕ × ℕ =>
      gateSegments p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair encCoordinates (encPair encSignalState
        (encPair Shuttle.encKind (encPair encUnary encUnary)))) (encList encSegment) := by
  dsimp only [gateSegments]
  fun_prop

@[local fun_prop] private theorem tripleSignal_polyTime :
    ComputableInPolyTime (fun p : Coordinates × SignalState × Placement => tripleSignal p.1 p.2.1 p.2.2)
      (encPair encCoordinates (encPair encSignalState encPlacement)) (encList encSegment) := by
  dsimp only [tripleSignal]
  fun_prop

@[local fun_prop] private theorem rawSignals_polyTime :
    ComputableInPolyTime (fun q : PortLayout × Coordinates × SignalState =>
      rawSignals q.1 q.2.1 q.2.2)
      (encPair encPortLayout (encPair encCoordinates encSignalState)) (encList encSegment) := by
  unfold rawSignals
  fun_prop

section PolyTime

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout}
  {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include haxes hlevels

private theorem coordinates_polyTime :
    ComputableInPolyTime (fun a => coordinates (p a)) enc encCoordinates := by
  have hD := computableInPolyTime_D haxes hlevels
  have hW := computableInPolyTime_W haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  have hd := computableInPolyTime_depthTable haxes hlevels
  have ht := computableInPolyTime_lengthTable haxes hlevels
  simp only [coordinates, hlevels]
  fun_prop

include hl

/-- Compute the complete fixed-hole list from the actual port data and fixed-level scales. -/
theorem computableInPolyTime_fixedSegments :
    ComputableInPolyTime (fun a => (layout a).fixedSegments (p a)) enc (encList encSegment) := by
  have hc := coordinates_polyTime haxes hlevels
  unfold fixedSegments
  fun_prop

/-- Compute every actual signal segment without any geometric validity hypothesis. -/
private theorem computableInPolyTime_signalSegments {state : α → SignalState}
    (hs : ComputableInPolyTime state enc encSignalState) :
    ComputableInPolyTime (fun a => (layout a).signalSegments (p a) (state a))
      enc (encList encSegment) := by
  have hc := coordinates_polyTime haxes hlevels
  exact rawSignals_polyTime.comp (hl.prod (hc.prod hs))

/-- Emit the actual initial and target segment lists in polynomial time. The level bound
is a fixed family parameter, including on raw layouts whose computed levels exceed it. -/
theorem computableInPolyTime_segmentRecipe {initial target : α → SignalState}
    (hi : ComputableInPolyTime initial enc encSignalState)
    (ht : ComputableInPolyTime target enc encSignalState) :
    ComputableInPolyTime (fun a => (layout a).segmentRecipe (p a) (initial a) (target a))
      enc encSegmentRecipe := by
  have hf := computableInPolyTime_fixedSegments hl haxes hlevels
  have hi' := computableInPolyTime_signalSegments hl haxes hlevels hi
  have ht' := computableInPolyTime_signalSegments hl haxes hlevels ht
  have hW := computableInPolyTime_W haxes hlevels
  have hH := computableInPolyTime_H haxes hlevels
  unfold segmentRecipe encodedSegments
  fun_prop

/-- Compute the complete marked board directly from the two interface bit arrays. -/
theorem computableInPolyTime_canonicalRecipe {initial target : α → List Bool}
    (hi : ComputableInPolyTime initial enc (encList encBool))
    (ht : ComputableInPolyTime target enc (encList encBool)) :
    ComputableInPolyTime (fun a => (layout a).canonicalRecipe (p a) (initial a) (target a))
      enc encSegmentRecipe := by
  unfold canonicalRecipe
  exact computableInPolyTime_segmentRecipe hl haxes hlevels (by fun_prop) (by fun_prop)

/-- Compose the actual canonical recipe with the dense instance compiler. Its remaining
mathematical input is exactly the validity of those emitted recipes. -/
theorem computableInPolyTime_canonicalInstance {initial target : α → List Bool}
    (hi : ComputableInPolyTime initial enc (encList encBool))
    (ht : ComputableInPolyTime target enc (encList encBool))
    (hv : ∀ a, ((layout a).canonicalRecipe (p a) (initial a) (target a)).Valid) :
    ComputableInPolyTime
      (fun a => ((layout a).canonicalRecipe (p a) (initial a) (target a)).toInstance (hv a))
      enc encoding :=
  SegmentRecipe.computableInPolyTime_toInstance
    (computableInPolyTime_canonicalRecipe hl haxes hlevels hi ht) hv

end PolyTime

/-- Fixed holes and the current signal holes are the complete emitted segment union. -/
theorem holeTest_encodedSegments (l : PortLayout) (p : Scales.Parameters) (s : SignalState)
    (q : ℕ × ℕ) : SegmentRecipe.holeTest (l.encodedSegments p s, q) = true ↔
      SegmentRecipe.holeTest (l.fixedSegments p, q) = true ∨
        SegmentRecipe.holeTest (l.signalSegments p s, q) = true := by
  simp only [SegmentRecipe.holeTest_eq_true, encodedSegments, List.mem_append,
    or_and_right, exists_or]

/-- Every cell on either horizontal frame edge is an actual fixed hole. -/
theorem horizontal_frame_empty (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hy : y = 0 ∨ y = p.H) (hx : x ≤ p.W) :
    SegmentRecipe.holeTest (l.fixedSegments p, x, y) = true := by
  rw [SegmentRecipe.holeTest_eq_true]
  rcases hy with rfl | rfl
  · refine ⟨segment 0 0 p.W 0, by simp [fixedSegments, frame, coordinates], ?_⟩
    simp [segment, Segment.Contains, hx]
  · refine ⟨segment 0 p.H p.W p.H, by simp [fixedSegments, frame, coordinates], ?_⟩
    simp [segment, Segment.Contains, hx]

/-- Every cell on either vertical frame edge is an actual fixed hole. -/
theorem vertical_frame_empty (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hx : x = 0 ∨ x = p.W) (hy : y ≤ p.H) :
    SegmentRecipe.holeTest (l.fixedSegments p, x, y) = true := by
  rw [SegmentRecipe.holeTest_eq_true]
  rcases hx with rfl | rfl
  · refine ⟨segment 0 0 0 p.H, by simp [fixedSegments, frame, coordinates], ?_⟩
    simp [segment, Segment.Contains, hy]
  · refine ⟨segment p.W 0 p.W p.H, by simp [fixedSegments, frame, coordinates], ?_⟩
    simp [segment, Segment.Contains, hy]

/-- The actual recipe starts its player inside its declared rectangle. -/
theorem segmentRecipe_player_bounds (l : PortLayout) (p : Scales.Parameters)
    (initial target : SignalState) :
    (l.segmentRecipe p initial target).playerX < (l.segmentRecipe p initial target).width ∧
      (l.segmentRecipe p initial target).playerY < (l.segmentRecipe p initial target).height := by
  simp [segmentRecipe]

/-- The actual initial segment union contains the initial player. -/
theorem segmentRecipe_player_empty (l : PortLayout) (p : Scales.Parameters)
    (initial target : SignalState) :
    SegmentRecipe.holeTest ((l.segmentRecipe p initial target).initialSegments, 0, 0) = true :=
  (l.holeTest_encodedSegments p initial (0, 0)).mpr
    (Or.inl (l.horizontal_frame_empty p (Or.inl rfl) (Nat.zero_le _)))

/-- For the concrete emitted recipe, validity reduces exactly to equal hole inventories. -/
theorem segmentRecipe_valid_iff (l : PortLayout) (p : Scales.Parameters)
    (initial target : SignalState) :
    (l.segmentRecipe p initial target).Valid ↔
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial)).card =
        (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target)).card := by
  constructor
  · exact fun h => h.card_eq
  · intro h
    exact ⟨(l.segmentRecipe_player_bounds p initial target).1,
      (l.segmentRecipe_player_bounds p initial target).2,
      l.segmentRecipe_player_empty p initial target, h⟩

/-- The explicit recipe rectangle has the previously proved geometric area bound. -/
theorem segmentRecipe_area_le (l : PortLayout) (p : Scales.Parameters)
    (initial target : SignalState) :
    (l.segmentRecipe p initial target).width * (l.segmentRecipe p initial target).height ≤
      6 * (4096 * (p.levels + 1) * 64 ^ (2 * p.levels)) ^ 2 *
        (p.axes + 1) ^ (4 * p.levels + 3) := p.area_le

end PushPuzzle.PushS.PortLayout
