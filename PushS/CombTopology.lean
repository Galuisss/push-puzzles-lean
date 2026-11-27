/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Native
public import PushS.CombOrdering
public import PushS.PortEncoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding

/-! The literal baseline contour and its actual port numbering, before partner repair. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal Turing.MultiTapeTM

/-- The original native weighted graph and its actual vertex/route arrays. -/
structure Input where
  graph : NCL.AndOrGraph
  drawing : Graph.OrthogonalDrawing

enc_structure encInput : Input where
  graph : NCL.encAndOrGraph, drawing : Graph.encOrthogonalDrawing

/-- An original incidence, a side of a genuine tooth crossing, or a local heavy-port rotation. -/
inductive Token where
  | tip (edge : ℕ) (dir : Bool)
  | mark (edge slot vertex : ℕ) (returnSide : Bool)
  | rotation (vertex : ℕ) (inside : Bool)
  deriving DecidableEq

/-- Native source edge names stay binary; actual scan positions use their unary list encodings. -/
enc_inductive encToken : Token where
  | tip : encNat, encBool
  | mark : encUnary, encUnary, encUnary, encBool
  | rotation : encUnary, encBool

/-- Token groups retain all three gate incidences until actual contour numbering is proved. -/
inductive TokenGroup where
  | wire (left right : Token)
  | gate (kind : Shuttle.Kind) (left middle right : Token)
  deriving DecidableEq

/-- The literal token incidences of one emitted page group. -/
@[expose] def TokenGroup.tokens : TokenGroup → List Token
  | .wire a b => [a, b]
  | .gate _ a b c => [a, b, c]

enc_inductive encTokenGroup : TokenGroup where
  | wire : encToken, encToken
  | gate : Shuttle.encKind, encToken, encToken, encToken

/-- Original weighted incidences attached to a real output core. -/
structure Core where
  vertex : ℕ
  kind : Shuttle.Kind
  ports : List (Token × (NCL.WeightedPort ℕ))

enc_structure encCore : Core where
  vertex : encUnary, kind : Shuttle.encKind,
  ports : (encList (encPair encToken (NCL.encWeightedPort encNat)))

/-- The actual local contour fragment around one original vertex and its tooth. -/
structure Block where
  order : List Token
  upper : List (Token × Token)
  lower : List TokenGroup
  core : Core

enc_structure encBlock : Block where
  order : (encList encToken), upper : (encList (encPair encToken encToken)),
  lower : (encList encTokenGroup), core : encCore

/-- The complete emitted token contour, page groups, and original incidence labels. -/
structure Cut where
  order : List Token
  upper : List (Token × Token)
  lower : List TokenGroup
  cores : List Core

enc_structure encCut : Cut where
  order : (encList encToken), upper : (encList (encPair encToken encToken)),
  lower : (encList encTokenGroup), cores : (encList encCore)

/-- Retain the original occurrence identity when choosing one side of its contour cut. -/
@[expose] def Crossing.token (c : Crossing) (returnSide : Bool) : Token :=
  .mark c.edge c.segment c.vertex returnSide

/-- Original native incidence identity, without renumbering the source edge. -/
@[expose] def incidenceToken (p : NCL.Port ℕ) : Token := .tip p.edge p.dir

/-- The outgoing prepared tangent, using the matching end of the same original route. -/
@[expose] def outgoingVector (width : ℕ) (d : Graph.OrthogonalDrawing) (p : NCL.Port ℕ) : Point :=
  let route := (prepare width d).2.getD p.edge []
  let oriented := if p.dir then route.reverse else route
  oriented.getD 1 (0, 0) - oriented.getD 0 (0, 0)

/-- Clockwise-from-below order of the four actual prepared orthogonal tangent directions. -/
@[expose] def tangentKey (v : Point) : ℕ :=
  if v.2 < 0 then 0 else if v.1 < 0 then 1 else if 0 < v.2 then 2 else 3

/-- The actual native weighted incidence list in geometric cyclic order. -/
@[expose] def fan (width : ℕ) (input : Input) (vertex : ℕ) : List (NCL.WeightedPort ℕ) :=
  let ports := (input.graph.vertices.getD vertex ⟨[], 0⟩).ports
  let decorated := ports.map fun p => (tangentKey (outgoingVector width input.drawing p.1), p)
  (Sort.run Prod.fst (0, ⟨⟨0, false⟩, 0⟩) decorated).map Prod.snd

/-- Emit the actual three-port contour template and its literal heavy-port rotation. -/
@[expose] def coreTemplate (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) : Block :=
  let a := ports.getD 0 ⟨⟨0, false⟩, 0⟩
  let b := ports.getD 1 ⟨⟨0, false⟩, 0⟩
  let c := ports.getD 2 ⟨⟨0, false⟩, 0⟩
  let kind : Shuttle.Kind := if ports.any (fun p => decide (p.2 = 1)) then .andGate else .orGate
  let ta := incidenceToken a.1
  let tb := incidenceToken b.1
  let tc := incidenceToken c.1
  let inside := Token.rotation vertex true
  let outside := Token.rotation vertex false
  if kind = .andGate ∧ a.2 = 2 then
    { order := [ta, tb, tc, inside, outside]
      upper := [(inside, outside)]
      lower := [.wire ta outside, .gate kind tb tc inside]
      core := ⟨vertex, kind, [(tb, b), (tc, c), (inside, a)]⟩ }
  else if kind = .andGate ∧ b.2 = 2 then
    { order := [outside, inside, ta, tb, tc]
      upper := [(outside, inside)]
      lower := [.wire outside tc, .gate kind inside ta tb]
      core := ⟨vertex, kind, [(inside, c), (ta, a), (tb, b)]⟩ }
  else
    { order := [ta, tb, tc]
      upper := []
      lower := [.gate kind ta tb tc]
      core := ⟨vertex, kind, [(ta, a), (tb, b), (tc, c)]⟩ }

/-- Apply the literal local template to the actual native vertex's geometrically ordered incidences. -/
@[expose] def coreBlock (width : ℕ) (input : Input) (vertex : ℕ) : Block :=
  coreTemplate vertex (fan width input vertex)

/-- Put the actual ascending crossings before the core and their returning sides after it. -/
@[expose] def vertexBlock (width : ℕ) (input : Input) (vertex : ℕ) : Block :=
  let localCore := coreBlock width input vertex
  let hits := toothCrossings width input.drawing vertex
  { localCore with
    order := hits.map (fun c => c.token false) ++ localCore.order ++
      hits.reverse.map (fun c => c.token true)
    lower := hits.map (fun c => .wire (c.token false) (c.token true)) ++ localCore.lower }

/-- The complete edge's successive incidence/crossing-side visits in its original reference direction. -/
@[expose] def edgeVisits (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) : List Token :=
  [.tip edge false] ++ (edgeCrossings width d edge).flatMap (fun c =>
    if c.forward then [c.token false, c.token true] else [c.token true, c.token false]) ++ [.tip edge true]

/-- Pair successive alternating visits by their actual even positions in the explicit list. -/
@[expose] def pairOff (tokens : List Token) : List (Token × Token) :=
  tokens.zipIdx.filterMap fun p =>
    if p.2 % 2 = 0 then some (p.1, tokens.getD (p.2 + 1) (.tip 0 false)) else none

/-- Compile the complete baseline contour on the same original graph and drawing arrays. -/
@[expose] def cut (width : ℕ) (input : Input) : Cut :=
  let blocks := (vertexOrder width input.drawing).map fun sv => vertexBlock width input sv.2
  { order := blocks.flatMap Block.order
    upper := input.drawing.2.zipIdx.flatMap (fun re => pairOff (edgeVisits width input.drawing re.2)) ++
      blocks.flatMap Block.upper
    lower := blocks.flatMap Block.lower
    cores := blocks.map Block.core }

/-- Read the exact emitted token position, retaining the source list's canonical numbering. -/
@[expose] def Cut.rank (c : Cut) (token : Token) : ℕ := c.order.idxOf token

/-- Number one literal token group by the actual contour positions. -/
@[expose] def Cut.lowerGroup (c : Cut) : TokenGroup → LowerGroup
  | .wire a b => .wire (min (c.rank a) (c.rank b)) (max (c.rank a) (c.rank b))
  | .gate kind a _ _ => .gate kind (c.rank a)

/-- Emit the existing physical `PortLayout` from the actual computed token contour. -/
@[expose] def Cut.toLayout (c : Cut) : PortLayout where
  portCount := c.order.length
  upperPairs := c.upper.map fun (a, b) => (min (c.rank a) (c.rank b), max (c.rank a) (c.rank b))
  lowerGroups := c.lower.map c.lowerGroup

/-- The actual baseline two-page output before the subsequent reader-partner subdivisions. -/
@[expose] def compile (width : ℕ) (input : Input) : PortLayout := (cut width input).toLayout

end PushPuzzle.PushS.Comb
