/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortGeometry

/-!
# Numbered finite routes of the complete source drawing

Every route carries its actual compiled edge number. The middle band contains
the three gate arms and all bypass wires. Layer offsets are prefix sums of
their computed heights, so successive standard boundaries coincide.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- Translate a segment without changing its orientation. -/
def Segment.translate (s : Segment) (dx dy : ℕ) : Segment :=
  ⟨(s.start.1 + dx, s.start.2 + dy), (s.finish.1 + dx, s.finish.2 + dy)⟩

/-- The complete translated trace, with explicit bounds on inverse coordinates. -/
theorem Segment.contains_translate (s : Segment) (dx dy : ℕ) (p : ℕ × ℕ) :
    (s.translate dx dy).Contains p ↔ dx ≤ p.1 ∧ dy ≤ p.2 ∧
      s.Contains (p.1 - dx, p.2 - dy) := by
  simp only [Segment.translate, Segment.Contains]
  omega

/-- Serialization commutes with translating an actual path. -/
theorem segments_translate {p q : NCL.GridRouting.Point}
    (r : NCL.GridRouting.Path p q) (dx dy : ℕ) :
    segments (r.translate dx dy) = (segments r).map (fun s => s.translate dx dy) := by
  induction r with
  | horizontal => rfl
  | vertical => rfl
  | comp r s ihr ihs =>
    simp only [NCL.GridRouting.Path.translate, segments, ihr, ihs, List.map_append]

@[fun_prop] theorem Segment.translate_polyTime :
    ComputableInPolyTime (fun q : Segment × ℕ × ℕ => q.1.translate q.2.1 q.2.2)
      (encPair encSegment Bitmap.encPoint) encSegment := by
  unfold Segment.translate Bitmap.encPoint
  fun_prop

/-- One finite route fragment, labelled by the actual source edge number. -/
structure Route where
  /-- Number used by the upstream word compiler and both orientation bit lists. -/
  edge : ℕ
  /-- The complete ordered segment list of this fragment. -/
  path : List Segment

/-- Unary edge names and unary lattice coordinates. -/
enc_structure encRoute : Route where
  edge : encUnary, path : (encList encSegment)

/-- Translate a route while retaining its source edge name. -/
def Route.translate (r : Route) (dx dy : ℕ) : Route :=
  ⟨r.edge, r.path.map (fun s => s.translate dx dy)⟩

@[fun_prop] theorem Route.translate_polyTime :
    ComputableInPolyTime (fun q : Route × ℕ × ℕ => q.1.translate q.2.1 q.2.2)
      (encPair encRoute Bitmap.encPoint) encRoute := by
  unfold Route.translate
  fun_prop

namespace Plan

/-- The first row of the three-port middle band. -/
def Layer.middleY (l : Layer) : ℕ := 2 * (l.before.wires.length + 1)

/-- The unique gate vertex in a layer's own coordinates. -/
def Layer.vertexPoint (l : Layer) : ℕ × ℕ :=
  (4 * l.instruction.data.offset + NCL.GridStar.center l.instruction.data.inputs.length,
    l.middleY + 1)

/-- The exact edge-labelled routes from the upper standard boundary. -/
def Layer.upperRoutes (l : Layer) : List Route :=
  (List.range l.before.wires.length).map fun i =>
    ⟨l.before.wires.getD i 0, Band.curve (l.upperBand, i)⟩

/-- The exact edge-labelled routes to the lower standard boundary. -/
def Layer.lowerRoutes (l : Layer) : List Route :=
  (List.range l.after.wires.length).map fun i =>
    (⟨l.after.wires.getD i 0, Band.curve (l.lowerBand, i)⟩ : Route).translate 0 (l.middleY + 2)

/-- Prefix bypasses preserve their existing edge identities. -/
def Layer.prefixRoutes (l : Layer) : List Route :=
  (List.range l.instruction.data.offset).map fun i =>
    ⟨l.before.wires.getD i 0,
      [⟨(4 * i, l.middleY), (4 * i, l.middleY + 2)⟩]⟩

/-- Suffix bypasses preserve their existing edge identities across the arity change. -/
def Layer.suffixRoutes (l : Layer) : List Route :=
  (List.range (l.before.wires.length -
    (l.instruction.data.offset + l.instruction.data.inputs.length))).map fun i =>
    let x := 4 * l.instruction.data.offset + 4 + 4 * i
    ⟨l.before.wires.getD (l.instruction.data.offset + l.instruction.data.inputs.length + i) 0,
      [⟨(x, l.middleY), (x, l.middleY + 2)⟩]⟩

/-- Incoming gate arms end at the vertex and use the actual consumed wire numbers. -/
def Layer.inputRoutes (l : Layer) : List Route :=
  (List.range l.instruction.data.inputs.length).map fun i =>
    let x := 4 * l.instruction.data.offset + i
    ⟨(l.inputPort i).port.edge,
      [⟨(x, l.middleY), (x, l.middleY + 1)⟩,
       ⟨(x, l.middleY + 1), l.vertexPoint⟩]⟩

/-- Outgoing gate arms start at the vertex and use the actual newly allocated numbers. -/
def Layer.outputRoutes (l : Layer) : List Route :=
  (List.range l.instruction.data.outputs.length).map fun i =>
    let x := 4 * l.instruction.data.offset + i
    ⟨(l.outputPort i).port.edge,
      [⟨l.vertexPoint, (x, l.middleY + 1)⟩,
       ⟨(x, l.middleY + 1), (x, l.middleY + 2)⟩]⟩

/-- All physical route fragments of a numbered layer, including every bypass. -/
def Layer.routes (l : Layer) : List Route :=
  l.upperRoutes ++ l.prefixRoutes ++ l.inputRoutes ++ l.outputRoutes ++
    l.suffixRoutes ++ l.lowerRoutes

/-- The global row assigned to the layer at a given position. -/
def rowOffset (ls : List Layer) (i : ℕ) : ℕ :=
  ((ls.take i).map Layer.height).sum

/-- Complete edge-labelled segment data of the actual source word. -/
def routes (w : NCL.Word) : List Route :=
  let ls := annotate w
  (List.range ls.length).flatMap fun i =>
    let l := ls.getD i ⟨.swap 0, ⟨[], 0, []⟩⟩
    l.routes.map (fun r => r.translate 0 (rowOffset ls i))

@[fun_prop] theorem Layer.middleY_polyTime :
    ComputableInPolyTime Layer.middleY encLayer encUnary := by
  unfold Layer.middleY
  fun_prop

@[fun_prop] theorem Layer.vertexPoint_polyTime :
    ComputableInPolyTime Layer.vertexPoint encLayer Bitmap.encPoint := by
  unfold Layer.vertexPoint NCL.GridStar.center Bitmap.encPoint
  fun_prop

@[fun_prop] theorem Layer.upperRoutes_polyTime :
    ComputableInPolyTime Layer.upperRoutes encLayer (encList encRoute) := by
  unfold Layer.upperRoutes
  fun_prop

@[fun_prop] theorem Layer.lowerRoutes_polyTime :
    ComputableInPolyTime Layer.lowerRoutes encLayer (encList encRoute) := by
  unfold Layer.lowerRoutes
  fun_prop

@[fun_prop] theorem Layer.prefixRoutes_polyTime :
    ComputableInPolyTime Layer.prefixRoutes encLayer (encList encRoute) := by
  unfold Layer.prefixRoutes
  fun_prop

@[fun_prop] theorem Layer.suffixRoutes_polyTime :
    ComputableInPolyTime Layer.suffixRoutes encLayer (encList encRoute) := by
  unfold Layer.suffixRoutes
  dsimp only
  fun_prop

@[fun_prop] theorem Layer.inputRoutes_polyTime :
    ComputableInPolyTime Layer.inputRoutes encLayer (encList encRoute) := by
  unfold Layer.inputRoutes Layer.inputPort
  dsimp only
  fun_prop

@[fun_prop] theorem Layer.outputRoutes_polyTime :
    ComputableInPolyTime Layer.outputRoutes encLayer (encList encRoute) := by
  unfold Layer.outputRoutes Layer.outputPort
  dsimp only
  fun_prop

@[fun_prop] theorem Layer.routes_polyTime :
    ComputableInPolyTime Layer.routes encLayer (encList encRoute) := by
  unfold Layer.routes
  fun_prop

@[fun_prop] theorem rowOffset_polyTime :
    ComputableInPolyTime (fun q : List Layer × ℕ => rowOffset q.1 q.2)
      (encPair (encList encLayer) encUnary) encUnary := by
  unfold rowOffset
  fun_prop

end Plan
end PushPuzzle.PushFS.Reduction
