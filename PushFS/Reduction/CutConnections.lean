/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.MiddleGeometry
public import PushFS.Reduction.Numbering
import Mathlib.Data.List.GetD

/-!
# Exact wire identities across a drawn source layer

Prefix and suffix wires continue at their actual new cut positions. A consumed
wire ends at the source vertex; each newly allocated wire begins there. These
identities join the finite geometric fragments without renumbering an edge.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- The exact generator update of the numbered wire cut. -/
theorem Layer.after_wires {l : Layer} (h : l.HasDrawing) :
    l.after.wires = l.before.wires.take l.instruction.data.offset ++
      List.ofFn (fun j : Fin l.instruction.data.outputs.length => l.before.next + j.val) ++
      l.before.wires.drop (l.instruction.data.offset + l.instruction.data.inputs.length) := by
  obtain ⟨source, target, D, _⟩ := h
  unfold Layer.after
  rw [D.layer_eq]
  rfl

private theorem take_length {l : Layer} (h : l.HasDrawing) :
    (l.before.wires.take l.instruction.data.offset).length = l.instruction.data.offset := by
  have hk := h.constraints.2.2.1
  simp only [List.length_take]
  omega

/-- Prefix bypasses keep their exact edge number at the same position. -/
theorem Layer.after_prefix {l : Layer} (h : l.HasDrawing) (i : ℕ)
    (hi : i < l.instruction.data.offset) :
    l.after.wires.getD i 0 = l.before.wires.getD i 0 := by
  have hbound : i < l.before.wires.length := by have := h.constraints.2.2.1; omega
  rw [l.after_wires h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, take_length h, hi, hbound]

/-- The middle output block contains exactly the newly allocated edge numbers. -/
theorem Layer.after_output {l : Layer} (h : l.HasDrawing)
    (j : Fin l.instruction.data.outputs.length) :
    l.after.wires.getD (l.instruction.data.offset + j.val) 0 = l.before.next + j.val := by
  rw [l.after_wires h]
  have hj := j.isLt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, take_length h,
    show ¬l.instruction.data.offset + j.val < l.instruction.data.offset by omega, hj]

/-- Suffix bypasses shift their cut index by the actual arity change. -/
theorem Layer.after_suffix {l : Layer} (h : l.HasDrawing) (j : ℕ) :
    l.after.wires.getD
      (l.instruction.data.offset + l.instruction.data.outputs.length + j) 0 =
    l.before.wires.getD
      (l.instruction.data.offset + l.instruction.data.inputs.length + j) 0 := by
  rw [l.after_wires h]
  have hcalc : l.instruction.data.offset + l.instruction.data.outputs.length + j -
      l.instruction.data.offset - l.instruction.data.outputs.length = j := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, take_length h,
    show ¬l.instruction.data.offset + l.instruction.data.outputs.length + j <
      l.instruction.data.offset by omega,
    show ¬l.instruction.data.offset + l.instruction.data.outputs.length + j -
      l.instruction.data.offset < l.instruction.data.outputs.length by omega, hcalc]

/-- The new bottom index of a surviving incoming wire; `none` means it ends at the gate. -/
def Layer.exitIndex (l : Layer) (i : ℕ) : Option ℕ :=
  if i < l.instruction.data.offset then some i
  else if i < l.instruction.data.offset + l.instruction.data.inputs.length then none
  else some (l.instruction.data.offset + l.instruction.data.outputs.length +
    (i - (l.instruction.data.offset + l.instruction.data.inputs.length)))

/-- A surviving wire lands inside the actual next cut. -/
theorem Layer.exitIndex_lt {l : Layer} (h : l.HasDrawing) {i j : ℕ}
    (hi : i < l.before.wires.length) (hj : l.exitIndex i = some j) :
    j < l.after.wires.length := by
  obtain ⟨_, _, hk, hlen⟩ := h.constraints
  unfold Layer.exitIndex at hj
  split_ifs at hj with hp hg
  · have := Option.some.inj hj
    omega
  · have := Option.some.inj hj
    omega

/-- The source edge number at each surviving wire is unchanged by the whole layer. -/
theorem Layer.exitIndex_edge {l : Layer} (h : l.HasDrawing) {i j : ℕ}
    (hj : l.exitIndex i = some j) :
    l.after.wires.getD j 0 = l.before.wires.getD i 0 := by
  unfold Layer.exitIndex at hj
  split_ifs at hj with hp hg
  · cases Option.some.inj hj
    exact l.after_prefix h i hp
  · cases Option.some.inj hj
    rw [l.after_suffix h]
    congr 1
    omega

/-- Every created output has a real position in the next cut. -/
theorem Layer.outputIndex_lt {l : Layer} (h : l.HasDrawing)
    (j : Fin l.instruction.data.outputs.length) :
    l.instruction.data.offset + j.val < l.after.wires.length := by
  obtain ⟨_, _, hk, hlen⟩ := h.constraints
  have := j.isLt
  omega

/-- The complete lower-band segment program at a raw cut index. -/
def Layer.bottomPath (l : Layer) (i : ℕ) : List Segment :=
  (Band.curve (l.lowerBand, i)).map (fun s => s.translate 0 (l.middleY + 2))

/-- Follow one incoming edge until the next cut or its consuming vertex. -/
def Layer.incomingRoute (l : Layer) (i : ℕ) : Route :=
  let top := Band.curve (l.upperBand, i)
  let k := l.instruction.data.offset
  let a := l.instruction.data.inputs.length
  let b := l.instruction.data.outputs.length
  ⟨l.before.wires.getD i 0,
    if i < k then top ++ (l.prefixRoutes.getD i ⟨0, []⟩).path ++ l.bottomPath i
    else if i < k + a then top ++ (l.inputRoutes.getD (i - k) ⟨0, []⟩).path
    else let j := i - (k + a)
      top ++ (l.suffixRoutes.getD j ⟨0, []⟩).path ++ l.bottomPath (k + b + j)⟩

/-- Follow a newly allocated edge from its creating vertex to the next cut. -/
def Layer.createdRoute (l : Layer) (j : ℕ) : Route :=
  ⟨l.before.next + j,
    (l.outputRoutes.getD j ⟨0, []⟩).path ++
      l.bottomPath (l.instruction.data.offset + j)⟩

/-- Route programs grouped into complete cut-to-cut and vertex-to-cut connections. -/
def Layer.connections (l : Layer) : List Route :=
  (List.range l.before.wires.length).map l.incomingRoute ++
    (List.range l.instruction.data.outputs.length).map l.createdRoute

/-- The endpoint of an incoming wire, at the gate or at its new cut position. -/
def Layer.incomingTarget (l : Layer) (i : ℕ) : GridRouting.Point :=
  (l.exitIndex i).elim l.vertexPoint (fun j => (4 * j, l.height))

private theorem prefix_connects (l : Layer) (i : Fin l.instruction.data.offset) :
    Connects (l.prefixRoutes.getD i.val ⟨0, []⟩).path
      (4 * i.val, l.middleY) (4 * i.val, l.middleY + 2) := by
  simpa [Layer.prefixRoutes, List.getD_eq_getElem?_getD, i.isLt] using
    Connects.vertical (4 * i.val) l.middleY (l.middleY + 2) (by omega)

private theorem input_connects (l : Layer) (i : Fin l.instruction.data.inputs.length) :
    Connects (l.inputRoutes.getD i.val ⟨0, []⟩).path
      (4 * l.instruction.data.offset + i.val, l.middleY) l.vertexPoint := by
  have hc := (Connects.vertical (4 * l.instruction.data.offset + i.val)
      l.middleY (l.middleY + 1) (by omega)).append
    (Connects.horizontal (4 * l.instruction.data.offset + i.val)
      l.vertexPoint.1 (l.middleY + 1))
  simpa [Layer.inputRoutes, Layer.vertexPoint, List.getD_eq_getElem?_getD, i.isLt] using hc

private theorem output_connects (l : Layer) (i : Fin l.instruction.data.outputs.length) :
    Connects (l.outputRoutes.getD i.val ⟨0, []⟩).path l.vertexPoint
      (4 * l.instruction.data.offset + i.val, l.middleY + 2) := by
  have hc := (Connects.horizontal l.vertexPoint.1 (4 * l.instruction.data.offset + i.val)
      (l.middleY + 1)).append
    (Connects.vertical (4 * l.instruction.data.offset + i.val)
      (l.middleY + 1) (l.middleY + 2) (by omega))
  simpa [Layer.outputRoutes, Layer.vertexPoint, List.getD_eq_getElem?_getD, i.isLt] using hc

private theorem suffix_connects (l : Layer)
    (i : Fin (l.before.wires.length -
      (l.instruction.data.offset + l.instruction.data.inputs.length))) :
    Connects (l.suffixRoutes.getD i.val ⟨0, []⟩).path
      (4 * l.instruction.data.offset + 4 + 4 * i.val, l.middleY)
      (4 * l.instruction.data.offset + 4 + 4 * i.val, l.middleY + 2) := by
  simpa [Layer.suffixRoutes, List.getD_eq_getElem?_getD, i.isLt] using
    Connects.vertical (4 * l.instruction.data.offset + 4 + 4 * i.val)
      l.middleY (l.middleY + 2) (by omega)

/-- Each complete incoming program really reaches its declared new cut or consuming gate. -/
theorem Layer.incoming_connects {l : Layer} (h : l.HasDrawing)
    (i : Fin l.before.wires.length) :
    Connects (l.incomingRoute i.val).path (4 * i.val, 0) (l.incomingTarget i.val) := by
  have htop := l.upper_connects i
  by_cases hp : i.val < l.instruction.data.offset
  · have he : l.exitIndex i.val = some i.val := by simp [Layer.exitIndex, hp]
    have hbot := l.lower_connects ⟨i.val, l.exitIndex_lt h i.isLt he⟩
    have ht : Connects (Band.curve (l.upperBand, i.val)) (4 * i.val, 0)
        (4 * i.val, l.middleY) := by simpa [expanded, hp] using htop
    have hb : Connects (l.bottomPath i.val) (4 * i.val, l.middleY + 2)
        (4 * i.val, l.height) := by simpa [Layer.bottomPath, expanded, hp] using hbot
    simpa [Layer.incomingRoute, Layer.incomingTarget, he, hp] using
      (ht.append (prefix_connects l ⟨i.val, hp⟩)).append hb
  · by_cases hg : i.val < l.instruction.data.offset + l.instruction.data.inputs.length
    · have hj : i.val - l.instruction.data.offset < l.instruction.data.inputs.length := by omega
      have he : l.exitIndex i.val = none := by simp [Layer.exitIndex, hp, hg]
      have ht : Connects (Band.curve (l.upperBand, i.val)) (4 * i.val, 0)
          (4 * l.instruction.data.offset + (i.val - l.instruction.data.offset), l.middleY) := by
        simpa [expanded, hp, hg] using htop
      simpa [Layer.incomingRoute, Layer.incomingTarget, he, hp, hg] using
        ht.append (input_connects l ⟨i.val - l.instruction.data.offset, hj⟩)
    · let j := i.val - (l.instruction.data.offset + l.instruction.data.inputs.length)
      have hj : j < l.before.wires.length -
          (l.instruction.data.offset + l.instruction.data.inputs.length) := by
        have := i.isLt
        dsimp [j]
        omega
      let j' := l.instruction.data.offset + l.instruction.data.outputs.length + j
      have he : l.exitIndex i.val = some j' := by simp [Layer.exitIndex, hp, hg, j', j]
      have hbot := l.lower_connects ⟨j', l.exitIndex_lt h i.isLt he⟩
      have ht : Connects (Band.curve (l.upperBand, i.val)) (4 * i.val, 0)
          (4 * l.instruction.data.offset + 4 + 4 * j, l.middleY) := by
        simpa [expanded, hp, hg, j] using htop
      have hb : Connects (l.bottomPath j')
          (4 * l.instruction.data.offset + 4 + 4 * j, l.middleY + 2)
          (4 * j', l.height) := by
        have hk : ¬j' < l.instruction.data.offset := by dsimp [j']; omega
        have hk' : ¬j' < l.instruction.data.offset + l.instruction.data.outputs.length := by
          dsimp [j']; omega
        simpa [Layer.bottomPath, expanded, hk, hk', j'] using hbot
      simpa [Layer.incomingRoute, Layer.incomingTarget, he, hp, hg, j', j] using
        (ht.append (suffix_connects l ⟨j, hj⟩)).append hb

/-- Each new edge starts at the real gate and reaches its actual allocated cut position. -/
theorem Layer.created_connects {l : Layer} (h : l.HasDrawing)
    (j : Fin l.instruction.data.outputs.length) :
    Connects (l.createdRoute j.val).path l.vertexPoint
      (4 * (l.instruction.data.offset + j.val), l.height) := by
  have hb := l.lower_connects ⟨l.instruction.data.offset + j.val, l.outputIndex_lt h j⟩
  have hp : ¬l.instruction.data.offset + j.val < l.instruction.data.offset := by omega
  have hg : l.instruction.data.offset + j.val <
      l.instruction.data.offset + l.instruction.data.outputs.length := by have := j.isLt; omega
  have hb' : Connects (l.bottomPath (l.instruction.data.offset + j.val))
      (4 * l.instruction.data.offset + j.val, l.middleY + 2)
      (4 * (l.instruction.data.offset + j.val), l.height) := by
    simpa [Layer.bottomPath, expanded, hp, hg] using hb
  exact (output_connects l j).append hb'

@[fun_prop] theorem Layer.exitIndex_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.exitIndex q.2)
      (encPair encLayer encUnary) (encOption encUnary) := by
  unfold Layer.exitIndex
  fun_prop

set_option maxHeartbeats 1000000 in
@[fun_prop] theorem Layer.bottomPath_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.bottomPath q.2)
      (encPair encLayer encUnary) (encList encSegment) := by
  have hc : ComputableInPolyTime (fun q : Layer × ℕ => Band.curve (q.1.lowerBand, q.2))
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  have hs : ComputableInPolyTime (fun q : Layer × ℕ => q.1.middleY + 2)
      (encPair encLayer encUnary) encUnary := by fun_prop
  have ht : ComputableInPolyTime (fun q : ℕ × Segment => q.2.translate 0 q.1)
      (encPair encUnary encSegment) encSegment := by fun_prop
  exact ComputableInPolyTime.mapWith ht hs hc

@[fun_prop] theorem Layer.incomingRoute_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.incomingRoute q.2)
      (encPair encLayer encUnary) encRoute := by
  have ht : ComputableInPolyTime (fun q : Layer × ℕ => Band.curve (q.1.upperBand, q.2))
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  have hp : ComputableInPolyTime (fun q : Layer × ℕ =>
      (q.1.prefixRoutes.getD q.2 ⟨0, []⟩).path)
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  have hi : ComputableInPolyTime (fun q : Layer × ℕ =>
      (q.1.inputRoutes.getD (q.2 - q.1.instruction.data.offset) ⟨0, []⟩).path)
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  have hs : ComputableInPolyTime (fun q : Layer × ℕ =>
      (q.1.suffixRoutes.getD (q.2 - (q.1.instruction.data.offset +
        q.1.instruction.data.inputs.length)) ⟨0, []⟩).path)
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  have hb : ComputableInPolyTime (fun q : Layer × ℕ => q.1.bottomPath
      (q.1.instruction.data.offset + q.1.instruction.data.outputs.length +
        (q.2 - (q.1.instruction.data.offset + q.1.instruction.data.inputs.length))))
      (encPair encLayer encUnary) (encList encSegment) := by fun_prop
  unfold Layer.incomingRoute
  dsimp only
  fun_prop

@[fun_prop] theorem Layer.createdRoute_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.createdRoute q.2)
      (encPair encLayer encUnary) encRoute := by
  unfold Layer.createdRoute
  fun_prop

@[fun_prop] theorem Layer.connections_polyTime :
    ComputableInPolyTime Layer.connections encLayer (encList encRoute) := by
  unfold Layer.connections
  fun_prop

end PushPuzzle.PushFS.Reduction.Plan
