/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

import all CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Program
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Program.Correctness
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering.Rows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time row arrays for actual block emission

All vertices and owned wires emitted by a block have that block's row. Repeating the row for
the exact template lengths gives polynomial-time arrays in the same actual numbering.

## Main definitions

* `PushPuzzle.NCL.SelectorNetwork.AndOr.Program.vertexRows`: rows of emitted standard vertices.
* `PushPuzzle.NCL.SelectorNetwork.AndOr.Program.ownerRows`: rows of emitted wire owners.

## Main results

* `PushPuzzle.NCL.SelectorNetwork.AndOr.Program.vertexRows_blocks`: exact numbered source rows.
* `PushPuzzle.NCL.SelectorNetwork.AndOr.Program.ownerRows_blocks`: exact numbered wire-owner rows.
-/

public section

namespace PushPuzzle.NCL.SelectorNetwork.AndOr.Program

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.SelectorNetwork Cslib.Complexity.NCL.SelectorNetwork.AndOr Cslib.Complexity.NCL.SelectorNetwork.AndOr.Program Cslib Diagram _root_.Turing.MultiTapeTM

/-- Source rows in exact emitted standard-vertex order. -/
@[expose] def vertexRows {budget : ℕ} (blocks : List (Block budget)) : List ℕ :=
  blocks.flatMap fun b => List.replicate b.shape.val.template.vertices.length b.row

/-- Owner rows in exact shared/private wire emission order. -/
@[expose] def ownerRows {budget : ℕ} (blocks : List (Block budget)) : List ℕ :=
  blocks.flatMap fun b => List.replicate
    (b.ownedNames.length + b.shape.val.template.privateWires.length) b.row

/-- Source rows are emitted in polynomial time under the standard block encoding. -/
theorem computableInPolyTime_vertexRows (budget : ℕ) :
    ComputableInPolyTime (vertexRows (budget := budget)) (encList (encBlock budget))
      (encList encUnary) := by
  have ht := encTemplate_vertices_polyTime (computableInPolyTime_blockTemplate budget)
  have hr := encBlock_row_polyTime budget (ComputableInPolyTime.id' (encIn := encBlock budget))
  have hb : ComputableInPolyTime (fun b : Block budget =>
      List.replicate b.shape.val.template.vertices.length b.row) (encBlock budget)
      (encList encUnary) := by fun_prop
  unfold vertexRows
  apply ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.id'
  simpa only [Function.comp_def] using hb.comp
    (ComputableInPolyTime.snd (encList (encBlock budget)) (encBlock budget))

/-- Wire-owner rows are emitted in polynomial time under the standard block encoding. -/
theorem computableInPolyTime_ownerRows (budget : ℕ) :
    ComputableInPolyTime (ownerRows (budget := budget)) (encList (encBlock budget))
      (encList encUnary) := by
  have ht := encTemplate_privateWires_polyTime (computableInPolyTime_blockTemplate budget)
  have ho := encBlock_ownedNames_polyTime budget
    (ComputableInPolyTime.id' (encIn := encBlock budget))
  have hr := encBlock_row_polyTime budget (ComputableInPolyTime.id' (encIn := encBlock budget))
  have hb : ComputableInPolyTime (fun b : Block budget => List.replicate
      (b.ownedNames.length + b.shape.val.template.privateWires.length) b.row) (encBlock budget)
      (encList encUnary) := by fun_prop
  unfold ownerRows
  apply ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.id'
  simpa only [Function.comp_def] using hb.comp
    (ComputableInPolyTime.snd (encList (encBlock budget)) (encBlock budget))

variable {U C R : Type*} [DecidableEq U] [DecidableEq C] [DecidableEq R]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m budget : ℕ} (order : Vert U C R ≃ Fin m)
variable (hshape : ∀ v, (cell N A v).top.length ≤ budget)
variable (stride : ℕ) (row : Vert U C R → ℕ)

/-- Row repetition agrees with the exact finite vertex numbering of the same graph. -/
theorem vertexRows_blocks : vertexRows (blocks N A order hshape stride row) =
    List.ofFn (Numbering.vertexRow N A order row) := by
  change _ = List.ofFn (fun i => row ((Numbering.vertexList N A order).get i).1)
  rw [List.ofFn_comp' (Numbering.vertexList N A order).get (fun v => row v.1), List.ofFn_get]
  simp only [vertexRows, blocks, List.flatMap_map, Cell.template, List.length_map,
    Numbering.vertexList, List.sigma, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro v _
  simp only [List.map_const', List.length_ofFn]

/-- Row repetition agrees with the exact finite owner numbering of shared and private wires. -/
theorem ownerRows_blocks : ownerRows (blocks N A order hshape stride row) =
    List.ofFn (Numbering.ownerRow N A order row) := by
  change _ = List.ofFn (fun i =>
    row (Numbering.edgeOwner N A ((Numbering.edgeList N A order).get i)))
  rw [List.ofFn_comp' (Numbering.edgeList N A order).get
    (fun e => row (Numbering.edgeOwner N A e)), List.ofFn_get]
  simp only [ownerRows, blocks, List.flatMap_map, Cell.template, List.length_map,
    Numbering.edgeList, List.map_flatMap]
  apply List.flatMap_congr
  intro v _
  have hm : (Numbering.localEdges N A v).map (fun e => row (Numbering.edgeOwner N A e)) =
      (Numbering.localEdges N A v).map (fun _ => row v) := by
    apply List.map_congr_left
    intro e he
    rw [Numbering.owner_mem_localEdges N A v e he]
  rw [hm, List.map_const']
  simp only [Numbering.localEdges, List.length_append, List.length_map]

end PushPuzzle.NCL.SelectorNetwork.AndOr.Program
