/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNativeStationDarts
public import PushS.OctantSuccessor
import all PushS.CombPartition
import all PushS.CombSourceDarts
import all PushS.PreparedRayOrder
import all PushS.CombGenus

/-! The three actual sorted weighted fan slots name their original geometric source-tip darts. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The actual compiler fan retains nondecreasing original tangent keys. -/
theorem fan_pairwise (width : ℕ) (input : Input) (vertex : ℕ) :
    (fan width input vertex).Pairwise (fun a b => tangentKey (outgoingVector width input.drawing a.1) ≤
      tangentKey (outgoingVector width input.drawing b.1)) := by
  let decorated := (input.graph.vertices.getD vertex ⟨[], 0⟩).ports.map fun p =>
    (tangentKey (outgoingVector width input.drawing p.1), p)
  change ((Sort.run Prod.fst (0, ⟨⟨0, false⟩, 0⟩) decorated).map Prod.snd).Pairwise _
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ (Sort.run_pairwise Prod.fst (0, ⟨⟨0, false⟩, 0⟩) decorated)
  intro a b ha hb hab
  obtain ⟨pa, _, rfl⟩ := List.mem_map.mp ((Sort.run_perm Prod.fst (0, ⟨⟨0, false⟩, 0⟩) decorated).mem_iff.mp ha)
  obtain ⟨pb, _, rfl⟩ := List.mem_map.mp ((Sort.run_perm Prod.fst (0, ⟨⟨0, false⟩, 0⟩) decorated).mem_iff.mp hb)
  exact hab

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d)

include drawing hd in
private theorem native_count : d.1.length = g.vertices.length := by
  rw [hd.vertexCount]
  simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_range]

/-- An original native fan slot retains its complete sorted weighted port. -/
@[expose] def nativeFanPort (vertex : Fin d.1.length) (slot : Fin 3) : NCL.WeightedPort ℕ :=
  (fan width ⟨g, d⟩ vertex.val).get ⟨slot.val, by
    rw [fan_length width ⟨g, d⟩ hg (by rw [← native_count drawing hd]; exact vertex.isLt)]
    exact slot.isLt⟩

/-- The indexed weighted port occurs in exactly the original compiler fan. -/
theorem nativeFanPort_mem (vertex : Fin d.1.length) (slot : Fin 3) :
    nativeFanPort width hg drawing hd vertex slot ∈ fan width ⟨g, d⟩ vertex.val := List.get_mem _ _

private theorem nativeFanPort_bounded (vertex : Fin d.1.length) (slot : Fin 3) :
    (nativeFanPort width hg drawing hd vertex slot).1.edge < g.edgeCount := by
  have hv : vertex.val < g.vertices.length := by rw [← native_count drawing hd]; exact vertex.isLt
  have hp := (fan_perm width ⟨g, d⟩ vertex.val).mem_iff.mp (nativeFanPort_mem width hg drawing hd vertex slot)
  apply hg.1 _ (by rw [List.getD_eq_getElem _ _ hv]; exact List.getElem_mem hv) _ hp

/-- The literal original source-tip dart selected by one of the compiler's three fan slots. -/
@[expose] def nativeFanDart (vertex : Fin d.1.length) (slot : Fin 3) : Graph.Dart (augmentedGraph width hd) :=
  sourceTipDart width hd (nativeEdgeIndex drawing ⟨(nativeFanPort width hg drawing hd vertex slot).1.edge,
    by exact nativeFanPort_bounded width hg drawing hd vertex slot⟩) (nativeFanPort width hg drawing hd vertex slot).1.dir

/-- Each actual fan dart retains exactly the original slot's incidence token. -/
theorem nativeFanDart_token (vertex : Fin d.1.length) (slot : Fin 3) :
    dartToken width hd (nativeFanDart width hg drawing hd vertex slot) =
      some (incidenceToken (nativeFanPort width hg drawing hd vertex slot).1) := by
  rw [nativeFanDart, sourceTipDart_token]
  rfl

/-- Distinct original sorted slots name distinct actual source darts. -/
theorem nativeFanDart_injective (vertex : Fin d.1.length) :
    Function.Injective (nativeFanDart width hg drawing hd vertex) := by
  intro left right he
  have ht := congrArg (dartToken width hd) he
  rw [nativeFanDart_token, nativeFanDart_token] at ht
  have hv : vertex.val < g.vertices.length := by rw [← native_count drawing hd]; exact vertex.isLt
  have hn := fan_tips_nodup width ⟨g, d⟩ hg hv
  have hl : left.val < ((fan width ⟨g, d⟩ vertex.val).map (fun p => incidenceToken p.1)).length := by
    rw [List.length_map, fan_length width ⟨g, d⟩ hg hv]
    exact left.isLt
  have hr : right.val < ((fan width ⟨g, d⟩ vertex.val).map (fun p => incidenceToken p.1)).length := by
    rw [List.length_map, fan_length width ⟨g, d⟩ hg hv]
    exact right.isLt
  have helem : ((fan width ⟨g, d⟩ vertex.val).map (fun p => incidenceToken p.1))[left.val] =
      ((fan width ⟨g, d⟩ vertex.val).map (fun p => incidenceToken p.1))[right.val] := by
    simpa only [List.getElem_map, nativeFanPort, List.get_eq_getElem] using Option.some.inj ht
  have hi := hn.injective_get (a₁ := ⟨left.val, hl⟩) (a₂ := ⟨right.val, hr⟩) helem
  have hval : left.val = right.val := congrArg (fun index => index.val) hi
  exact Fin.ext hval

/-- The original four-way tangent key of one actual sorted native fan slot. -/
@[expose] def nativeFanKey (vertex : Fin d.1.length) (slot : Fin 3) : Fin 4 :=
  ⟨tangentKey (outgoingVector width d (nativeFanPort width hg drawing hd vertex slot).1), tangentKey_lt _⟩

section Geometry

variable (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

include hfit in
/-- Each genuine original weighted fan slot occupies exactly its original native tip. -/
theorem nativeFanDart_vertex (vertex : Fin d.1.length) (slot : Fin 3) :
    (nativeFanDart width hg drawing hd vertex slot).vertex = stationNumber width d (.tip vertex) := by
  apply (native_dart_vertex_tip_iff width height g hg.1 drawing hd hfit _ vertex).mpr
  left
  refine ⟨⟨(nativeFanPort width hg drawing hd vertex slot).1.edge,
    nativeFanPort_bounded width hg drawing hd vertex slot⟩, (nativeFanPort width hg drawing hd vertex slot).1.dir,
    (nativeFanPort width hg drawing hd vertex slot).2, ?_, rfl⟩
  exact nativeFanPort_mem width hg drawing hd vertex slot

include hfit in
/-- The full actual native fiber consists of its three sorted original fan darts and its downward tooth. -/
theorem nativeFanDart_cover (vertex : Fin d.1.length) (dart : Graph.Dart (augmentedGraph width hd))
    (hv : dart.vertex = stationNumber width d (.tip vertex)) :
    (∃ slot : Fin 3, nativeFanDart width hg drawing hd vertex slot = dart) ∨ dart = toothTipDart width hd vertex := by
  rcases (native_dart_vertex_tip_iff width height g hg.1 drawing hd hfit dart vertex).mp hv with ⟨edge, side, weight, hp, rfl⟩ | he
  · obtain ⟨index, he⟩ := List.mem_iff_get.mp hp
    have hv' : vertex.val < g.vertices.length := by rw [← native_count drawing hd]; exact vertex.isLt
    let slot : Fin 3 := ⟨index.val, by rw [← fan_length width ⟨g, d⟩ hg hv']; exact index.isLt⟩
    have hport : nativeFanPort width hg drawing hd vertex slot = (⟨⟨edge.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) := he
    left
    refine ⟨slot, dartToken_some_injective width hd _ _ _ ?_ (sourceTipDart_token width hd (nativeEdgeIndex drawing edge) side)⟩
    rw [nativeFanDart_token, hport]
    rfl
  · exact Or.inr he

/-- An actual fan slot has exactly the original compiler tangent's compass angle. -/
theorem nativeFanDart_direction (vertex : Fin d.1.length) (slot : Fin 3) :
    (augmentedDrawing width height hd hfit hhead).direction (nativeFanDart width hg drawing hd vertex slot) =
      octantAngle (tangentOctant (outgoingVector width d (nativeFanPort width hg drawing hd vertex slot).1)) := by
  rw [nativeFanDart, sourceTipDart_direction]
  rfl

include hfit hhead in
/-- The actual native fan's original tangent keys increase strictly in its literal emitted slot order. -/
theorem nativeFanKey_strictMono (vertex : Fin d.1.length) : StrictMono (nativeFanKey width hg drawing hd vertex) := by
  intro left right hlt
  have hle := (fan_pairwise width ⟨g, d⟩ vertex.val).rel_get_of_lt
    (a := ⟨left.val, by rw [fan_length width ⟨g, d⟩ hg (by rw [← native_count drawing hd]; exact vertex.isLt)]; exact left.isLt⟩)
    (b := ⟨right.val, by rw [fan_length width ⟨g, d⟩ hg (by rw [← native_count drawing hd]; exact vertex.isLt)]; exact right.isLt⟩) hlt
  apply lt_of_le_of_ne hle
  intro he
  change tangentKey (outgoingVector width d (nativeFanPort width hg drawing hd vertex left).1) =
    tangentKey (outgoingVector width d (nativeFanPort width hg drawing hd vertex right).1) at he
  have hdir : (augmentedDrawing width height hd hfit hhead).direction (nativeFanDart width hg drawing hd vertex left) =
      (augmentedDrawing width height hd hfit hhead).direction (nativeFanDart width hg drawing hd vertex right) := by
    rw [nativeFanDart_direction, nativeFanDart_direction]
    unfold tangentOctant
    rw [he]
  have heq := (augmentedDrawing_realizes_rotation width height hd hfit hhead).directions_injective _ _
    ((nativeFanDart_vertex width hg drawing hd height hfit vertex left).trans
      (nativeFanDart_vertex width hg drawing hd height hfit vertex right).symm) hdir
  exact (ne_of_lt hlt) (nativeFanDart_injective width hg drawing hd vertex heq)

end Geometry
end Native
end PushPuzzle.PushS.Comb
