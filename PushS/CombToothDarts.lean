/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSourceDarts
public import PushS.CombTreeStations
import all PushS.CombPartition
import all PushS.CombDarts

/-! Canonical actual comb-tooth darts at the native tips, lower feet and genuine crossing occurrences. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The original lower foot is exactly the first literal station of its actual tooth. -/
theorem toothStation_first (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    toothStation width d vertex 0 = .foot vertex := by
  simp only [toothStation, toothStations, List.get_eq_getElem, Fin.val_zero, List.cons_append, List.getElem_cons_zero]

/-- The original native tip is exactly the final literal station of its actual tooth. -/
theorem toothStation_last (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    toothStation width d vertex (Fin.last ((toothCrossings width d vertex).length + 1)) = .tip vertex := by
  let index := (toothCrossings width d vertex).length + 1
  have hi : index < (toothStations width d vertex).length := by rw [toothStations_length]; omega
  have hget : toothStation width d vertex (Fin.last ((toothCrossings width d vertex).length + 1)) =
      (toothStations width d vertex).getD index (.tip vertex) := by
    rw [List.getD_eq_getElem _ _ hi]
    rfl
  rw [hget]
  unfold toothStations
  convert List.getD_append_cons_length _ [] (Station.tip (width := width) vertex) (Station.tip vertex) using 2
  simp only [index, List.length_cons, List.length_map, List.length_attach]

/-- The original complete crossing occurrence at one actual ascending tooth-list index. -/
@[expose] def toothCrossingHit (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (hit : Fin (toothCrossings width d vertex).length) : {c // c ∈ crossings width d} :=
  ⟨(toothCrossings width d vertex).get hit, by exact (tooth_mem width d (List.get_mem _ hit)).1⟩

/-- The indexed tooth encounter retains exactly its own original native vertex. -/
theorem toothCrossingHit_vertex (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (hit : Fin (toothCrossings width d vertex).length) : (toothCrossingHit width d vertex hit).val.vertex = vertex.val :=
  (tooth_mem width d (List.get_mem _ hit)).2

/-- Reading the corresponding literal tooth station returns exactly that complete global occurrence. -/
theorem toothStation_crossing (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (hit : Fin (toothCrossings width d vertex).length) :
    toothStation width d vertex hit.succ.castSucc = .crossing (toothCrossingHit width d vertex hit) := by
  simp only [toothStation, toothStations, List.get_eq_getElem, Fin.val_castSucc, Fin.val_succ,
    List.cons_append, List.getElem_cons_succ]
  rw [List.getElem_append_left (by simpa only [List.length_map, List.length_attach] using hit.isLt)]
  simp only [List.getElem_map, List.getElem_attach]
  rfl

/-- The actual upward tooth dart at its original lower foot. -/
@[expose] def toothFootDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) : Graph.Dart (augmentedGraph width hd) :=
  (Piece.tooth vertex 0).dart width hd false

/-- The actual downward tooth dart at its original native source tip. -/
@[expose] def toothTipDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) : Graph.Dart (augmentedGraph width hd) :=
  (Piece.tooth vertex (Fin.last (toothCrossings width d vertex).length)).dart width hd true

/-- The actual upward foot dart has exactly its original numbered foot endpoint. -/
theorem toothFootDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) :
    (toothFootDart width hd vertex).vertex = stationNumber width d (.foot vertex) := by
  rw [toothFootDart, Piece.dart_vertex]
  simp only [Piece.station, Bool.false_eq_true, ite_false, Fin.castSucc_zero, toothStation_first]

/-- The actual downward tip dart has exactly its original numbered native endpoint. -/
theorem toothTipDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) :
    (toothTipDart width hd vertex).vertex = stationNumber width d (.tip vertex) := by
  rw [toothTipDart, Piece.dart_vertex]
  simp only [Piece.station, ite_true, Fin.succ_last, toothStation_last]

private theorem crossing_mem_tooth (width : ℕ) (d : Graph.OrthogonalDrawing) (hit : {c // c ∈ crossings width d}) :
    hit.val ∈ toothCrossings width d (.crossing hit : Station width d).tooth := by
  apply (toothCrossings_perm width d _).mem_iff.mpr
  exact List.mem_filter.mpr ⟨hit.property, by simp [Station.tooth]⟩

/-- The exact original ascending tooth-list index of a genuine global crossing occurrence. -/
@[expose] def toothHitIndex (width : ℕ) (d : Graph.OrthogonalDrawing) (hit : {c // c ∈ crossings width d}) :
    Fin (toothCrossings width d (.crossing hit : Station width d).tooth).length :=
  ⟨(toothCrossings width d (.crossing hit : Station width d).tooth).idxOf hit.val, by
    exact List.idxOf_lt_length_of_mem (crossing_mem_tooth width d hit)⟩

/-- Re-reading the actual ascending index retains the same complete global crossing occurrence. -/
theorem toothCrossingHit_index (width : ℕ) (d : Graph.OrthogonalDrawing) (hit : {c // c ∈ crossings width d}) :
    toothCrossingHit width d (.crossing hit : Station width d).tooth (toothHitIndex width d hit) = hit := by
  apply Subtype.ext
  simp only [toothCrossingHit, toothHitIndex, List.get_eq_getElem, List.getElem_idxOf]

/-- The actual upward or downward tooth dart at one genuine global crossing occurrence. -/
@[expose] def toothCrossingDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) (upward : Bool) :
    Graph.Dart (augmentedGraph width hd) :=
  let index := toothHitIndex width d hit
  (Piece.tooth (.crossing hit : Station width d).tooth (if upward then index.succ else index.castSucc)).dart width hd (!upward)

/-- Both canonical tooth-side darts occupy their exact original numbered crossing station. -/
theorem toothCrossingDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) (upward : Bool) :
    (toothCrossingDart width hd hit upward).vertex = stationNumber width d (.crossing hit) := by
  rw [toothCrossingDart, Piece.dart_vertex]
  cases upward <;> simp only [Piece.station, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true, Fin.succ_castSucc, toothStation_crossing, toothCrossingHit_index]

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The genuine tooth foot dart has precisely the real upward compass direction. -/
theorem toothFootDart_direction (vertex : Fin d.1.length) :
    (augmentedDrawing width height hd hfit hhead).direction (toothFootDart width hd vertex) = octantAngle 6 := by
  rw [toothFootDart, Piece.dart_direction]
  exact toothPiece_direction width height hd hfit vertex 0 false

/-- The genuine tooth tip dart has precisely the real downward compass direction. -/
theorem toothTipDart_direction (vertex : Fin d.1.length) :
    (augmentedDrawing width height hd hfit hhead).direction (toothTipDart width hd vertex) = octantAngle 2 := by
  rw [toothTipDart, Piece.dart_direction]
  exact toothPiece_direction width height hd hfit vertex _ true

/-- The actual crossing's upper and lower tooth darts have precisely the two real vertical directions. -/
theorem toothCrossingDart_direction (hit : {c // c ∈ crossings width d}) (upward : Bool) :
    (augmentedDrawing width height hd hfit hhead).direction (toothCrossingDart width hd hit upward) =
      octantAngle (if upward then 6 else 2) := by
  rw [toothCrossingDart, Piece.dart_direction]
  have h := toothPiece_direction width height hd hfit (.crossing hit : Station width d).tooth
    (if upward then (toothHitIndex width d hit).succ else (toothHitIndex width d hit).castSucc) (!upward)
  cases upward <;> exact h

end Geometry
end PushPuzzle.PushS.Comb
