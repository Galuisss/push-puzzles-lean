/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombEvents
public import PushS.CombSort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-! Actual tooth order, crossing-height order, and source-route crossing order. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal Turing.MultiTapeTM

/-- Original vertex identities sorted by their actual prepared contour columns. -/
@[expose] def vertexOrder (width : ℕ) (d : Graph.OrthogonalDrawing) : List (Point × ℕ) :=
  Sort.run (fun sv => sv.1.1.toNat) ((0, 0), 0) (prepare width d).1.zipIdx

/-- The actual original vertex's position in the emitted tooth order. -/
@[expose] def vertexRank (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : ℕ) : ℕ :=
  ((vertexOrder width d).map Prod.snd).idxOf vertex

/-- Crossings on one tooth, in increasing actual intersection-height order. -/
@[expose] def toothCrossings (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : ℕ) : List Crossing :=
  Sort.run (fun c => c.height.toNat) ⟨0, 0, 0, 0, false⟩
    ((crossings width d).filter fun c => decide (c.vertex = vertex))

/-- Lexicographic source-segment order and then the actual direction along that segment. -/
@[expose] def routeKey (width : ℕ) (d : Graph.OrthogonalDrawing) (c : Crossing) : ℕ :=
  c.segment * (d.1.length + 1) +
    if c.forward then vertexRank width d c.vertex else d.1.length - vertexRank width d c.vertex

/-- Every original edge's crossings, read in its actual source route order. -/
@[expose] def edgeCrossings (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) : List Crossing :=
  let decorated := ((crossings width d).filter fun c => decide (c.edge = edge)).map fun c =>
    (routeKey width d c, c)
  (Sort.run Prod.fst (0, ⟨0, 0, 0, 0, false⟩) decorated).map Prod.snd

/-- The tooth ordering retains every original vertex position and identity. -/
theorem vertexOrder_perm (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (vertexOrder width d).Perm (prepare width d).1.zipIdx := Sort.run_perm _ _ _

/-- The actual tooth order follows the computed prepared column keys. -/
theorem vertexOrder_pairwise (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (vertexOrder width d).Pairwise (fun a b => a.1.1.toNat ≤ b.1.1.toNat) :=
  Sort.run_pairwise _ _ _

/-- Every tooth-height occurrence remains its original crossing record. -/
theorem toothCrossings_perm (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : ℕ) :
    (toothCrossings width d vertex).Perm ((crossings width d).filter fun c => decide (c.vertex = vertex)) :=
  Sort.run_perm _ _ _

/-- Actual crossings on a tooth follow their computed nonnegative height keys. -/
theorem toothCrossings_pairwise (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : ℕ) :
    (toothCrossings width d vertex).Pairwise (fun a b => a.height.toNat ≤ b.height.toNat) :=
  Sort.run_pairwise _ _ _

/-- Every edge retains exactly the original crossing occurrences bearing its edge identity. -/
theorem edgeCrossings_perm (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeCrossings width d edge).Perm ((crossings width d).filter fun c => decide (c.edge = edge)) := by
  have hp := (Sort.run_perm Prod.fst (0, (⟨0, 0, 0, 0, false⟩ : Crossing))
    (((crossings width d).filter fun c => decide (c.edge = edge)).map fun c => (routeKey width d c, c))).map Prod.snd
  simpa only [edgeCrossings, List.map_map, Function.comp_def, List.map_id'] using hp

/-- Every valid original vertex has an actual in-bounds emitted tooth rank. -/
theorem vertexRank_lt (width : ℕ) (d : Graph.OrthogonalDrawing) {v : ℕ} (hv : v < d.1.length) :
    vertexRank width d v < d.1.length := by
  have hp := (vertexOrder_perm width d).map Prod.snd
  have hmem : v ∈ (prepare width d).1.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd]
    simpa only [prepare, List.length_map, ← List.range_eq_range'] using List.mem_range.mpr hv
  have hi := List.idxOf_lt_length_iff.mpr (hp.mem_iff.mpr hmem)
  have hlen := (vertexOrder_perm width d).length_eq
  simpa only [vertexRank, List.length_map, hlen, List.length_zipIdx, prepare] using hi

@[local fun_prop] private theorem vertexKey_polyTime :
    ComputableInPolyTime (fun sv : Point × ℕ => sv.1.1.toNat)
      (encPair encPoint encUnary) encNat := by unfold encPoint; fun_prop

/-- The actual list of ordered teeth is polynomial-time in the standard drawing encoding. -/
@[fun_prop] theorem computableInPolyTime_vertexOrder (width : ℕ) :
    ComputableInPolyTime (vertexOrder width) Graph.encOrthogonalDrawing
      (encList (encPair encPoint encUnary)) := by
  have hs := Sort.computableInPolyTime_run (encPair encPoint encUnary) vertexKey_polyTime ((0, 0), 0)
  have hp := computableInPolyTime_prepare width
  unfold vertexOrder Graph.encOrthogonalDrawing at *
  exact hs.comp (by fun_prop)

/-- Read an actual original vertex's emitted rank with unary list-position output. -/
@[fun_prop] theorem computableInPolyTime_vertexRank (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × ℕ => vertexRank width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing encUnary) encUnary := by
  unfold vertexRank
  fun_prop

@[local fun_prop] private theorem heightKey_polyTime :
    ComputableInPolyTime (fun c : Crossing => c.height.toNat) encCrossing encNat := by fun_prop

/-- The actual intersection-height ordering is standard polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_toothCrossings (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × ℕ => toothCrossings width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing encUnary) (encList encCrossing) := by
  have hs := Sort.computableInPolyTime_run encCrossing heightKey_polyTime ⟨0, 0, 0, 0, false⟩
  unfold toothCrossings
  exact hs.comp (by fun_prop)

/-- Read the actual source-segment/direction key using binary arithmetic on computed ranks. -/
@[fun_prop] theorem computableInPolyTime_routeKey (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × Crossing => routeKey width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing encCrossing) encNat := by
  have hsegment : ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × Crossing => p.2.segment)
      (encPair Graph.encOrthogonalDrawing encCrossing) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hrank : ComputableInPolyTime
      (fun p : Graph.OrthogonalDrawing × Crossing => vertexRank width p.1 p.2.vertex)
      (encPair Graph.encOrthogonalDrawing encCrossing) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold routeKey
  fun_prop

/-- The actual edgewise crossing list is emitted in standard polynomial time. -/
@[fun_prop] theorem computableInPolyTime_edgeCrossings (width : ℕ) :
    ComputableInPolyTime (fun p : Graph.OrthogonalDrawing × ℕ => edgeCrossings width p.1 p.2)
      (encPair Graph.encOrthogonalDrawing encUnary) (encList encCrossing) := by
  have hs := Sort.computableInPolyTime_run (encPair encNat encCrossing)
    (by fun_prop : ComputableInPolyTime (Prod.fst (α := ℕ) (β := Crossing))
      (encPair encNat encCrossing) encNat) (0, ⟨0, 0, 0, 0, false⟩)
  unfold edgeCrossings
  fun_prop

end PushPuzzle.PushS.Comb
