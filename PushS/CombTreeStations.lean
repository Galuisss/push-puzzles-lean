/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRootedOrientation
public import PushS.RootedTreeGrowth
import all PushS.CombTeeth
import all PushS.CombPartition

/-! The literal branch-station arrays of the actual rooted comb tree. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- Every station listed on a native tooth retains precisely that native vertex identity. -/
theorem toothStations_owner (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    {station : Station width d} (hs : station ∈ toothStations width d vertex) : station.tooth = vertex := by
  rcases toothStation_cases width d vertex hs with rfl | rfl | ⟨hit, hc, rfl⟩
  · rfl
  · rfl
  · exact Fin.ext (tooth_mem width d hc).2

/-- The complete genuine station array of each actual source tooth has no repeated identity. -/
theorem toothStations_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length) :
    (toothStations width d vertex).Nodup := by
  apply (toothStations_strict width height hd hfit vertex).imp
  intro a b hlt he
  exact (ne_of_lt hlt) (congrArg (fun station => (stationPoint width d station).2) he)

/-- The actual indexed getter reconstructs exactly the original complete tooth station array. -/
theorem toothStations_ofFn (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    List.ofFn (toothStation width d vertex) = toothStations width d vertex := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, toothStations_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, toothStation, List.get_eq_getElem]

/-- Every fresh station above the foot is an original tip or an emitted crossing. -/
theorem toothStations_tail_ne_foot (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    {station : Station width d} (hs : station ∈ (toothStations width d vertex).tail) (foot : Fin d.1.length) :
    station ≠ .foot foot := by
  change station ∈ ((toothCrossings width d vertex).attach.map (fun hit =>
    Station.crossing ⟨hit.val, (tooth_mem width d hit.property).1⟩) ++ [.tip vertex]) at hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨hit, _, rfl⟩ := List.mem_map.mp hs
    intro he
    cases he
  · have he := List.mem_singleton.mp hs
    rw [he]
    intro he
    cases he

/-- All actual lower feet in the same geometric order as the emitted source tooth array. -/
@[expose] def spineStations (width : ℕ) (d : Graph.OrthogonalDrawing) : List (Station width d) :=
  List.ofFn (fun rank => .foot (spineVertex width d rank))

/-- Every actual native foot is retained in the original spine station array. -/
theorem foot_mem_spineStations (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    Station.foot vertex ∈ spineStations width d := by
  obtain ⟨rank, hr⟩ := spineVertex_surjective width d vertex
  exact List.mem_ofFn.mpr ⟨rank, congrArg Station.foot hr⟩

/-- The actual source-comb feet are listed without repetition. -/
theorem spineStations_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    (spineStations width d).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j he
  apply (spineVertex_strictMono width height hd hfit).injective
  exact congrArg (fun vertex : Fin d.1.length => ((prepare width d).1.getD vertex (0, 0)).1) (Station.foot.inj he)

/-- The complete fresh-node array of all native tooth branches retains every occurrence once. -/
theorem tooth_tails_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    ((List.finRange d.1.length).flatMap (fun vertex => (toothStations width d vertex).tail)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun vertex _ => (toothStations_nodup width height hd hfit vertex).tail, ?_⟩
  apply List.Pairwise.imp (fun {a b} hne => ?_) (List.nodup_finRange _)
  apply List.disjoint_left.mpr
  intro station ha hb
  exact hne ((toothStations_owner width d a (List.mem_of_mem_tail ha)).symm.trans
    (toothStations_owner width d b (List.mem_of_mem_tail hb)))

/-- The fresh tooth stations are disjoint from the entire actual spine-foot array. -/
theorem tooth_tails_disjoint_spine (width : ℕ) (d : Graph.OrthogonalDrawing) :
    List.Disjoint ((List.finRange d.1.length).flatMap (fun vertex => (toothStations width d vertex).tail))
      (spineStations width d) := by
  apply List.disjoint_left.mpr
  intro station hs hf
  obtain ⟨vertex, _, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨rank, he⟩ := List.mem_ofFn.mp hf
  exact toothStations_tail_ne_foot width d vertex hs _ he.symm

end PushPuzzle.PushS.Comb
