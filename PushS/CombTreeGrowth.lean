/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTreeStations

/-! Actual numbered comb branches grow from the first native foot without repeating a station. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Graph.RootedTreeGrowth

/-- The actual ordered foot labels of the native source comb. -/
@[expose] def spineLabels (width : ℕ) (d : Graph.OrthogonalDrawing) : List ℕ :=
  (spineStations width d).map (stationNumber width d)

private theorem spineLabels_nonempty (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length) :
    spineLabels width d ≠ [] := by
  intro he
  have h := congrArg List.length he
  simp only [spineLabels, spineStations, List.length_map, List.length_ofFn, List.length_nil] at h
  omega

/-- The root is the actual first native foot in the original geometric spine order. -/
@[expose] def treeRoot (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length) : ℕ :=
  (spineLabels width d).head (by exact spineLabels_nonempty width d hv)

/-- Each native tooth retains its existing foot and its full emitted fresh station array. -/
@[expose] def toothBranches (width : ℕ) (d : Graph.OrthogonalDrawing) : List (ℕ × List ℕ) :=
  (List.finRange d.1.length).map (fun vertex =>
    (stationNumber width d (.foot vertex), (toothStations width d vertex).tail.map (stationNumber width d)))

/-- The exact child-to-parent comb-tree edge word from the actual native station arrays. -/
@[expose] def treeEdges (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length) : List (ℕ × ℕ) :=
  pathEdges (treeRoot width d hv) (spineLabels width d).tail ++
    (toothBranches width d).flatMap (fun branch => pathEdges branch.1 branch.2)

private theorem toothBranches_fresh (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (toothBranches width d).flatMap Prod.snd =
      ((List.finRange d.1.length).flatMap (fun vertex => (toothStations width d vertex).tail)).map (stationNumber width d) := by
  simp only [toothBranches, List.flatMap_map, List.map_flatMap]

private theorem toothBranches_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    ((toothBranches width d).flatMap Prod.snd).Nodup := by
  rw [toothBranches_fresh]
  exact (tooth_tails_nodup width height hd hfit).map (stationNumber_injective width d)

private theorem toothBranches_disjoint (width : ℕ) (d : Graph.OrthogonalDrawing) :
    List.Disjoint ((toothBranches width d).flatMap Prod.snd) (spineLabels width d) := by
  rw [toothBranches_fresh]
  apply List.disjoint_left.mpr
  intro label ht hs
  obtain ⟨station, ht, he⟩ := List.mem_map.mp ht
  obtain ⟨foot, hs, hf⟩ := List.mem_map.mp hs
  have hsf := stationNumber_injective width d (he.trans hf.symm)
  exact List.disjoint_left.mp (tooth_tails_disjoint_spine width d) ht (hsf ▸ hs)

private theorem toothBranches_attached (width : ℕ) (d : Graph.OrthogonalDrawing)
    {branch : ℕ × List ℕ} (hb : branch ∈ toothBranches width d) : branch.1 ∈ spineLabels width d := by
  obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp hb
  exact List.mem_map.mpr ⟨_, foot_mem_spineStations width d vertex, rfl⟩

/-- The actual root and tree children retain exactly the whole spine and all fresh tooth arrays. -/
theorem treeEdges_nodes (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length) :
    treeRoot width d hv :: (treeEdges width d hv).map Prod.fst =
      spineLabels width d ++ (toothBranches width d).flatMap Prod.snd := by
  simp only [treeEdges, List.map_append, List.map_flatMap, pathEdges_children]
  rw [← List.cons_append]
  have h : treeRoot width d hv :: (spineLabels width d).tail = spineLabels width d :=
    List.cons_head_tail (spineLabels_nonempty width d hv)
  rw [h]

private theorem nonfoot_mem_tree_nodes (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length)
    (station : Station width d) (hne : ∀ vertex, station ≠ .foot vertex) :
    stationNumber width d station ∈ treeRoot width d hv :: (treeEdges width d hv).map Prod.fst := by
  rw [treeEdges_nodes]
  apply List.mem_append_right
  have hs := station_mem_toothStations width d station
  change station ∈ Station.foot station.tooth :: (toothStations width d station.tooth).tail at hs
  have ht : station ∈ (toothStations width d station.tooth).tail :=
    (List.mem_cons.mp hs).resolve_left (hne station.tooth)
  apply List.mem_flatMap.mpr
  refine ⟨(stationNumber width d (.foot station.tooth), (toothStations width d station.tooth).tail.map (stationNumber width d)),
    ?_, List.mem_map.mpr ⟨station, ht, rfl⟩⟩
  exact List.mem_map.mpr ⟨station.tooth, List.mem_finRange _, rfl⟩

/-- Every genuine source-comb station is retained among the actual tree's root and children. -/
theorem station_mem_tree_nodes (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length)
    (station : Station width d) :
    stationNumber width d station ∈ treeRoot width d hv :: (treeEdges width d hv).map Prod.fst := by
  cases station with
  | foot vertex =>
    rw [treeEdges_nodes]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_, foot_mem_spineStations width d vertex, rfl⟩)
  | tip vertex => exact nonfoot_mem_tree_nodes width d hv (.tip vertex) (by intro _ he; cases he)
  | crossing hit => exact nonfoot_mem_tree_nodes width d hv (.crossing hit) (by intro _ he; cases he)

/-- The literal actual comb station arrays form a genuine fresh-child rooted tree-growth order. -/
theorem treeEdges_growth (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (hv : 0 < d.1.length) :
    Graph.RootedTreeGrowth (treeRoot width d hv) (treeEdges width d hv) := by
  have hfeet := (spineStations_nodup width height hd hfit).map (stationNumber_injective width d)
  have hspine := of_nodup_path (spineLabels width d) hfeet (spineLabels_nonempty width d hv)
  change Graph.RootedTreeGrowth (treeRoot width d hv) (pathEdges (treeRoot width d hv) (spineLabels width d).tail) at hspine
  have hnodes : treeRoot width d hv :: (pathEdges (treeRoot width d hv) (spineLabels width d).tail).map Prod.fst =
      spineLabels width d := by
    rw [pathEdges_children]
    exact List.cons_head_tail (spineLabels_nonempty width d hv)
  apply hspine.attach_paths (toothBranches width d)
  · intro branch hb
    rw [hnodes]
    exact toothBranches_attached width d hb
  · exact toothBranches_nodup width height hd hfit
  · rw [hnodes]
    exact toothBranches_disjoint width d

end PushPuzzle.PushS.Comb
