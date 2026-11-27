/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RootedTreeContraction
public import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
public import PushS.PermutationWordDeletion

/-! The actual tree-boundary successor turns around a vertex after reversing auxiliary tree darts. -/

public section
namespace PushPuzzle.Graph

open Cslib.Complexity.Graph

open Cslib.Complexity

namespace Dart

open Cslib.Complexity.Graph.Dart

open Cslib.Complexity.Graph.Dart

/-- Reverse exactly the auxiliary edge suffix, retaining every original source-fragment dart. -/
@[expose] def suffixReversal (G : Graph) (firstTree : ℕ) : Equiv.Perm (Dart G) where
  toFun dart := if dart.1.val < firstTree then dart else dart.reverse
  invFun dart := if dart.1.val < firstTree then dart else dart.reverse
  left_inv dart := by
    rcases dart with ⟨edge, side⟩
    by_cases h : edge.val < firstTree <;> simp only [h, ite_true, ite_false, reverse]
    simp
  right_inv dart := by
    rcases dart with ⟨edge, side⟩
    by_cases h : edge.val < firstTree <;> simp only [h, ite_true, ite_false, reverse]
    simp

/-- The retained original source prefix is pointwise fixed. -/
theorem suffixReversal_source (G : Graph) (firstTree : ℕ) (dart : Dart G) (h : dart.1.val < firstTree) :
    suffixReversal G firstTree dart = dart := by simp [suffixReversal, h]

/-- An auxiliary tree dart is sent to its genuine opposite end. -/
theorem suffixReversal_tree (G : Graph) (firstTree : ℕ) (dart : Dart G) (h : firstTree ≤ dart.1.val) :
    suffixReversal G firstTree dart = dart.reverse := by simp [suffixReversal, Nat.not_lt.mpr h]

/-- Once the exact source prefix is reached there are no auxiliary reversals left. -/
theorem suffixReversal_all_source (G : Graph) (firstTree : ℕ) (h : G.edges.length ≤ firstTree) :
    suffixReversal G firstTree = 1 := by
  apply Equiv.ext
  intro dart
  exact suffixReversal_source G firstTree dart (dart.1.isLt.trans_le h)

end Dart

namespace RotationSystem

open Cslib.Complexity.Graph.RotationSystem

private theorem contraction_coordinates_apply (G : Graph) (u v : ℕ) (dart : Dart (lastEdgeGraph G u v)) :
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v) ((contractLastEdgeDartEquiv G u v) dart) =
      if h : dart.1.val < G.edges.length then
        some (some (⟨dart.1.val, by simpa only [contractLastEdgeGraph, relabel, List.length_map] using h⟩, dart.2))
      else if dart.2 then none else some none := by
  rcases dart with ⟨⟨i, hi⟩, side⟩
  change ((contractLastEdgeDartEquiv G u v).trans (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)) (⟨i, hi⟩, side) = _
  rw [contractLastEdge_coordinates]
  change (Dart.relabelEquiv G (Function.update id u v)).optionCongr.optionCongr
    (if h : i < G.edges.length then some (some (⟨i, h⟩, side)) else if side then none else some none) = _
  split_ifs <;> rfl

private theorem suffixReversal_coordinates (G : Graph) (u v firstTree : ℕ) (hcut : firstTree ≤ G.edges.length) :
    (((contractLastEdgeDartEquiv G u v).trans (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).permCongr
      (Dart.suffixReversal (lastEdgeGraph G u v) firstTree)) =
      (Dart.suffixReversal (contractLastEdgeGraph G u v) firstTree).optionCongr.optionCongr *
        Equiv.swap (some none) none := by
  let coordinates := (contractLastEdgeDartEquiv G u v).trans (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  apply Equiv.ext
  intro point
  obtain ⟨dart, rfl⟩ := coordinates.surjective point
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases dart with ⟨⟨index, hi⟩, side⟩
  by_cases hbase : index < G.edges.length
  · by_cases hsource : index < firstTree <;>
      simp [Dart.suffixReversal, hsource, coordinates, contraction_coordinates_apply, hbase, Dart.reverse,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  · have hsource : ¬index < firstTree := by omega
    cases side <;> simp [Dart.suffixReversal, hsource, coordinates, contraction_coordinates_apply, hbase, Dart.reverse,
      Equiv.Perm.mul_apply]

/-- The literal comb-tree boundary walk on original indexed source and auxiliary darts. -/
@[expose] def treeTour {G : Graph} (r : RotationSystem G) (firstTree : ℕ) : Equiv.Perm (Dart G) :=
  r.rotate * Dart.suffixReversal G firstTree

/-- On a completely contracted graph the actual tree-boundary successor is the retained rotation. -/
theorem treeTour_all_source {G : Graph} (r : RotationSystem G) (firstTree : ℕ) (h : G.edges.length ≤ firstTree) :
    (PushPuzzle.Graph.RotationSystem.treeTour r) firstTree = r.rotate := by
  rw [treeTour, Dart.suffixReversal_all_source G firstTree h, mul_one]

/-- Actual nonloop tree contraction deletes precisely the two removed points from the same tree-boundary tour. -/
theorem treeTour_contractLastEdge {G : Graph} {u v : ℕ} (r : RotationSystem (lastEdgeGraph G u v))
    (huv : u ≠ v) (firstTree : ℕ) (hcut : firstTree ≤ G.edges.length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (r.contractLastEdge huv)) firstTree = Equiv.removeNone (Equiv.removeNone
      (((contractLastEdgeDartEquiv G u v).trans (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)).permCongr
        ((PushPuzzle.Graph.RotationSystem.treeTour r) firstTree))) := by
  let coordinates := (contractLastEdgeDartEquiv G u v).trans (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v)
  let remaining := Dart.suffixReversal (contractLastEdgeGraph G u v) firstTree
  let removed : Equiv.Perm (Option (Option (Dart (contractLastEdgeGraph G u v)))) := Equiv.swap (some none) none
  have htrue : coordinates (lastEdgeDart G u v true) = none := contractLastEdge_coordinates_last G u v true
  have hfalse : coordinates (lastEdgeDart G u v false) = some none := contractLastEdge_coordinates_last G u v false
  have hswap : coordinates.permCongr (Equiv.swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)) = removed := by
    have h := Equiv.symm_trans_swap_trans (lastEdgeDart G u v true) (lastEdgeDart G u v false) coordinates
    change coordinates.permCongr (Equiv.swap _ _) = _ at h
    rw [htrue, hfalse] at h
    exact h.trans (Equiv.swap_comm _ _)
  have hcomm : remaining.optionCongr.optionCongr * removed = removed * remaining.optionCongr.optionCongr := by
    rw [Equiv.mul_swap_eq_swap_mul]
    rfl
  have hcoordinates : coordinates.permCongr ((PushPuzzle.Graph.RotationSystem.treeTour r) firstTree) =
      coordinates.permCongr (r.rotate * Equiv.swap (lastEdgeDart G u v true) (lastEdgeDart G u v false)) *
        remaining.optionCongr.optionCongr := by
    rw [treeTour, Equiv.permCongr_mul, Equiv.permCongr_mul, hswap]
    rw [show coordinates.permCongr (Dart.suffixReversal (lastEdgeGraph G u v) firstTree) =
      remaining.optionCongr.optionCongr * removed from suffixReversal_coordinates G u v firstTree hcut]
    rw [hcomm, mul_assoc]
  rw [treeTour, rotate_contractLastEdge]
  change _ = Equiv.removeNone (Equiv.removeNone (coordinates.permCongr ((PushPuzzle.Graph.RotationSystem.treeTour r) firstTree)))
  rw [hcoordinates, Equiv.Perm.CycleSurgery.removeNone_mul_optionCongr, Equiv.Perm.CycleSurgery.removeNone_mul_optionCongr]

/-- Standard tree contraction retains exactly the original directed word with the selected tree ends deleted. -/
theorem treeTour_contract_word {G : Graph} {u v : ℕ} (r : RotationSystem (lastEdgeGraph G u v))
    (huv : u ≠ v) (firstTree : ℕ) (hcut : firstTree ≤ G.edges.length)
    (word : List (Dart (lastEdgeGraph G u v))) (hn : word.Nodup) (htour : (PushPuzzle.Graph.RotationSystem.treeTour r) firstTree = word.formPerm) :
    (PushPuzzle.Graph.RotationSystem.treeTour (r.contractLastEdge huv)) firstTree =
      (((word.map ((contractLastEdgeDartEquiv G u v).trans
        (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v))).filterMap id).filterMap id).formPerm := by
  rw [treeTour_contractLastEdge r huv firstTree hcut, htour, ← PushPuzzle.List.formPerm_map_equiv,
    PushPuzzle.List.removeNone_twice_formPerm _ (hn.map (by exact Equiv.injective _))]

end RotationSystem
end PushPuzzle.Graph
