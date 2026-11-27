/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RotationTreeTour
import all PushS.RotationTreeTour

/-! A genuine standard contraction trace preserves the exact source-prefix cyclic word. -/

public section
namespace PushPuzzle.Graph

open Cslib.Complexity.Graph

open Cslib.Complexity

/-- The unchanged original edge index and Boolean end tag of an actual graph dart. -/
@[expose] def Dart.edgeCoordinates {G : Graph} (dart : Dart G) : ℕ × Bool := (dart.1.val, dart.2)

/-- Indexed edge/end coordinates retain each actual graph dart. -/
theorem Dart.edgeCoordinates_injective (G : Graph) : Function.Injective (Dart.edgeCoordinates (G := G)) := by
  intro a b he
  have hindex : a.1.val = b.1.val := congrArg (fun coordinate : ℕ × Bool => coordinate.1) he
  have hside : a.2 = b.2 := congrArg (fun coordinate : ℕ × Bool => coordinate.2) he
  exact Prod.ext (Fin.ext hindex) hside

namespace RotationSystem

open Cslib.Complexity.Graph.RotationSystem

/-- Every genuine trace removes a suffix of the actual listed edge occurrences. -/
theorem ContractionTrace.length_le {G H : Graph} {r : RotationSystem G} {s : RotationSystem H}
    (trace : ContractionTrace r s) : H.edges.length ≤ G.edges.length := by
  induction trace with
  | refl => exact le_rfl
  | cast h _ => cases h; exact le_rfl
  | contract => simp [contractLastEdgeGraph, lastEdgeGraph, relabel]
  | trans _ _ ihfirst ihsecond => exact ihsecond.trans ihfirst

/-- Delete precisely the selected last edge's two actual dart coordinates from a directed word. -/
@[expose] def contractedWord (G : Graph) (u v : ℕ) (word : List (Dart (lastEdgeGraph G u v))) :
    List (Dart (contractLastEdgeGraph G u v)) :=
  (((word.map ((contractLastEdgeDartEquiv G u v).trans
    (lastEdgeDartEquiv (contractLastEdgeGraph G u v) v v))).filterMap id).filterMap id)

private theorem filterMap_id_nodup {α : Type} {word : List (Option α)} (hn : word.Nodup) :
    (word.filterMap id).Nodup := List.Nodup.filterMap
  (fun _ _ _ ha hb => (Option.mem_def.mp ha).trans (Option.mem_def.mp hb).symm) hn

/-- Deleting the actual selected tree darts retains every remaining original occurrence once. -/
theorem contractedWord_nodup (G : Graph) (u v : ℕ) (word : List (Dart (lastEdgeGraph G u v))) (hn : word.Nodup) :
    (contractedWord G u v word).Nodup :=
  filterMap_id_nodup (filterMap_id_nodup (hn.map (by exact Equiv.injective _)))

/-- The complete actual word retains exactly its unchanged original edge/end coordinates below the removed edge. -/
theorem contractedWord_coordinates (G : Graph) (u v : ℕ) (word : List (Dart (lastEdgeGraph G u v))) :
    (contractedWord G u v word).map Dart.edgeCoordinates =
      (word.map Dart.edgeCoordinates).filter (fun coordinate => decide (coordinate.1 < G.edges.length)) := by
  induction word with
  | nil => rfl
  | cons dart word ih =>
    by_cases hbase : dart.1.val < G.edges.length
    · simpa [contractedWord, Equiv.trans_apply, contraction_coordinates_apply, hbase, Dart.edgeCoordinates] using
        congrArg (Dart.edgeCoordinates (⟨dart.1.val, by simpa only [contractLastEdgeGraph, relabel, List.length_map] using hbase⟩, dart.2) :: ·) ih
    · cases hside : dart.2 <;>
        simpa [contractedWord, Equiv.trans_apply, contraction_coordinates_apply, hbase, hside, Dart.edgeCoordinates] using ih

private theorem coordinates_filter_bound (G : Graph) (word : List (Dart G)) :
    (word.map Dart.edgeCoordinates).filter (fun coordinate => decide (coordinate.1 < G.edges.length)) =
      word.map Dart.edgeCoordinates := by
  apply List.filter_eq_self.mpr
  intro coordinate hc
  obtain ⟨dart, _, rfl⟩ := List.mem_map.mp hc
  exact decide_eq_true dart.1.isLt

private theorem filter_smaller (word : List (ℕ × Bool)) (middle final : ℕ) (h : final ≤ middle) :
    (word.filter (fun coordinate => decide (coordinate.1 < middle))).filter (fun coordinate => decide (coordinate.1 < final)) =
      word.filter (fun coordinate => decide (coordinate.1 < final)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro coordinate _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A genuine complete trace preserves the exact remaining source-prefix word in original edge/end coordinates. -/
theorem ContractionTrace.preserves_word {G H : Graph} {r : RotationSystem G} {s : RotationSystem H}
    (trace : ContractionTrace r s) (firstTree : ℕ) (hcut : firstTree ≤ H.edges.length)
    (word : List (Dart G)) (hn : word.Nodup) (htour : (PushPuzzle.Graph.RotationSystem.treeTour r) firstTree = word.formPerm) :
    ∃ retained : List (Dart H), retained.Nodup ∧ (PushPuzzle.Graph.RotationSystem.treeTour s) firstTree = retained.formPerm ∧
      retained.map Dart.edgeCoordinates =
        (word.map Dart.edgeCoordinates).filter (fun coordinate => decide (coordinate.1 < H.edges.length)) := by
  induction trace generalizing firstTree with
  | refl r => exact ⟨word, hn, htour, (coordinates_filter_bound _ word).symm⟩
  | cast h r => cases h; exact ⟨word, hn, htour, (coordinates_filter_bound _ word).symm⟩
  | @contract G u v r huv =>
    have hbase : firstTree ≤ G.edges.length := by simpa only [contractLastEdgeGraph, relabel, List.length_map] using hcut
    refine ⟨contractedWord G u v word, contractedWord_nodup G u v word hn,
      treeTour_contract_word r huv firstTree hbase word hn htour, ?_⟩
    simpa only [contractLastEdgeGraph, relabel, List.length_map] using contractedWord_coordinates G u v word
  | trans first second ihfirst ihsecond =>
    obtain ⟨middle, hmiddle, hmidTour, hmidWord⟩ := ihfirst firstTree (hcut.trans second.length_le) word hn htour
    obtain ⟨retained, hretained, hretTour, hretWord⟩ := ihsecond firstTree hcut middle hmiddle hmidTour
    refine ⟨retained, hretained, hretTour, ?_⟩
    rw [hretWord, hmidWord, filter_smaller _ _ _ second.length_le]

end RotationSystem
end PushPuzzle.Graph
