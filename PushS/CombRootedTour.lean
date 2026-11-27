/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTourWord
import all PushS.CombRootedOrientation

/-! The explicit original tree-end flip transports the actual complete comb tour without changing any source end. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem suffixReversal_permCongr {G H : Graph} (equiv : Graph.Dart G ≃ Graph.Dart H)
    (hindex : ∀ dart, (equiv dart).1.val = dart.1.val)
    (hreverse : ∀ dart, equiv dart.reverse = (equiv dart).reverse) (cutoff : ℕ) :
    equiv.permCongr (Graph.Dart.suffixReversal G cutoff) = Graph.Dart.suffixReversal H cutoff := by
  apply Equiv.ext
  intro point
  obtain ⟨dart, rfl⟩ := equiv.surjective point
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  by_cases h : dart.1.val < cutoff
  · rw [Graph.Dart.suffixReversal_source G cutoff dart h,
      Graph.Dart.suffixReversal_source H cutoff (equiv dart) (by rw [hindex]; exact h)]
  · rw [Graph.Dart.suffixReversal_tree G cutoff dart (by omega),
      Graph.Dart.suffixReversal_tree H cutoff (equiv dart) (by rw [hindex]; omega)]
    exact hreverse dart

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The actual original tree-end equivalence conjugates the same genuine complete tree tours. -/
theorem rootedRotation_treeTour_congr :
    (rootedDartEquiv width hd).permCongr ((PushPuzzle.Graph.RotationSystem.treeTour (rootedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length) =
      (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length := by
  rw [Graph.RotationSystem.treeTour, Equiv.permCongr_mul]
  rw [suffixReversal_permCongr (rootedDartEquiv width hd) (fun _ => rfl) (rootedDartEquiv_reverse width hd)]
  change (rootedDartEquiv width hd).permCongr
      ((rootedDartEquiv width hd).symm.permCongr (augmentedRotation width height hd hfit hhead).rotate) * _ = _
  rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]
  rfl

/-- Mapping the exact actual augmented contour through the original tree-end flip gives the same rooted tour word. -/
theorem rootedRotation_treeTour_word (word : List (Graph.Dart (augmentedGraph width hd)))
    (hword : (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length = word.formPerm) :
    (PushPuzzle.Graph.RotationSystem.treeTour (rootedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length =
      (word.map (rootedDartEquiv width hd).symm).formPerm := by
  rw [PushPuzzle.List.formPerm_map_equiv]
  apply (rootedDartEquiv width hd).permCongr.injective
  rw [rootedRotation_treeTour_congr, hword]
  rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]

end Geometry
end PushPuzzle.PushS.Comb
