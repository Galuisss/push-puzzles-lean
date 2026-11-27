/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.OctantSuccessor
public import PushS.CombStationDarts
import all PushS.CombGenus
import all PushS.CombSpineDarts
import all PushS.CombToothDarts

/-! The genuine foot rotations join the actual ordered spine and tooth walks. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

private theorem foot_octants (vertex : Fin d.1.length) (dart : Graph.Dart (augmentedGraph width hd))
    (hv : dart.vertex = stationNumber width d (.foot vertex)) : ∃ rank : Fin 8,
      (augmentedDrawing width height hd hfit hhead).direction dart = octantAngle rank.val ∧
        (rank.val = 6 ∨ (rank.val = 4 ∧ 0 < vertexRank width d vertex) ∨
          (rank.val = 0 ∧ vertexRank width d vertex + 1 < d.1.length)) := by
  rcases (dart_vertex_foot_iff width height hd hfit dart vertex).mp hv with rfl | ⟨hleft, rfl⟩ | ⟨hright, rfl⟩
  · exact ⟨6, toothFootDart_direction width height hd hfit hhead vertex, Or.inl rfl⟩
  · exact ⟨4, spineLeftDart_direction width height hd hfit hhead vertex hleft, Or.inr (Or.inl ⟨rfl, hleft⟩)⟩
  · exact ⟨0, spineRightDart_direction width height hd hfit hhead vertex hright, Or.inr (Or.inr ⟨rfl, hright⟩)⟩

private theorem rotate_foot (vertex : Fin d.1.length) (origin next : Graph.Dart (augmentedGraph width hd))
    (horigin : origin.vertex = stationNumber width d (.foot vertex)) (hnext : next.vertex = stationNumber width d (.foot vertex))
    (originRank nextRank : Fin 8) (hne : originRank ≠ nextRank)
    (horiginDir : (augmentedDrawing width height hd hfit hhead).direction origin = octantAngle originRank.val)
    (hnextDir : (augmentedDrawing width height hd hfit hhead).direction next = octantAngle nextRank.val)
    (hfirst : ∀ rank : Fin 8, (rank.val = 6 ∨ (rank.val = 4 ∧ 0 < vertexRank width d vertex) ∨
        (rank.val = 0 ∧ vertexRank width d vertex + 1 < d.1.length)) →
      rank = originRank ∨ (nextRank.val + 7 - originRank.val) % 8 ≤ (rank.val + 7 - originRank.val) % 8) :
    (augmentedRotation width height hd hfit hhead).rotate origin = next := by
  apply rotate_eq_of_octant_minimum (augmentedDrawing_realizes_rotation width height hd hfit hhead)
    origin next (hnext.trans horigin.symm) originRank nextRank hne horiginDir hnextDir
  intro dart hv
  obtain ⟨rank, hdir, hrank⟩ := foot_octants width height hd hfit hhead vertex dart (hv.trans horigin)
  exact ⟨rank, hdir, hfirst rank hrank⟩

/-- Every genuine predecessor spine end rotates into the actual upward tooth at that foot. -/
theorem augmentedRotation_spineLeft (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex) :
    (augmentedRotation width height hd hfit hhead).rotate (spineLeftDart width hd vertex hleft) = toothFootDart width hd vertex := by
  apply rotate_foot width height hd hfit hhead vertex _ _ (spineLeftDart_vertex width hd vertex hleft)
    (toothFootDart_vertex width hd vertex) 4 6 (by decide)
    (spineLeftDart_direction width height hd hfit hhead vertex hleft) (toothFootDart_direction width height hd hfit hhead vertex)
  intro rank hrank
  simp only [Fin.ext_iff]
  rcases hrank with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- A tooth with a next foot rotates into the actual successor spine end. -/
theorem augmentedRotation_toothFoot_right (vertex : Fin d.1.length) (hright : vertexRank width d vertex + 1 < d.1.length) :
    (augmentedRotation width height hd hfit hhead).rotate (toothFootDart width hd vertex) = spineRightDart width hd vertex hright := by
  apply rotate_foot width height hd hfit hhead vertex _ _ (toothFootDart_vertex width hd vertex)
    (spineRightDart_vertex width hd vertex hright) 6 0 (by decide)
    (toothFootDart_direction width height hd hfit hhead vertex) (spineRightDart_direction width height hd hfit hhead vertex hright)
  intro rank hrank
  simp only [Fin.ext_iff]
  rcases hrank with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The last tooth returns into the actual predecessor spine end. -/
theorem augmentedRotation_toothFoot_left (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex)
    (hright : ¬ vertexRank width d vertex + 1 < d.1.length) :
    (augmentedRotation width height hd hfit hhead).rotate (toothFootDart width hd vertex) = spineLeftDart width hd vertex hleft := by
  apply rotate_foot width height hd hfit hhead vertex _ _ (toothFootDart_vertex width hd vertex)
    (spineLeftDart_vertex width hd vertex hleft) 6 4 (by decide)
    (toothFootDart_direction width height hd hfit hhead vertex) (spineLeftDart_direction width height hd hfit hhead vertex hleft)
  intro rank hrank
  simp only [Fin.ext_iff]
  rcases hrank with h | ⟨h, _⟩ | ⟨h, hh⟩ <;> omega

/-- Returning along the spine continues to its actual predecessor when present. -/
theorem augmentedRotation_spineRight_left (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex)
    (hright : vertexRank width d vertex + 1 < d.1.length) :
    (augmentedRotation width height hd hfit hhead).rotate (spineRightDart width hd vertex hright) = spineLeftDart width hd vertex hleft := by
  apply rotate_foot width height hd hfit hhead vertex _ _ (spineRightDart_vertex width hd vertex hright)
    (spineLeftDart_vertex width hd vertex hleft) 0 4 (by decide)
    (spineRightDart_direction width height hd hfit hhead vertex hright) (spineLeftDart_direction width height hd hfit hhead vertex hleft)
  intro rank hrank
  simp only [Fin.ext_iff]
  rcases hrank with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The first returning spine end closes the contour through the first actual tooth. -/
theorem augmentedRotation_spineRight_first (vertex : Fin d.1.length) (hleft : ¬ 0 < vertexRank width d vertex)
    (hright : vertexRank width d vertex + 1 < d.1.length) :
    (augmentedRotation width height hd hfit hhead).rotate (spineRightDart width hd vertex hright) = toothFootDart width hd vertex := by
  apply rotate_foot width height hd hfit hhead vertex _ _ (spineRightDart_vertex width hd vertex hright)
    (toothFootDart_vertex width hd vertex) 0 6 (by decide)
    (spineRightDart_direction width height hd hfit hhead vertex hright) (toothFootDart_direction width height hd hfit hhead vertex)
  intro rank hrank
  simp only [Fin.ext_iff]
  rcases hrank with h | ⟨h, hh⟩ | ⟨h, _⟩ <;> omega

/-- A sole actual tooth foot closes directly onto itself. -/
theorem augmentedRotation_toothFoot_single (vertex : Fin d.1.length) (hleft : ¬ 0 < vertexRank width d vertex)
    (hright : ¬ vertexRank width d vertex + 1 < d.1.length) :
    (augmentedRotation width height hd hfit hhead).rotate (toothFootDart width hd vertex) = toothFootDart width hd vertex := by
  apply rotate_eq_self_of_vertex_unique
  intro dart hv
  rw [toothFootDart_vertex] at hv
  rcases (dart_vertex_foot_iff width height hd hfit dart vertex).mp hv with he | ⟨hl, _⟩ | ⟨hr, _⟩
  · exact he
  · exact False.elim (hleft hl)
  · exact False.elim (hright hr)

end Geometry
end PushPuzzle.PushS.Comb
