/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombStationDarts
public import PushS.OctantSuccessor
import all PushS.CombGenus
import all PushS.CombDarts
import all PushS.CombSourceDarts
import all PushS.CombToothDarts

/-! The genuine geometric rotation follows the four literal contour sides at every actual crossing. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private def crossingRanks (left right : Fin 8) : Fin 4 → Fin 8 := ![2, left, 6, right]

private theorem crossingRanks_injective : ∀ left right : Fin 8,
    (left.val = 3 ∨ left.val = 4) → (right.val = 0 ∨ right.val = 7) →
      Function.Injective (crossingRanks left right) := by decide

private theorem crossingRanks_first : ∀ left right : Fin 8,
    (left.val = 3 ∨ left.val = 4) → (right.val = 0 ∨ right.val = 7) →
      ∀ origin other : Fin 4, other ≠ origin →
        ((crossingRanks left right (origin + 1)).val + 7 - (crossingRanks left right origin).val) % 8 ≤
          ((crossingRanks left right other).val + 7 - (crossingRanks left right origin).val) % 8 := by decide

private theorem rotate_crossing_catalog {G : Graph} {drawing : Graph.PolygonalDrawing G}
    {rotation : Graph.RotationSystem G} (hR : drawing.Realizes rotation) (catalog : Fin 4 → Graph.Dart G)
    (hsame : ∀ index, (catalog index).vertex = (catalog 0).vertex)
    (hcover : ∀ dart : Graph.Dart G, dart.vertex = (catalog 0).vertex → ∃ index, catalog index = dart)
    (left right : Fin 8) (hl : left.val = 3 ∨ left.val = 4) (hr : right.val = 0 ∨ right.val = 7)
    (hdir : ∀ index, drawing.direction (catalog index) = octantAngle (crossingRanks left right index).val)
    (origin : Fin 4) : rotation.rotate (catalog origin) = catalog (origin + 1) := by
  have hinj : Function.Injective catalog := by
    intro a b he
    apply crossingRanks_injective left right hl hr
    apply octantAngle_injective
    change octantAngle (crossingRanks left right a).val = octantAngle (crossingRanks left right b).val
    rw [← hdir a, ← hdir b, he]
  apply rotate_eq_of_octant_catalog hR catalog hinj origin (origin + 1) (by omega)
    (fun index => (hsame index).trans (hsame origin).symm)
    (fun dart hv => hcover dart (hv.trans (hsame origin))) (crossingRanks left right) hdir
  exact crossingRanks_first left right hl hr origin

/-- The actual four clockwise darts are down, original ascending source side, up and original returning source side. -/
@[expose] def crossingDartCycle (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) : Fin 4 → Graph.Dart (augmentedGraph width hd) :=
  ![toothCrossingDart width hd hit false, crossingDart width hd hit false,
    toothCrossingDart width hd hit true, crossingDart width hd hit true]

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The complete actual crossing fiber rotates through the literal compiler contour sides in clockwise order. -/
theorem augmentedRotation_crossing (hit : {c // c ∈ crossings width d}) (origin : Fin 4) :
    (augmentedRotation width height hd hfit hhead).rotate (crossingDartCycle width hd hit origin) =
      crossingDartCycle width hd hit (origin + 1) := by
  have hv (index : Fin 4) : (crossingDartCycle width hd hit index).vertex = stationNumber width d (.crossing hit) := by
    fin_cases index
    · exact toothCrossingDart_vertex width hd hit false
    · exact crossingDart_vertex width hd hit false
    · exact toothCrossingDart_vertex width hd hit true
    · exact crossingDart_vertex width hd hit true
  have hcover (dart : Graph.Dart (augmentedGraph width hd))
      (he : dart.vertex = (crossingDartCycle width hd hit 0).vertex) : ∃ index, crossingDartCycle width hd hit index = dart := by
    rw [hv] at he
    rcases (dart_vertex_crossing_iff width height hd hfit dart hit).mp he with h | h | h | h
    · exact ⟨1, h.symm⟩
    · exact ⟨3, h.symm⟩
    · exact ⟨0, h.symm⟩
    · exact ⟨2, h.symm⟩
  have hl := crossingDart_direction width height hd hfit hhead hit false
  have hr := crossingDart_direction width height hd hfit hhead hit true
  change _ = octantAngle 3 ∨ _ = octantAngle 4 at hl
  change _ = octantAngle 0 ∨ _ = octantAngle 7 at hr
  obtain ⟨left, hlrank, hleft⟩ : ∃ left : Fin 8, (left.val = 3 ∨ left.val = 4) ∧
      (augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit false) = octantAngle left.val := by
    rcases hl with hl | hl
    · exact ⟨3, Or.inl rfl, hl⟩
    · exact ⟨4, Or.inr rfl, hl⟩
  obtain ⟨right, hrrank, hright⟩ : ∃ right : Fin 8, (right.val = 0 ∨ right.val = 7) ∧
      (augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit true) = octantAngle right.val := by
    rcases hr with hr | hr
    · exact ⟨0, Or.inl rfl, hr⟩
    · exact ⟨7, Or.inr rfl, hr⟩
  apply rotate_crossing_catalog (augmentedDrawing_realizes_rotation width height hd hfit hhead)
    (crossingDartCycle width hd hit) (fun index => (hv index).trans (hv 0).symm) hcover left right hlrank hrrank _ origin
  intro index
  fin_cases index
  · exact toothCrossingDart_direction width height hd hfit hhead hit false
  · exact hleft
  · exact toothCrossingDart_direction width height hd hfit hhead hit true
  · exact hright

end Geometry
end PushPuzzle.PushS.Comb
