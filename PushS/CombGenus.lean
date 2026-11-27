/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombEmbedding
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse
import all PushS.CombEmbedding

/-! Numerical genus zero follows from the actual augmented source-comb polygonal embedding. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The genuine clockwise rotation read from the actual augmented source and comb-tree rays. -/
@[expose] noncomputable def augmentedRotation : Graph.RotationSystem (augmentedGraph width hd) :=
  (augmentedDrawing_isEmbedding width height hd hfit hhead).rotation

/-- The actual augmented drawing realizes its own literal clockwise geometric rotation. -/
theorem augmentedDrawing_realizes_rotation :
    (augmentedDrawing width height hd hfit hhead).Realizes (augmentedRotation width height hd hfit hhead) :=
  (augmentedDrawing_isEmbedding width height hd hfit hhead).realizes_rotation

/-- The actual source-comb rotation has numerical genus zero on every component. -/
theorem augmentedRotation_numericalGenusZero :
    (augmentedRotation width height hd hfit hhead).NumericalGenusZero :=
  (augmentedDrawing_isEmbedding width height hd hfit hhead).numericalGenusZero
    (augmented_incidence_declared width hd) (augmentedDrawing_realizes_rotation width height hd hfit hhead)

end Geometry
end PushPuzzle.PushS.Comb
