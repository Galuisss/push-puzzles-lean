/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Orthogonal
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Identity
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Finite

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Geometric

/-! Complete layer and word paths for the internal strip compiler. -/

public section
namespace PushPuzzle.NCL
open Cslib.Complexity Cslib.Complexity.NCL Diagram

/-- The complete edge paths of one word layer draw its exact diagram graph. -/
@[expose] noncomputable def Slice.OrthogonalDrawing.geometric {sl : Slice}
    {source target : List Color}
    (L : sl.OrthogonalDrawing source target) :
    GridDrawing.DiagramDrawing Prim.interp L.diagram := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hp, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  exact GridDrawing.Pad.drawing left as bs right v hp layout

/-- Replace the layered construction by full finite paths for all its diagram edges. -/
@[expose] noncomputable def Word.OrthogonalDrawing.geometric {w : Word} {a b : List Color} :
    (D : w.OrthogonalDrawing a b) → GridDrawing.DiagramDrawing Prim.interp D.diagram
  | .nil a => GridDrawing.identity Prim.interp a
  | .cons layer rest => GridDrawing.comp (Slice.OrthogonalDrawing.geometric layer) (geometric rest)

namespace GridDrawing
open Cslib.Complexity.NCL.GridDrawing Cslib.Complexity.NCL.GridRouting
variable {V E : Type*}
/-- Closing an empty-boundary drawing retains every point of each complete path in its trace.
-/
theorem Open.close_path_mem {G : ConstraintGraph V E} {top bottom : Fin 0 → E}
    (P : Open G top bottom) (e : E) (p : Point) (hp : (P.close.path e).Contains p) :
    P.trace e p := by
  classical
  exact (P.path e).choose_spec p ((Path.contains_cast_iff _ _ _ _).mp hp)

variable {V' E' : Type*} {G : ConstraintGraph V E} {G' : ConstraintGraph V' E'}
/-- Renaming a complete graph drawing retains exactly the same complete path points. -/
theorem Closed.reindex_path_contains_iff (P : Closed G) (σ : V' ≃ V) (τ : E' ≃ E)
    (hports : ∀ v e d, HasPort G' v e d ↔ HasPort G (σ v) (τ e) d)
    (e : E') (p : Point) :
    ((P.reindex σ τ hports).path e).Contains p ↔ (P.path (τ e)).Contains p := by
  classical
  exact Path.contains_cast_iff _ _ _ _

end GridDrawing
end PushPuzzle.NCL
