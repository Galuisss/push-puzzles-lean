/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusSeamAnchors

/-! Exact raw local wall stencils of the actual oriented physical annular pieces. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

private theorem short_reoriented_walls (k : ShortCorners.Kind) (a b : Bool) {W H : ℕ}
    (e : GridIsometry (ShortCorners.width k) (ShortCorners.height k) W H)
    (p : Cell (ShortCorners.width k) (ShortCorners.height k)) :
    e.cells p∈(GridIsometry.reorientInstance (ShortCorners.puzzle k a b) e).board.walls ↔
      p∈(ShortCorners.template k).walls := by
  change e.cells p∈(e.board ((ShortCorners.template k).board ((ShortCorners.template k).boxes b))).walls ↔ _
  exact e.mem_walls _ p

def lineRawIso (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    GridIsometry (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height
      (linePiece q i hi a b).width (linePiece q i hi a b).height :=
  ((lineOrientation (original q i).travel (fillerFlip q i)).axis
    (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
    (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height).geometry

theorem line_raw_walls (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool)
    (p : Cell (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height) :
    (lineRawIso q i hi a b).cells p∈(linePiece q i hi a b).board.walls ↔
      p∈(lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).board.walls :=
  (lineRawIso q i hi a b).mem_walls _ p

theorem corner_raw_walls (q : Key) (i : ℕ) (a b : Bool)
    (p : Cell (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))) :
    (cornerIso q i).geometry.cells p∈(cornerPiece q i a b).board.walls ↔
      p∈(ShortCorners.template (cornerKind q i)).walls := by
  exact short_reoriented_walls (cornerKind q i) a b (cornerIso q i).geometry p

end PushPuzzle.PushFS.Reduction.GateTileRouting
