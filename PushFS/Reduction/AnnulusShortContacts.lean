/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusSeamAnchors
public import PushFS.Reduction.AnnulusShortWalls
public import PushFS.Reduction.AnnulusRawFrames

/-! Complete actual source/target ownership at every short-turn contact of the physical annular inventory. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem near_wall_contact (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (p : Cell (linePiece q i (by omega) a b).width (linePiece q i (by omega) a b).height)
    (c : Cell (cornerPiece q i a b).width (cornerPiece q i a b).height)
    (he : ((lineOffset q i).1+p.1.val,(lineOffset q i).2+p.2.val)=
      ((cornerOffset q i).1+c.1.val,(cornerOffset q i).2+c.2.val)) :
    p∈(linePiece q i (by omega) a b).board.walls ↔ c∈(cornerPiece q i a b).board.walls := by
  obtain ⟨p,rfl⟩ := (lineRawIso q i (by omega) a b).cells.surjective p
  obtain ⟨c,rfl⟩ := (cornerIso q i).geometry.cells.surjective c
  have hl := line_raw_walls q i (by omega) a b p
  have hc := corner_raw_walls q i a b c
  have hs := short_near_walls_placed (d := (original q i).travel) (e := (original q (i+1)).travel) (turn_perpendicular q i hi) (fillerFlip q i)
    (fillerSpan q i) (filler_shape q i (by omega)).2.1 a b (lineOffset q i).1 (lineOffset q i).2
    (cornerOffset q i).1 (cornerOffset q i).2 p c he
    ((line_far_anchor_coordinates q i (by omega) a b).trans (corner_near_anchor_coordinates q i hi).symm)
  exact hl.trans (hs.trans hc.symm)

theorem near_source_disjoint (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q i) (fillerSpan q i)) (k : Fin (ShortCorners.count (cornerKind q i))) :
    ((lineOffset q i).1+((lineSlotMatching q i (by omega) a b).source l).1.val,
      (lineOffset q i).2+((lineSlotMatching q i (by omega) a b).source l).2.val)≠
      ((cornerOffset q i).1+((cornerMatching q i a b).source k).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).source k).2.val) := by
  rw [line_source_coordinates q i (by omega) a b l,corner_source_coordinates q i a b k]
  have hb := line_source_bounds (fillerFlip q i) (fillerSpan q i) (filler_shape q i (by omega)).2.1 a b l
  exact short_near_disjoint (turn_perpendicular q i hi) (fillerFlip q i) a
    (fillerSpan q i) (filler_shape q i (by omega)).2.1 a b (lineOffset q i).1 (lineOffset q i).2
    (cornerOffset q i).1 (cornerOffset q i).2 _ hb.2.1 hb.2.2 k
    ((line_far_anchor_coordinates q i (by omega) a b).trans (corner_near_anchor_coordinates q i hi).symm)

theorem near_target_disjoint (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q i) (fillerSpan q i)) (k : Fin (ShortCorners.count (cornerKind q i))) :
    ((lineOffset q i).1+((lineSlotMatching q i (by omega) a b).target l).1.val,
      (lineOffset q i).2+((lineSlotMatching q i (by omega) a b).target l).2.val)≠
      ((cornerOffset q i).1+((cornerMatching q i a b).target k).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).target k).2.val) := by
  rw [line_target_coordinates q i (by omega) a b l,corner_target_coordinates q i a b k]
  have hb := line_target_bounds (fillerFlip q i) (fillerSpan q i) (filler_shape q i (by omega)).2.1 a b l
  exact short_near_disjoint (turn_perpendicular q i hi) (fillerFlip q i) b
    (fillerSpan q i) (filler_shape q i (by omega)).2.1 a b (lineOffset q i).1 (lineOffset q i).2
    (cornerOffset q i).1 (cornerOffset q i).2 _ hb.2.1 hb.2.2 k
    ((line_far_anchor_coordinates q i (by omega) a b).trans (corner_near_anchor_coordinates q i hi).symm)

theorem later_line_unflipped (q : Key) (i : ℕ) : fillerFlip q (i+1)=false := by
  simp [fillerFlip]

theorem far_wall_contact (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (p : Cell (linePiece q (i+1) hi a b).width (linePiece q (i+1) hi a b).height)
    (c : Cell (cornerPiece q i a b).width (cornerPiece q i a b).height)
    (he : ((lineOffset q (i+1)).1+p.1.val,(lineOffset q (i+1)).2+p.2.val)=
      ((cornerOffset q i).1+c.1.val,(cornerOffset q i).2+c.2.val)) :
    p∈(linePiece q (i+1) hi a b).board.walls ↔ c∈(cornerPiece q i a b).board.walls := by
  obtain ⟨p,rfl⟩ := (lineRawIso q (i+1) hi a b).cells.surjective p
  obtain ⟨c,rfl⟩ := (cornerIso q i).geometry.cells.surjective c
  have hl := line_raw_walls q (i+1) hi a b p
  have hc := corner_raw_walls q i a b c
  have hs := short_far_walls_placed (d := (original q i).travel) (e := (original q (i+1)).travel) (turn_perpendicular q i hi) (fillerFlip q (i+1)) (later_line_unflipped q i)
    (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1 a b (lineOffset q (i+1)).1 (lineOffset q (i+1)).2
    (cornerOffset q i).1 (cornerOffset q i).2 p c he
    ((line_near_anchor_coordinates q (i+1) hi a b).trans (corner_far_anchor_coordinates q i hi).symm)
  exact hl.trans (hs.trans hc.symm)

theorem far_source_disjoint (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q (i+1)) (fillerSpan q (i+1))) (k : Fin (ShortCorners.count (cornerKind q i))) :
    ((lineOffset q (i+1)).1+((lineSlotMatching q (i+1) hi a b).source l).1.val,
      (lineOffset q (i+1)).2+((lineSlotMatching q (i+1) hi a b).source l).2.val)≠
      ((cornerOffset q i).1+((cornerMatching q i a b).source k).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).source k).2.val) := by
  rw [line_source_coordinates q (i+1) hi a b l,corner_source_coordinates q i a b k]
  have hb := line_source_bounds (fillerFlip q (i+1)) (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1 a b l
  exact short_far_disjoint_general (turn_perpendicular q i hi) (fillerFlip q (i+1)) (later_line_unflipped q i) a
    (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1 a b (lineOffset q (i+1)).1 (lineOffset q (i+1)).2
    (cornerOffset q i).1 (cornerOffset q i).2 _ hb.1 hb.2.2 k
    ((line_near_anchor_coordinates q (i+1) hi a b).trans (corner_far_anchor_coordinates q i hi).symm)

theorem far_target_disjoint (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q (i+1)) (fillerSpan q (i+1))) (k : Fin (ShortCorners.count (cornerKind q i))) :
    ((lineOffset q (i+1)).1+((lineSlotMatching q (i+1) hi a b).target l).1.val,
      (lineOffset q (i+1)).2+((lineSlotMatching q (i+1) hi a b).target l).2.val)≠
      ((cornerOffset q i).1+((cornerMatching q i a b).target k).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).target k).2.val) := by
  rw [line_target_coordinates q (i+1) hi a b l,corner_target_coordinates q i a b k]
  have hb := line_target_bounds (fillerFlip q (i+1)) (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1 a b l
  exact short_far_disjoint_general (turn_perpendicular q i hi) (fillerFlip q (i+1)) (later_line_unflipped q i) b
    (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1 a b (lineOffset q (i+1)).1 (lineOffset q (i+1)).2
    (cornerOffset q i).1 (cornerOffset q i).2 _ hb.1 hb.2.2 k
    ((line_near_anchor_coordinates q (i+1) hi a b).trans (corner_far_anchor_coordinates q i hi).symm)

end PushPuzzle.PushFS.Reduction.GateTileRouting
